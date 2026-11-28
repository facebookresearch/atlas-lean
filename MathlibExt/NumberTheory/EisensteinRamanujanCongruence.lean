/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Instances.Rat
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import MathlibExt.NumberTheory.GeneralizedTau
import MathlibExt.NumberTheory.ModularForms.QParamProduct

/-!
# Lu's Eisenstein congruences

For even weights $k \ge 12$ with $k \ne 14$, the coefficients of $G_k$ are congruent to those
of a linear combination of $\Delta^i E_{k-12i}$, with multipliers determined by the coefficients
of $q, \dots, q^m$, where $m$ is the dimension of the space of cusp forms. The modulus is the
largest divisor of the absolute numerator of the constant term of $G_k$ coprime to the corresponding
numerators at weights $k-12i$ for $1 \le i \le \lfloor k/12 \rfloor$ (using $1$ at weights $0$
and $2$).

In the six weights with a one-dimensional cusp space, the coefficients of the Eisenstein
series are congruent to those of the discriminant times a normalized Eisenstein series.
In the six weights with a two-dimensional cusp space, they are congruent to those of the
discriminant times a normalized Eisenstein series plus an explicit multiple of the squared
discriminant times another normalized Eisenstein series.
In the six weights with a three-dimensional cusp space, the analogous congruence uses three
powers of the discriminant and coefficients found by successive elimination.

## References

* Qing Lu, *Explicit Congruences for Modular Forms of Higher Weights*, Journal of Integer
  Sequences 29 (2026), Article 26.5.1, pp. 1–12, Theorem 1 and Corollaries 3, 5, 6 and 7.
* B. Datskovsky and P. Guerzhoy, *On Ramanujan congruences for modular forms of integral and
  half-integral weights*, Proceedings of the American Mathematical Society 124 (1996),
  pp. 2283–2291, proof of Theorem 1 (the integral form subtracted from the Eisenstein series).
* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer-Verlag, 2005, Section 3.5 (level-one dimension formula).
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

private lemma coeff_two_mul_powerSeries {R : Type*} [CommRing R] (A B : R⟦X⟧) :
    coeff 2 (A * B) = coeff 0 A * coeff 2 B + coeff 1 A * coeff 1 B + coeff 2 A * coeff 0 B := by
  have h : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by decide
  rw [coeff_mul, h]
  simp [add_assoc]

/-- Every natural power of Euler's pentagonal series has constant coefficient $1$. -/
public lemma constantCoeff_pentagonalSeries_pow (R : Type*) [CommRing R] (m : ℕ) :
    constantCoeff (pentagonalSeries R ^ m) = 1 := by
  rw [map_pow, ← coeff_zero_eq_constantCoeff_apply,
    show (0 : ℕ) = pentagonal 0 by norm_num [pentagonal_def], coeff_pentagonalSeries_pentagonal]
  simp

/-- The coefficient of $q$ in the $m$-th power of Euler's pentagonal series is $-m$. -/
public lemma coeff_one_pentagonalSeries_pow (R : Type*) [CommRing R] (m : ℕ) :
    coeff 1 (pentagonalSeries R ^ m) = -(m : R) := by
  have h : coeff 1 (pentagonalSeries R) = -1 := by
    rw [show (1 : ℕ) = pentagonal 1 by norm_num [pentagonal_def],
      coeff_pentagonalSeries_pentagonal, Int.negOnePow_one]
    simp
  have h₀ : constantCoeff (pentagonalSeries R) = 1 := by
    simpa only [pow_one] using constantCoeff_pentagonalSeries_pow R 1
  rw [coeff_one_pow, h, h₀]
  simp

/-- The coefficient of $q^2$ in the $m$-th power of Euler's pentagonal series is
$\binom{m}{2}-m$, with the subtraction taken in the coefficient ring. -/
public lemma coeff_two_pentagonalSeries_pow (R : Type*) [CommRing R] (m : ℕ) :
    coeff 2 (pentagonalSeries R ^ m) = (m.choose 2 : R) - (m : R) := by
  have h₀ : coeff 0 (pentagonalSeries R) = 1 := by
    simpa only [pow_one, ← coeff_zero_eq_constantCoeff_apply] using
      constantCoeff_pentagonalSeries_pow R 1
  have h₁ : coeff 1 (pentagonalSeries R) = -1 := by
    simpa only [pow_one, Nat.cast_one] using coeff_one_pentagonalSeries_pow R 1
  have h₂ : coeff 2 (pentagonalSeries R) = -1 := by
    rw [show (2 : ℕ) = pentagonal (-1) by norm_num [pentagonal_def],
      coeff_pentagonalSeries_pentagonal, Int.negOnePow_neg, Int.negOnePow_one]
    simp
  induction m with
  | zero => simp [coeff_one]
  | succ m ih =>
    rw [pow_succ, coeff_two_mul_powerSeries, h₀, h₁, h₂, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_pentagonalSeries_pow, coeff_one_pentagonalSeries_pow, ih]
    simp only [Nat.choose_succ_succ' m 1, Nat.choose_one_right, Nat.cast_add, Nat.cast_succ]
    ring

namespace eisenstein_congr_delta_mul_eisenstein_dim_one

open UpperHalfPlane EisensteinSeries ModularForm
open scoped MatrixGroups

noncomputable section

private abbrev qParam (z : ℍ) := Function.Periodic.qParam 1 (z : ℂ)

private def deltaZ : ℤ⟦X⟧ := X * pentagonalSeries ℤ ^ 24

private lemma map_deltaZ (R : Type*) [CommRing R] :
    deltaZ.map (Int.castRingHom R) = X * pentagonalSeries R ^ 24 := by
  have he : (pentagonalSeries ℤ).map (Int.castRingHom R) = pentagonalSeries R := by
    ext n
    by_cases hn : n ∈ Set.range pentagonal
    · obtain ⟨m, rfl⟩ := hn
      simp [-Int.coe_negOnePow]
    · simp [coeff_pentagonalSeries_eq_zero _ hn]
  simp [deltaZ, he]

private lemma deltaZ_rat :
    deltaZ.map (Int.castRingHom ℚ) = X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24 := by
  rw [map_deltaZ, (WithPiTopology.hasProd_one_sub_X_pow ℚ).pow 24 |>.tprod_eq]

private lemma qExpansion_discriminant :
    qExpansion 1 discriminant = deltaZ.map (Int.castRingHom ℂ) := by
  rw [map_deltaZ]
  have he (a : ℕ) (z : ℍ) : HasSum
      (fun n => coeff n (pentagonalSeries ℂ ^ a) * qParam z ^ n)
      (eulerFunction (qParam z) ^ a) := by
    induction a generalizing z with
    | zero =>
      simpa +contextual [coeff_one] using (hasSum_ite_eq (0 : ℕ) (1 : ℂ))
    | succ a ih =>
      simp only [pow_succ]
      exact ModularCurve.hasSum_qParam_mul 1 one_pos _ _ _ _ ih
        (fun τ => hasSum_eulerFunction_pentagonalSeries (Function.Periodic.norm_qParam_lt_one
          one_pos τ.im_pos)) z
  have hx (z : ℍ) : HasSum (fun n => coeff n (X : ℂ⟦X⟧) * qParam z ^ n) (qParam z) := by
    simpa +contextual [coeff_X] using (hasSum_ite_eq (1 : ℕ) (qParam z))
  ext n
  rw [← CuspForm.coe_discriminant]
  refine (ModularFormClass.qExpansion_coeff_unique (f := CuspForm.discriminant)
    (c := fun i => coeff i (X * pentagonalSeries ℂ ^ 24))
    one_pos one_mem_strictPeriods_SL (fun z => ?_) n).symm
  have hq := Function.Periodic.norm_qParam_lt_one (h := 1) one_pos z.im_pos
  change HasSum _ (discriminant z)
  rw [discriminant_eq_q_prod, ((hasProd_eulerFunction hq).pow 24).tprod_eq]
  simpa only [smul_eq_mul] using ModularCurve.hasSum_qParam_mul 1 one_pos _ _ _ _ hx (he 24) z

private def sigma (w n : ℕ) : ℚ :=
  if w = 0 then (if n = 0 then 1 else 0)
  else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)

private lemma bernoulli_ne_zero {k : ℕ} (hk : 3 ≤ k) (he : Even k) : bernoulli k ≠ 0 := by
  obtain ⟨j, rfl⟩ := he
  rw [← two_mul]
  intro h
  have hd := Bernoulli.dvd_den_bernoulli (p := 2) (by omega : 0 < j)
    (by simp : 2 - 1 ∣ 2 * j)
  simp [h] at hd

private lemma sigma_zero_ne {k : ℕ} (hk : 3 ≤ k) (he : Even k) : sigma k 0 ≠ 0 := by
  simp [sigma, show k ≠ 0 by omega, bernoulli_ne_zero hk he]

private lemma coeff_eisenstein {k : ℕ} (hk : 3 ≤ k) (he : Even k) (n : ℕ) :
    coeff n (qExpansion 1 (E hk)) = ((sigma k n / sigma k 0 : ℚ) : ℂ) := by
  rw [E_qExpansion_coeff hk he]
  have h0 := sigma_zero_ne hk he
  by_cases hn : n = 0
  · simp [hn, h0]
  · simp [sigma, show k ≠ 0 by omega, hn, div_eq_mul_inv, mul_comm, mul_left_comm]

-- For these weights the reciprocal of the constant term is an integer.
private lemma small_multiplier {w : ℕ} (hw : w ∈ ({4, 6, 8, 10, 14} : Finset ℕ)) :
    ∃ a : ℤ, sigma w 0 * a = 1 := by
  fin_cases hw
  · exact ⟨240, by decide +kernel⟩
  · exact ⟨-504, by decide +kernel⟩
  · exact ⟨480, by decide +kernel⟩
  · exact ⟨-264, by decide +kernel⟩
  · exact ⟨-24, by decide +kernel⟩

private lemma integral_eisenstein {w : ℕ} (hw : w ∈ ({0, 4, 6, 8, 10, 14} : Finset ℕ)) :
    ∃ (F : ModularForm 𝒮ℒ w) (Z : ℤ⟦X⟧), coeff 0 Z = 1 ∧
      qExpansion 1 F = Z.map (Int.castRingHom ℂ) ∧
      ∀ n, sigma w n = sigma w 0 * coeff n Z := by
  rcases Finset.mem_insert.mp hw with rfl | hw
  · refine ⟨(1 : ModularForm 𝒮ℒ 0), 1, by simp, ?_, ?_⟩
    · simpa using (ModularForm.qExpansion_one (Γ := 𝒮ℒ) (h := 1))
    · intro n
      simp [sigma, coeff_one]
  obtain ⟨a, ha⟩ := small_multiplier hw
  have h3 : 3 ≤ w := by fin_cases hw <;> decide
  have he : Even w := by fin_cases hw <;> decide
  let Z : ℤ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 1
    else a * (ArithmeticFunction.sigma (w - 1) n : ℤ)
  have hZ (n : ℕ) : sigma w n = sigma w 0 * coeff n Z := by
    by_cases hn : n = 0
    · simp [Z, hn]
    · simp only [Z, coeff_mk, ite_eq_right hn, Int.cast_mul, Int.cast_natCast,
        ← mul_assoc, ha, one_mul]
      simp [sigma, hn, show w ≠ 0 by omega]
  refine ⟨E h3, Z, by simp [Z], ?_, hZ⟩
  ext n
  rw [coeff_eisenstein h3 he, hZ n, mul_div_cancel_left₀ _ (sigma_zero_ne h3 he)]
  simp

private lemma coprime_den {c : ℚ} {N : ℕ} (hd : N ∣ c.num.natAbs) (z : ℤ) :
    (c * z / N).den.Coprime N := by
  by_cases hN : N = 0
  · simp [hN]
  obtain ⟨a, ha⟩ := Int.natCast_dvd.mpr hd
  have heq : c * z / N = Rat.divInt (a * z) c.den := by
    rw [Rat.divInt_eq_div]
    conv_lhs => rw [← c.num_div_den, ha]
    push_cast
    field_simp
  rw [heq]
  apply Nat.Coprime.of_dvd_left (Int.natCast_dvd.mp (Rat.den_dvd _ _))
  exact c.reduced.symm.of_dvd_right hd

-- Subtract the integral form E₄³ F with the same constant term as Eₖ.
-- Division by Δ identifies the difference with a multiple of F.
private lemma compare_forms {k w : ℕ} (hkw : k = 12 + w) (he : Even k)
    (hr : Module.rank ℂ (ModularForm 𝒮ℒ (w : ℤ)) = 1)
    (F : ModularForm 𝒮ℒ w) (Z : ℤ⟦X⟧) (hZ : coeff 0 Z = 1)
    (hF : qExpansion 1 F = Z.map (Int.castRingHom ℂ)) (n : ℕ) :
    ∃ z : ℤ, sigma k n - coeff n (deltaZ * Z) = sigma k 0 * z := by
  have h3 : 3 ≤ k := by omega
  obtain ⟨F₄, Z₄, hZ₄, hF₄, -⟩ := integral_eisenstein (w := 4) (by decide)
  let H : ModularForm 𝒮ℒ k := ModularForm.mcast (by exact_mod_cast (show 3 * 4 + w = k by omega))
    ((F₄.pow 3).mul F)
  let L := Z₄ ^ 3 * Z
  let D := deltaZ * Z
  have hH : qExpansion 1 H = L.map (Int.castRingHom ℂ) := by
    simp only [H, ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos
      one_mem_strictPeriods_SL, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      hF₄, hF, L, map_mul, map_pow]
  have hL : coeff 0 L = 1 := by
    simp_all only [L, coeff_zero_eq_constantCoeff, map_mul, map_pow, one_pow, one_mul]
  let U := E h3 - H
  have hU : qExpansion 1 U = qExpansion 1 (E h3) - L.map (Int.castRingHom ℂ) :=
    (ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL (E h3) H).trans (by rw [hH])
  have hc : coeff 0 (qExpansion 1 U) = 0 := by
    rw [hU, map_sub, E_qExpansion_coeff_zero h3 he, coeff_map, hL, map_one, sub_self]
  have hwt : (w : ℤ) = (k : ℤ) - 12 := by omega
  have hF0 : F ≠ 0 := by
    intro h
    have hh := congrArg (coeff 0) hF
    simp [h, coeff_map, hZ, qExpansion_zero] at hh
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_ne_zero' F hF0).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp hr)
    ((CuspForm.discriminantEquiv (U.toCuspForm hc)).mcast hwt.symm)
  have hquot := congrArg (fun f : ModularForm 𝒮ℒ w => qExpansion 1 f) ha
  change qExpansion 1 (a • ⇑F) = qExpansion 1 ⇑(CuspForm.discriminantEquiv _) at hquot
  rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, hF] at hquot
  have heq := qExpansion_eq_qExpansion_discriminant_mul U hc
  rw [hU, qExpansion_discriminant, ← hquot, mul_smul_comm, ← map_mul] at heq
  have hcoeff (i : ℕ) :
      ((sigma k i / sigma k 0 : ℚ) : ℂ) - coeff i L = a * coeff i D := by
    simpa only [map_sub, coeff_eisenstein h3 he, coeff_map, Int.coe_castRingHom,
      coeff_smul, smul_eq_mul, D] using congrArg (coeff i) heq
  have hD : coeff 1 D = 1 := by
    change coeff (0 + 1) ((X * pentagonalSeries ℤ ^ 24) * Z) = 1
    rw [mul_assoc, coeff_succ_X_mul, coeff_zero_eq_constantCoeff, map_mul, map_pow,
      constantCoeff_pentagonalSeries_int]
    simpa [coeff_zero_eq_constantCoeff] using hZ
  have ha' := hcoeff 1
  rw [hD, Int.cast_one, mul_one, show sigma k 1 = 1 by simp [sigma, show k ≠ 0 by omega]] at ha'
  have hn := hcoeff n
  rw [← ha'] at hn
  have hrat : sigma k n / sigma k 0 - coeff n L =
      (1 / sigma k 0 - coeff 1 L) * coeff n D := by exact_mod_cast hn
  refine ⟨coeff n L - coeff 1 L * coeff n D, ?_⟩
  push_cast
  field_simp [sigma_zero_ne h3 he] at hrat
  linear_combination hrat

private lemma coefficient_congruence (k : ℕ) (hk : k ∈ ({12, 16, 18, 20, 22, 26} : Finset ℕ))
    (N : ℕ) (hd : N ∣ (sigma k 0).num.natAbs) (n : ℕ) :
    ((sigma k n - coeff n (deltaZ.map (Int.castRingHom ℚ) * PowerSeries.mk (sigma (k - 12))) /
      sigma (k - 12) 0) / N).den.Coprime N := by
  let w := k - 12
  have hw : w ∈ ({0, 4, 6, 8, 10, 14} : Finset ℕ) := by fin_cases hk <;> decide
  have hkw : k = 12 + w := by fin_cases hk <;> decide
  have he : Even k := by fin_cases hk <;> decide
  have hew : Even w := by fin_cases hk <;> decide
  have hr : Module.rank ℂ (ModularForm 𝒮ℒ (w : ℤ)) = 1 := by
    rw [dimension_level_one w hew]
    fin_cases hk <;> norm_num [w, Nat.ModEq]
  obtain ⟨F, Z, hZ, hF, hσ⟩ := integral_eisenstein hw
  have hc : sigma w 0 ≠ 0 := by
    rcases Finset.mem_insert.mp hw with h | h
    · simp [h, sigma]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      exact sigma_zero_ne (by omega) hew
  have hm : PowerSeries.mk (sigma w) = sigma w 0 • Z.map (Int.castRingHom ℚ) := by
    ext i
    simpa [coeff_smul, coeff_map] using hσ i
  obtain ⟨z, hz⟩ := compare_forms hkw he hr F Z hZ hF n
  change ((_ - coeff n (_ * PowerSeries.mk (sigma w)) / sigma w 0) / N).den.Coprime N
  rw [hm, mul_smul_comm, ← map_mul, coeff_smul, smul_eq_mul, mul_div_cancel_left₀ _ hc,
    coeff_map]
  exact hz ▸ coprime_den hd z

-- Remove the coefficient of degree j using a series with leading term q^j.
private def cancelCoeff (j : ℕ) (B : ℚ⟦X⟧) : ℚ⟦X⟧ →ₗ[ℚ] ℚ⟦X⟧ where
  toFun A := A - coeff j A • B
  map_add' A A' := by
    simp only [map_add, add_smul]
    abel
  map_smul' a A := by
    simp only [RingHom.id_apply, coeff_smul, smul_sub, smul_smul, smul_eq_mul]

private lemma coeff_cancelCoeff (j n : ℕ) (B A : ℚ⟦X⟧) :
    coeff n (cancelCoeff j B A) = coeff n A - coeff j A * coeff n B := by
  change coeff n (A - coeff j A • B) = _
  rw [map_sub, coeff_smul, smul_eq_mul]

private abbrev deltaRat : ℚ⟦X⟧ := deltaZ.map (Int.castRingHom ℚ)

private abbrev deltaUnit : ℚ⟦X⟧ := pentagonalSeries ℚ ^ 24

private lemma deltaRat_eq_X_mul : deltaRat = X * deltaUnit := map_deltaZ ℚ

private def eisensteinRat (w : ℕ) : ℚ⟦X⟧ := (sigma w 0)⁻¹ • PowerSeries.mk (sigma w)

private lemma coeff_eisensteinRat (w n : ℕ) :
    coeff n (eisensteinRat w) = sigma w n / sigma w 0 := by
  simp [eisensteinRat, smul_eq_mul, div_eq_mul_inv, mul_comm]

private lemma sigma_prime {w p : ℕ} (hw : w ≠ 0) (hp : p.Prime) :
    sigma w p = 1 + (p : ℚ) ^ (w - 1) := by
  rw [sigma, ite_eq_right hw, ite_eq_right hp.ne_zero, ArithmeticFunction.sigma_apply, hp.divisors]
  simp [Ne.symm hp.ne_one]

private lemma sigma_one {w : ℕ} (hw : w ≠ 0) : sigma w 1 = 1 := by
  simp [sigma, hw]

private def basisRat (k i : ℕ) : ℚ⟦X⟧ := deltaRat ^ i * eisensteinRat (k - 12 * i)

private lemma coeff_basisRat (k i n : ℕ) :
    coeff n (basisRat k i) = if i ≤ n then
      coeff (n - i) (deltaUnit ^ i * eisensteinRat (k - 12 * i)) else 0 := by
  rw [basisRat, deltaRat_eq_X_mul, mul_pow, mul_assoc, coeff_X_pow_mul']

private lemma coeff_basisRat_le (k i n : ℕ) (hn : n ≤ i)
    (hc : sigma (k - 12 * i) 0 ≠ 0) : coeff n (basisRat k i) = if n = i then 1 else 0 := by
  rcases hn.eq_or_lt with rfl | hn
  · rw [coeff_basisRat, ite_eq_left le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply,
      map_mul, map_pow, constantCoeff_pentagonalSeries_pow,
      ← coeff_zero_eq_constantCoeff_apply (eisensteinRat _), coeff_eisensteinRat, div_self hc]
    simp
  · simp [coeff_basisRat, hn.ne, not_le.mpr hn]

private lemma basisRat_first_coeffs {k : ℕ} (hk : 36 ≤ k)
    (hs₁ : sigma (k - 12) 0 ≠ 0) (hs₂ : sigma (k - 24) 0 ≠ 0) :
    coeff 2 (basisRat k 1) = 1 / sigma (k - 12) 0 - 24 ∧
    coeff 3 (basisRat k 1) = 252 + (2 ^ (k - 13) - 23) / sigma (k - 12) 0 ∧
    coeff 3 (basisRat k 2) = 1 / sigma (k - 24) 0 - 48 := by
  have h₁ : coeff 1 deltaUnit = -24 := coeff_one_pentagonalSeries_pow ℚ 24
  have h₂ : coeff 2 deltaUnit = 252 := by
    rw [coeff_two_pentagonalSeries_pow, show (24 : ℕ).choose 2 = 276 by decide]
    norm_num
  have hw₁ : k - 12 ≠ 0 := by omega
  have hw₂ : k - 24 ≠ 0 := by omega
  have hE₁ : coeff 0 (eisensteinRat (k - 12)) = 1 := by simp [coeff_eisensteinRat, hs₁]
  have hE₂ : coeff 0 (eisensteinRat (k - 24)) = 1 := by simp [coeff_eisensteinRat, hs₂]
  have hD₂ : coeff 1 (deltaUnit ^ 2) = -48 := by
    change coeff 1 ((pentagonalSeries ℚ ^ 24) ^ 2) = -48
    rw [← pow_mul, coeff_one_pentagonalSeries_pow]
    norm_num
  have hD₀ : constantCoeff (deltaUnit ^ 2) = 1 := by
    change constantCoeff ((pentagonalSeries ℚ ^ 24) ^ 2) = 1
    rw [← pow_mul, constantCoeff_pentagonalSeries_pow]
  constructor
  · norm_num [coeff_basisRat, coeff_one_mul, h₁, hE₁, constantCoeff_pentagonalSeries_pow,
      ← coeff_zero_eq_constantCoeff_apply (eisensteinRat (k - 12)),
      coeff_eisensteinRat, sigma_one hw₁]
    ring
  constructor
  · norm_num [coeff_basisRat, coeff_two_mul_powerSeries, h₁, h₂, hE₁,
      coeff_zero_eq_constantCoeff_apply deltaUnit, constantCoeff_pentagonalSeries_pow,
      coeff_eisensteinRat, sigma_one hw₁, sigma_prime hw₁ Nat.prime_two,
      show k - 12 - 1 = k - 13 by omega]
    ring
  · norm_num [coeff_basisRat, coeff_one_mul, hD₂, hD₀, ← coeff_zero_eq_constantCoeff_apply
      (eisensteinRat (k - 24)), hE₂, coeff_eisensteinRat, sigma_one hw₂]
    ring

private abbrev ratToComplex : ℚ →+* ℂ := Rat.castHom ℂ

private lemma map_rat_smul (a : ℚ) (A : ℚ⟦X⟧) :
    (a • A).map ratToComplex = (a : ℂ) • A.map ratToComplex := by
  ext n
  simp [smul_eq_mul]

private lemma map_int_rat_complex (Z : ℤ⟦X⟧) :
    (Z.map (Int.castRingHom ℚ)).map ratToComplex = Z.map (Int.castRingHom ℂ) := by
  ext n
  simp

-- Use Δ-division to successively lower the order bound and weight. At the terminal weight the
-- constant coefficient is injective, since the normalized form spans a one-dimensional space.
private lemma qExpansion_eq_zero_of_order {w : ℤ} (H : ModularForm 𝒮ℒ w)
    (hH : coeff 0 (qExpansion 1 H) = 1) (hr : Module.rank ℂ (ModularForm 𝒮ℒ w) = 1)
    (d : ℕ) (F : ModularForm 𝒮ℒ (w + 12 * (d : ℤ)))
    (h : (d : ℕ∞) < (qExpansion 1 F).order) : qExpansion 1 F = 0 := by
  induction d with
  | zero =>
    have h₀ := PowerSeries.coeff_of_lt_order 0 ((Nat.cast_nonneg (0 : ℕ)).trans_lt h)
    let F₀ := F.mcast (by simp : w + 12 * ((0 : ℕ) : ℤ) = w)
    have hH₀ : H ≠ 0 := by
      intro hh
      simp [hh, qExpansion_zero] at hH
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_ne_zero' H hH₀).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp hr) F₀
    have hq : qExpansion 1 F = a • qExpansion 1 H := by
      have hq₀ := congrArg (fun f : ModularForm 𝒮ℒ w => qExpansion 1 f) ha.symm
      change qExpansion 1 F = qExpansion 1 (a • ⇑H) at hq₀
      exact hq₀.trans (ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL a H)
    rw [hq, coeff_smul, hH, smul_eq_mul, mul_one] at h₀
    rw [hq, h₀, zero_smul]
  | succ d ih =>
    have h₀ := PowerSeries.coeff_of_lt_order 0 ((Nat.cast_nonneg (d + 1)).trans_lt h)
    let Q := (CuspForm.discriminantEquiv (F.toCuspForm h₀)).mcast
      (by push_cast; ring : w + 12 * ((d + 1 : ℕ) : ℤ) - 12 = w + 12 * (d : ℤ))
    have hq : qExpansion 1 F = qExpansion 1 discriminant * qExpansion 1 Q := by
      simpa only [Q, ModularForm.qExpansion_mcast] using
        qExpansion_eq_qExpansion_discriminant_mul F h₀
    have hsucc : (↑(d + 1) : ℕ∞) < (qExpansion 1 Q).order + 1 := by
      rw [hq, PowerSeries.order_mul, discriminant_qExpansion_order] at h
      simpa only [add_comm (1 : ℕ∞)] using h
    have ht : (d : ℕ∞) < (qExpansion 1 Q).order := by
      rw [Nat.cast_add, Nat.cast_one] at hsucc
      exact (ENat.add_lt_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp hsucc
    rw [hq, ih Q ht, mul_zero]

-- Keep the comparison on rational power series; these witnesses supply the modularity needed
-- for the order argument without requiring any descent of complex scalars.
private def IsRatExpansion (k : ℕ) (A : ℚ⟦X⟧) : Prop :=
  ∃ F : ModularForm 𝒮ℒ k, qExpansion 1 F = A.map ratToComplex

private lemma IsRatExpansion.sub_smul {k : ℕ} {A B : ℚ⟦X⟧}
    (hA : IsRatExpansion k A) (hB : IsRatExpansion k B) (a : ℚ) :
    IsRatExpansion k (A - a • B) := by
  obtain ⟨F, hF⟩ := hA
  obtain ⟨G, hG⟩ := hB
  refine ⟨F - (a : ℂ) • G, ?_⟩
  change qExpansion 1 (⇑F - ⇑((a : ℂ) • G)) = _
  rw [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL F ((a : ℂ) • G), hF]
  change A.map ratToComplex - qExpansion 1 ((a : ℂ) • ⇑G) = _
  rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (a : ℂ) G,
    hG, map_sub, map_rat_smul]

private lemma IsRatExpansion.cancel {k j : ℕ} {A B : ℚ⟦X⟧}
    (hA : IsRatExpansion k A) (hB : IsRatExpansion k B) :
    IsRatExpansion k (cancelCoeff j B A) := hA.sub_smul hB (coeff j A)

private lemma qExpansion_eisensteinRat {w : ℕ} (hw : 3 ≤ w) (he : Even w) :
    qExpansion 1 (E hw) = (eisensteinRat w).map ratToComplex := by
  ext n
  rw [coeff_eisenstein hw he, coeff_map, coeff_eisensteinRat]
  rfl

private lemma isRatExpansion_sigma {k : ℕ} (hk : 3 ≤ k) (he : Even k) :
    IsRatExpansion k (PowerSeries.mk (sigma k)) := by
  let c := sigma k 0
  have h : c • eisensteinRat k = PowerSeries.mk (sigma k) := by
    rw [eisensteinRat, smul_smul, mul_inv_cancel₀ (sigma_zero_ne hk he), one_smul]
  refine ⟨(c : ℂ) • E hk, ?_⟩
  change qExpansion 1 ((c : ℂ) • ⇑(E hk)) = _
  rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    qExpansion_eisensteinRat hk he, ← map_rat_smul, h]

private lemma isRatExpansion_basis (k i : ℕ) (h : 12 * i ≤ k)
    (F : ModularForm 𝒮ℒ ((k - 12 * i : ℕ) : ℤ))
    (hF : qExpansion 1 F = (eisensteinRat (k - 12 * i)).map ratToComplex) :
    IsRatExpansion k (basisRat k i) := by
  refine ⟨ModularForm.mcast (by rw [Nat.cast_sub h, Nat.cast_mul]; norm_num; ring)
    (((CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow i).mul F), ?_⟩
  simp only [ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos
    one_mem_strictPeriods_SL, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    hF, basisRat, map_mul, map_pow, map_int_rat_complex]
  change (qExpansion 1 discriminant) ^ i * _ = _
  rw [qExpansion_discriminant]

-- The rationals that are integral at every prime dividing N.
private def coprimeDenRing (N : ℕ) : Subring ℚ where
  carrier := {a | a.den.Coprime N}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' ha hb := (ha.mul_left hb).of_dvd_left (Rat.add_den_dvd _ _)
  neg_mem' := by simp
  mul_mem' ha hb := (ha.mul_left hb).of_dvd_left (Rat.mul_den_dvd _ _)

private lemma coeff_mul_mem_coprimeDenRing {N : ℕ} {A B : ℚ⟦X⟧}
    (hA : ∀ n, coeff n A ∈ coprimeDenRing N) (hB : ∀ n, coeff n B ∈ coprimeDenRing N)
    (n : ℕ) : coeff n (A * B) ∈ coprimeDenRing N := by
  rw [coeff_mul]
  exact (coprimeDenRing N).sum_mem fun p _ => (coprimeDenRing N).mul_mem (hA p.1) (hB p.2)

private lemma coeff_pow_mem_coprimeDenRing {N : ℕ} {A : ℚ⟦X⟧}
    (hA : ∀ n, coeff n A ∈ coprimeDenRing N) (i n : ℕ) :
    coeff n (A ^ i) ∈ coprimeDenRing N := by
  induction i generalizing n with
  | zero =>
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ i ih =>
    rw [pow_succ]
    exact coeff_mul_mem_coprimeDenRing ih hA n

private lemma coeff_map_int_mem_coprimeDenRing (N : ℕ) (Z : ℤ⟦X⟧) (n : ℕ) :
    coeff n (Z.map (Int.castRingHom ℚ)) ∈ coprimeDenRing N := by
  simp [coprimeDenRing]

private lemma coeff_cancelCoeff_mem_coprimeDenRing {N : ℕ} {A B : ℚ⟦X⟧}
    (hA : ∀ n, coeff n A ∈ coprimeDenRing N) (hB : ∀ n, coeff n B ∈ coprimeDenRing N)
    (j n : ℕ) : coeff n (cancelCoeff j B A) ∈ coprimeDenRing N := by
  rw [coeff_cancelCoeff]
  exact (coprimeDenRing N).sub_mem (hA n) ((coprimeDenRing N).mul_mem (hA j) (hB n))

private lemma coeff_basisRat_mem_coprimeDenRing {N k i : ℕ}
    (hc : sigma (k - 12 * i) 0 ≠ 0) (hd : (sigma (k - 12 * i) 0).num.natAbs.Coprime N)
    (n : ℕ) : coeff n (basisRat k i) ∈ coprimeDenRing N := by
  apply coeff_mul_mem_coprimeDenRing
  · exact coeff_pow_mem_coprimeDenRing (coeff_map_int_mem_coprimeDenRing N deltaZ) i
  intro m
  by_cases hm : m = 0
  · subst m
    rw [coeff_eisensteinRat, div_self hc]
    exact (coprimeDenRing N).one_mem
  rw [coeff_eisensteinRat, div_eq_mul_inv]
  apply (coprimeDenRing N).mul_mem
  · by_cases hw : k - 12 * i = 0 <;> simp [sigma, hm, hw, coprimeDenRing]
  · change ((sigma (k - 12 * i) 0)⁻¹).den.Coprime N
    rwa [Rat.den_inv_of_ne_zero hc]

private def cancelThree (k : ℕ) : ℚ⟦X⟧ →ₗ[ℚ] ℚ⟦X⟧ :=
  (cancelCoeff 3 (basisRat k 3)).comp ((cancelCoeff 2 (basisRat k 2)).comp
    (cancelCoeff 1 (basisRat k 1)))

private lemma coeff_cancelThree_sigma {k : ℕ} (hk : 36 ≤ k)
    (hs₁ : sigma (k - 12) 0 ≠ 0) (hs₂ : sigma (k - 24) 0 ≠ 0)
    (n : ℕ) :
    let γ₂ : ℚ := 2 ^ (k - 1) + 25 - 1 / sigma (k - 12) 0
    let γ₃ : ℚ := 3 ^ (k - 1) + 2 ^ (k - 1) * 48 + 949 -
      (2 ^ (k - 13) + 25) / sigma (k - 12) 0 - (2 ^ (k - 1) + 25) / sigma (k - 24) 0 +
      1 / (sigma (k - 12) 0 * sigma (k - 24) 0)
    coeff n (cancelThree k (PowerSeries.mk (sigma k))) =
      sigma k n - (coeff n (basisRat k 1) + γ₂ * coeff n (basisRat k 2) +
        γ₃ * coeff n (basisRat k 3)) := by
  dsimp only
  obtain ⟨hb₁₂, hb₁₃, hb₂₃⟩ := basisRat_first_coeffs hk hs₁ hs₂
  have hk₀ : k ≠ 0 := by omega
  simp only [cancelThree, LinearMap.comp_apply, coeff_cancelCoeff, coeff_mk, hb₁₂, hb₁₃, hb₂₃,
    sigma_one hk₀, sigma_prime hk₀ Nat.prime_two, sigma_prime hk₀ Nat.prime_three, one_mul]
  field_simp [hs₁, hs₂]
  ring

set_option maxHeartbeats 800000 in
-- The six weight cases and the comparison of the three modular q-expansions need extra reduction.
private lemma coefficient_congruence_three (k : ℕ)
    (hk : k ∈ ({36, 40, 42, 44, 46, 50} : Finset ℕ)) (N : ℕ)
    (hd : N ∣ (sigma k 0).num.natAbs)
    (hcop : ∀ i, 1 ≤ i → i ≤ 3 → (sigma (k - 12 * i) 0).num.natAbs.Coprime N) (n : ℕ) :
    (coeff n (cancelThree k (PowerSeries.mk (sigma k))) / N).den.Coprime N := by
  let w := k - 36
  have hw : w ∈ ({0, 4, 6, 8, 10, 14} : Finset ℕ) := by fin_cases hk <;> decide
  have hk₃₆ : 36 ≤ k := by fin_cases hk <;> decide
  have he : Even k := by fin_cases hk <;> decide
  have he₁ : Even (k - 12) := by fin_cases hk <;> decide
  have he₂ : Even (k - 24) := by fin_cases hk <;> decide
  have hew : Even w := by fin_cases hk <;> decide
  have hs (i : ℕ) (hi₁ : 1 ≤ i) (hi₃ : i ≤ 3) : sigma (k - 12 * i) 0 ≠ 0 := by
    have hwt : k - 12 * i = 0 ∨ (3 ≤ k - 12 * i ∧ Even (k - 12 * i)) := by
      interval_cases i <;> fin_cases hk <;> decide
    rcases hwt with h | ⟨h, hev⟩
    · simp [h, sigma]
    · exact sigma_zero_ne h hev
  have hr : Module.rank ℂ (ModularForm 𝒮ℒ (w : ℤ)) = 1 := by
    rw [dimension_level_one w hew]
    fin_cases hk <;> norm_num [w, Nat.ModEq]
  obtain ⟨H, Z, hZ, hH, hσ⟩ := integral_eisenstein hw
  have hH₀ : coeff 0 (qExpansion 1 H) = 1 := by simp [hH, hZ]
  have hE₃ : qExpansion 1 H = (eisensteinRat w).map ratToComplex := by
    have hs₃ : sigma w 0 ≠ 0 := hs 3 (by decide) (by decide)
    ext j
    rw [hH, coeff_map, coeff_map, coeff_eisensteinRat, hσ j,
      mul_div_cancel_left₀ _ hs₃]
    simp
  obtain ⟨F₄, Z₄, hZ₄, hF₄, -⟩ := integral_eisenstein (w := 4) (by decide)
  let L := (Z₄ ^ 9 * Z).map (Int.castRingHom ℚ)
  have hL : IsRatExpansion k L := by
    refine ⟨ModularForm.mcast (by dsimp [w]; omega) ((F₄.pow 9).mul H), ?_⟩
    simp only [ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos
      one_mem_strictPeriods_SL, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      hF₄, hH, L, map_int_rat_complex, map_mul, map_pow]
  have hL₀ : coeff 0 L = 1 := by
    change coeff 0 ((Z₄ ^ 9 * Z).map (Int.castRingHom ℚ)) = 1
    rw [coeff_map, coeff_zero_eq_constantCoeff_apply, map_mul, map_pow,
      ← coeff_zero_eq_constantCoeff_apply Z, ← coeff_zero_eq_constantCoeff_apply Z₄, hZ, hZ₄]
    simp
  have hB₁ : IsRatExpansion k (basisRat k 1) :=
    isRatExpansion_basis k 1 (by omega) (E (by omega)) (qExpansion_eisensteinRat (by omega) he₁)
  have hB₂ : IsRatExpansion k (basisRat k 2) :=
    isRatExpansion_basis k 2 (by omega) (E (by omega)) (qExpansion_eisensteinRat (by omega) he₂)
  have hB₃ : IsRatExpansion k (basisRat k 3) := isRatExpansion_basis k 3 (by omega) H hE₃
  let G := PowerSeries.mk (sigma k)
  let A := G - sigma k 0 • L
  have hA : IsRatExpansion k A := (isRatExpansion_sigma (by omega) he).sub_smul hL _
  have hA₀ : coeff 0 A = 0 := by
    change coeff 0 (G - sigma k 0 • L) = 0
    rw [map_sub, coeff_smul, smul_eq_mul, hL₀, mul_one]
    simp [G]
  have htri (i j : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 3) (hji : j ≤ i) :
      coeff j (basisRat k i) = if j = i then 1 else 0 :=
    coeff_basisRat_le k i j hji (hs i hi hi')
  have hvanish (j : ℕ) (hj : j < 4) : coeff j (cancelThree k A) = 0 := by
    interval_cases j <;> simp [cancelThree, coeff_cancelCoeff, hA₀, htri]
  obtain ⟨F, hF⟩ : IsRatExpansion k (cancelThree k A) :=
    ((hA.cancel (j := 1) hB₁).cancel (j := 2) hB₂).cancel (j := 3) hB₃
  have hwt : (k : ℤ) = (w : ℤ) + 12 * ((3 : ℕ) : ℤ) := by dsimp [w]; omega
  let F' := F.mcast hwt
  have hF' : qExpansion 1 F' = (cancelThree k A).map ratToComplex := by
    simpa only [F', ModularForm.qExpansion_mcast] using hF
  have hOrder : (3 : ℕ∞) < (qExpansion 1 F').order := by
    apply lt_of_lt_of_le (show (3 : ℕ∞) < (4 : ℕ∞) by decide)
    apply PowerSeries.nat_le_order
    intro j hj
    simp only [hF', coeff_map, hvanish j hj, map_zero]
  have hZero : cancelThree k A = 0 := by
    apply (PowerSeries.map_eq_zero _ ratToComplex).mp
    exact hF'.symm.trans (qExpansion_eq_zero_of_order H hH₀ hr 3 F' hOrder)
  have hEq : cancelThree k G = sigma k 0 • cancelThree k L := by
    apply sub_eq_zero.mp
    simpa only [A, map_sub, LinearMap.map_smul] using hZero
  have hLmem := coeff_map_int_mem_coprimeDenRing N (Z₄ ^ 9 * Z)
  have hBmem (i : ℕ) (hi₁ : 1 ≤ i) (hi₃ : i ≤ 3) (j : ℕ) :
      coeff j (basisRat k i) ∈ coprimeDenRing N :=
    coeff_basisRat_mem_coprimeDenRing (hs i hi₁ hi₃) (hcop i hi₁ hi₃) j
  have hT : coeff n (cancelThree k L) ∈ coprimeDenRing N :=
    coeff_cancelCoeff_mem_coprimeDenRing
      (coeff_cancelCoeff_mem_coprimeDenRing
        (coeff_cancelCoeff_mem_coprimeDenRing hLmem (hBmem 1 (by decide) (by decide)) 1)
        (hBmem 2 (by decide) (by decide)) 2) (hBmem 3 (by decide) (by decide)) 3 n
  have hcN : sigma k 0 / N ∈ coprimeDenRing N := by
    change (sigma k 0 / N).den.Coprime N
    simpa using coprime_den hd 1
  change coeff n (cancelThree k G) / N ∈ coprimeDenRing N
  rw [hEq, coeff_smul, smul_eq_mul, mul_comm, mul_div_assoc]
  exact (coprimeDenRing N).mul_mem hT hcN

private lemma deltaZ_sq_mul (Z : ℤ⟦X⟧) :
    deltaZ ^ 2 * Z = X * (X * (pentagonalSeries ℤ ^ 48 * Z)) := by
  change (X * pentagonalSeries ℤ ^ 24) ^ 2 * Z = _
  ring

private lemma cusp_quotient {K W : ℕ} (G : ModularForm 𝒮ℒ K)
    (hc : coeff 0 (qExpansion 1 G) = 0) (hKW : (W : ℤ) = K - 12)
    (hr : Module.rank ℂ (ModularForm 𝒮ℒ (W : ℤ)) = 1)
    (F : ModularForm 𝒮ℒ W) (Z : ℤ⟦X⟧)
    (hF : qExpansion 1 F = Z.map (Int.castRingHom ℂ)) (hF0 : F ≠ 0) :
    ∃ c : ℂ, qExpansion 1 G = c • (deltaZ * Z).map (Int.castRingHom ℂ) := by
  obtain ⟨c, ha⟩ := (finrank_eq_one_iff_of_ne_zero' F hF0).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp hr)
    ((CuspForm.discriminantEquiv (G.toCuspForm hc)).mcast hKW.symm)
  have hquot := congrArg (fun f : ModularForm 𝒮ℒ W => qExpansion 1 f) ha
  change qExpansion 1 (c • ⇑F) = qExpansion 1 ⇑(CuspForm.discriminantEquiv _) at hquot
  rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, hF] at hquot
  have heq := qExpansion_eq_qExpansion_discriminant_mul G hc
  rw [qExpansion_discriminant, ← hquot, mul_smul_comm, ← map_mul] at heq
  exact ⟨c, heq⟩

private lemma eisenstein_sub_integral {w₁ w₂ : ℕ} (hw : w₁ = 12 + w₂)
    (h3 : 3 ≤ w₁) (he : Even w₁)
    (hr : Module.rank ℂ (ModularForm 𝒮ℒ (w₂ : ℤ)) = 1)
    (F₂ : ModularForm 𝒮ℒ w₂) (Z₂ : ℤ⟦X⟧) (hZ₂ : coeff 0 Z₂ = 1)
    (hF₂ : qExpansion 1 F₂ = Z₂.map (Int.castRingHom ℂ))
    (A : ModularForm 𝒮ℒ w₁) (L_A : ℤ⟦X⟧) (hA0 : coeff 0 L_A = 1)
    (hA : qExpansion 1 A = L_A.map (Int.castRingHom ℂ)) :
    ∃ v : ℚ, v = 1 / sigma w₁ 0 - coeff 1 L_A ∧
      ∀ n, sigma w₁ n / sigma w₁ 0 =
        coeff n L_A + v * coeff n (deltaZ * Z₂) := by
  have hwt : (w₂ : ℤ) = w₁ - 12 := by omega
  have hF0 : F₂ ≠ 0 := by
    intro h
    have hh := congrArg (coeff 0) hF₂
    simp [h, coeff_map, hZ₂, qExpansion_zero] at hh
  let G := E h3 - A
  have hG : qExpansion 1 G = qExpansion 1 (E h3) - L_A.map (Int.castRingHom ℂ) :=
    (ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL (E h3) A).trans (by rw [hA])
  have hc : coeff 0 (qExpansion 1 G) = 0 := by
    rw [hG, map_sub, E_qExpansion_coeff_zero h3 he, coeff_map, hA0, map_one, sub_self]
  obtain ⟨vc, hvc⟩ := cusp_quotient G hc hwt hr F₂ Z₂ hF₂ hF0
  have hcoeff (n : ℕ) :
      ((sigma w₁ n / sigma w₁ 0 : ℚ) : ℂ) - coeff n L_A =
        vc * coeff n (deltaZ * Z₂) := by
    simpa only [hG, map_sub, coeff_eisenstein h3 he, coeff_map, Int.coe_castRingHom,
      coeff_smul, smul_eq_mul] using congrArg (coeff n) hvc
  have hD1 : coeff 1 (deltaZ * Z₂) = 1 := by
    change coeff (0 + 1) ((X * pentagonalSeries ℤ ^ 24) * Z₂) = 1
    rw [mul_assoc, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, map_mul, map_pow,
      constantCoeff_pentagonalSeries_int]
    simpa [coeff_zero_eq_constantCoeff_apply] using hZ₂
  have hs1 : sigma w₁ 1 = 1 := sigma_one (by omega : w₁ ≠ 0)
  have hvc1 := hcoeff 1
  rw [hD1, Int.cast_one, mul_one, hs1] at hvc1
  refine ⟨1 / sigma w₁ 0 - coeff 1 L_A, rfl, fun n => ?_⟩
  have hn := hcoeff n
  have hvc_eq : vc = ((1 / sigma w₁ 0 - coeff 1 L_A : ℚ) : ℂ) := by
    exact_mod_cast hvc1.symm
  rw [hvc_eq] at hn
  have hQ : sigma w₁ n / sigma w₁ 0 - coeff n L_A =
      (1 / sigma w₁ 0 - coeff 1 L_A) * coeff n (deltaZ * Z₂) := by
    exact_mod_cast hn
  linear_combination hQ

private lemma eisenstein_two_step {k w₁ w₂ : ℕ} (hkw : k = 12 + w₁) (hw : w₁ = 12 + w₂)
    (h3 : 3 ≤ k) (he : Even k)
    (hr : Module.rank ℂ (ModularForm 𝒮ℒ (w₂ : ℤ)) = 1)
    (F₂ : ModularForm 𝒮ℒ w₂) (Z₂ : ℤ⟦X⟧) (hZ₂ : coeff 0 Z₂ = 1)
    (hF₂ : qExpansion 1 F₂ = Z₂.map (Int.castRingHom ℂ))
    (A : ModularForm 𝒮ℒ w₁) (L_A : ℤ⟦X⟧) (hA0 : coeff 0 L_A = 1)
    (hA : qExpansion 1 A = L_A.map (Int.castRingHom ℂ))
    (H : ModularForm 𝒮ℒ k) (L : ℤ⟦X⟧) (hL0 : coeff 0 L = 1)
    (hH : qExpansion 1 H = L.map (Int.castRingHom ℂ)) :
    ∃ a b : ℚ, a = 1 / sigma k 0 - coeff 1 L ∧
      b = (1 + 2 ^ (k - 1)) / sigma k 0 - coeff 2 L - a * (coeff 1 L_A - 24) ∧
      ∀ n, sigma k n / sigma k 0 = coeff n L + a * coeff n (deltaZ * L_A) +
        b * coeff n ((deltaZ ^ 2 * Z₂ : ℤ⟦X⟧)) := by
  have hwt : (w₁ : ℤ) = k - 12 := by omega
  have hwt2 : (w₂ : ℤ) = w₁ - 12 := by omega
  have hF0 : F₂ ≠ 0 := by
    intro h
    have hh := congrArg (coeff 0) hF₂
    simp [h, coeff_map, hZ₂, qExpansion_zero] at hh
  have hk0 : k ≠ 0 := by omega
  have hAc0 : constantCoeff L_A = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hA0
  let U := E h3 - H
  have hU : qExpansion 1 U = qExpansion 1 (E h3) - L.map (Int.castRingHom ℂ) :=
    (ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL (E h3) H).trans (by rw [hH])
  have hc : coeff 0 (qExpansion 1 U) = 0 := by
    rw [hU, map_sub, E_qExpansion_coeff_zero h3 he, coeff_map, hL0, map_one, sub_self]
  let V := (CuspForm.discriminantEquiv (U.toCuspForm hc)).mcast hwt.symm
  have hVm : qExpansion 1 V =
      qExpansion 1 (CuspForm.discriminantEquiv (U.toCuspForm hc)) := by
    simp only [V, ModularForm.qExpansion_mcast]
  have hV : qExpansion 1 U = qExpansion 1 discriminant * qExpansion 1 V := by
    rw [hVm]
    exact qExpansion_eq_qExpansion_discriminant_mul U hc
  let ac : ℂ := coeff 0 (qExpansion 1 V)
  let V' : ModularForm 𝒮ℒ w₁ := V - ac • A
  have hV' : qExpansion 1 V' = qExpansion 1 V - ac • L_A.map (Int.castRingHom ℂ) :=
    (ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL V (ac • A)).trans (by
      change qExpansion 1 ⇑V - qExpansion 1 (ac • ⇑A) =
        qExpansion 1 ⇑V - ac • L_A.map (Int.castRingHom ℂ)
      rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, hA])
  have hc' : coeff 0 (qExpansion 1 V') = 0 := by
    rw [hV', map_sub, coeff_smul, smul_eq_mul, coeff_map, hA0, map_one, mul_one]
    exact sub_self _
  obtain ⟨bc, hW⟩ := cusp_quotient V' hc' hwt2 hr F₂ Z₂ hF₂ hF0
  have hqV : qExpansion 1 V =
      ac • L_A.map (Int.castRingHom ℂ) + bc • (deltaZ * Z₂).map (Int.castRingHom ℂ) := by
    have h1 : qExpansion 1 V =
        ac • L_A.map (Int.castRingHom ℂ) + qExpansion 1 V' := by
      rw [hV']
      abel
    rw [h1, hW]
  have hqU : qExpansion 1 U = ac • (deltaZ * L_A).map (Int.castRingHom ℂ) +
      bc • (deltaZ ^ 2 * Z₂).map (Int.castRingHom ℂ) := by
    have eB : deltaZ * (deltaZ * Z₂) = deltaZ ^ 2 * Z₂ := by ring
    rw [hV, hqV, qExpansion_discriminant, mul_add, mul_smul_comm, mul_smul_comm, ← map_mul,
      ← map_mul, eB]
  have hcoeff (n : ℕ) :
      ((sigma k n / sigma k 0 : ℚ) : ℂ) - coeff n L =
        ac * coeff n (deltaZ * L_A) + bc * coeff n ((deltaZ ^ 2 * Z₂ : ℤ⟦X⟧)) := by
    simpa only [hU, map_sub, coeff_eisenstein h3 he, coeff_map, Int.coe_castRingHom,
      map_add, coeff_smul, smul_eq_mul] using congrArg (coeff n) hqU
  have hA1 : coeff 1 (deltaZ * L_A) = 1 := by
    change coeff (0 + 1) ((X * pentagonalSeries ℤ ^ 24) * L_A) = 1
    rw [mul_assoc, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, map_mul, map_pow,
      constantCoeff_pentagonalSeries_int]
    simpa [coeff_zero_eq_constantCoeff_apply] using hA0
  have hB1 : coeff 1 (deltaZ ^ 2 * Z₂) = 0 := by
    have h : (1 : ℕ) = 0 + 1 := rfl
    rw [deltaZ_sq_mul, h, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, map_mul]
    simp
  have hB2 : coeff 2 (deltaZ ^ 2 * Z₂) = 1 := by
    have h : (2 : ℕ) = 1 + 1 := rfl
    have h1 : (1 : ℕ) = 0 + 1 := rfl
    rw [deltaZ_sq_mul, h, coeff_succ_X_mul, h1, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, constantCoeff_pentagonalSeries_int]
    simpa [coeff_zero_eq_constantCoeff_apply] using hZ₂
  have hA2 : coeff 2 (deltaZ * L_A) = coeff 1 L_A - 24 := by
    change coeff (1 + 1) ((X * pentagonalSeries ℤ ^ 24) * L_A) = _
    rw [mul_assoc, coeff_succ_X_mul, coeff_one_mul, constantCoeff_pentagonalSeries_pow,
      coeff_one_pentagonalSeries_pow, hAc0]
    push_cast
    ring
  have hs1 : sigma k 1 = 1 := sigma_one hk0
  have hs2 : sigma k 2 = 1 + 2 ^ (k - 1) := by
    simpa using sigma_prime hk0 Nat.prime_two
  have hac1 := hcoeff 1
  rw [hA1, hB1, Int.cast_one, Int.cast_zero, mul_one, mul_zero, add_zero, hs1] at hac1
  have hbc2 := hcoeff 2
  rw [hA2, hB2, Int.cast_one, mul_one, hs2] at hbc2
  refine ⟨1 / sigma k 0 - coeff 1 L,
    (1 + 2 ^ (k - 1)) / sigma k 0 - coeff 2 L -
      (1 / sigma k 0 - coeff 1 L) * (coeff 1 L_A - 24), rfl, rfl, fun n => ?_⟩
  have hn := hcoeff n
  have hac_eq : ac = ((1 / sigma k 0 - coeff 1 L : ℚ) : ℂ) := by
    exact_mod_cast hac1.symm
  rw [hac_eq] at hbc2 hn
  have h1 : bc = (((1 + 2 ^ (k - 1)) / sigma k 0 : ℚ) : ℂ) - coeff 2 L -
      ((1 / sigma k 0 - coeff 1 L : ℚ) : ℂ) * ((coeff 1 L_A - 24 : ℤ) : ℂ) := by
    linear_combination -hbc2
  have hbc_eq : bc = ((((1 + 2 ^ (k - 1)) / sigma k 0 - coeff 2 L -
      (1 / sigma k 0 - coeff 1 L) * (coeff 1 L_A - 24) : ℚ)) : ℂ) := by
    exact_mod_cast h1
  rw [hbc_eq] at hn
  have hQ : sigma k n / sigma k 0 - coeff n L =
      (1 / sigma k 0 - coeff 1 L) * coeff n (deltaZ * L_A) +
        ((1 + 2 ^ (k - 1)) / sigma k 0 - coeff 2 L -
          (1 / sigma k 0 - coeff 1 L) * (coeff 1 L_A - 24)) *
          coeff n ((deltaZ ^ 2 * Z₂ : ℤ⟦X⟧)) := by
    exact_mod_cast hn
  linear_combination hQ

private lemma coefficient_congruence_two (k : ℕ)
    (hk : k ∈ ({24, 28, 30, 32, 34, 38} : Finset ℕ))
    (N : ℕ) (hd : N ∣ (sigma k 0).num.natAbs) (n : ℕ) :
    ((sigma k n - (coeff n (deltaZ.map (Int.castRingHom ℚ) * PowerSeries.mk (sigma (k - 12))) /
      sigma (k - 12) 0 + (2 ^ (k - 1) + 25 - 1 / sigma (k - 12) 0) *
      (coeff n ((deltaZ.map (Int.castRingHom ℚ)) ^ 2 * PowerSeries.mk (sigma (k - 24))) /
        sigma (k - 24) 0))) / N).den.Coprime N := by
  have hk24 : 24 ≤ k := by fin_cases hk <;> decide
  have h3 : 3 ≤ k := by omega
  have he : Even k := by fin_cases hk <;> decide
  have he1 : Even (k - 12) := by fin_cases hk <;> decide
  have he2 : Even (k - 24) := by fin_cases hk <;> decide
  have h31 : 3 ≤ k - 12 := by omega
  have hkw : k = 12 + (k - 12) := by omega
  have hw : k - 12 = 12 + (k - 24) := by omega
  have hw2mem : k - 24 ∈ ({0, 4, 6, 8, 10, 14} : Finset ℕ) := by fin_cases hk <;> decide
  have hr : Module.rank ℂ (ModularForm 𝒮ℒ (k - 24 : ℕ)) = 1 := by
    rw [dimension_level_one (k - 24) he2]
    fin_cases hk <;> norm_num [Nat.ModEq]
  obtain ⟨F₂, Z₂, hZ₂, hF₂, hσ₂⟩ := integral_eisenstein hw2mem
  obtain ⟨F₄, Z₄, hZ₄, hF₄, -⟩ := integral_eisenstein (w := 4) (by decide)
  have h0k := sigma_zero_ne h3 he
  have h01 := sigma_zero_ne h31 he1
  have hc2 : sigma (k - 24) 0 ≠ 0 := by fin_cases hk <;> decide +kernel
  let A : ModularForm 𝒮ℒ (k - 12 : ℕ) :=
    ModularForm.mcast (by exact_mod_cast (show 3 * 4 + (k - 24) = k - 12 by omega))
      ((F₄.pow 3).mul F₂)
  let L_A : ℤ⟦X⟧ := Z₄ ^ 3 * Z₂
  have hA : qExpansion 1 A = L_A.map (Int.castRingHom ℂ) := by
    simp only [A, L_A, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, hF₄, hF₂, map_mul, map_pow]
  have hA0 : coeff 0 L_A = 1 := by
    have e4 : constantCoeff Z₄ = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      exact hZ₄
    have e2 : constantCoeff Z₂ = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      exact hZ₂
    simp only [L_A, coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, e4, e2, one_pow,
      one_mul]
  let H : ModularForm 𝒮ℒ k :=
    ModularForm.mcast (by exact_mod_cast (show 3 * 4 + (k - 12) = k by omega))
      ((F₄.pow 3).mul A)
  let L : ℤ⟦X⟧ := Z₄ ^ 3 * L_A
  have hH : qExpansion 1 H = L.map (Int.castRingHom ℂ) := by
    simp only [H, L, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, hF₄, hA, map_mul, map_pow]
  have hL0 : coeff 0 L = 1 := by
    have e4 : constantCoeff Z₄ = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      exact hZ₄
    have eA : constantCoeff L_A = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      exact hA0
    simp only [L, coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, e4, eA, one_pow,
      one_mul]
  obtain ⟨v, hv, hEv⟩ := eisenstein_sub_integral hw h31 he1 hr F₂ Z₂ hZ₂ hF₂ A L_A hA0 hA
  obtain ⟨a, b, ha, hb, hEk⟩ := eisenstein_two_step hkw hw h3 he hr F₂ Z₂ hZ₂ hF₂
    A L_A hA0 hA H L hL0 hH
  have hm2 : PowerSeries.mk (sigma (k - 24)) =
      sigma (k - 24) 0 • Z₂.map (Int.castRingHom ℚ) := by
    ext i
    simpa [coeff_smul, coeff_map] using hσ₂ i
  have hb2 : coeff n ((deltaZ.map (Int.castRingHom ℚ)) ^ 2 *
      PowerSeries.mk (sigma (k - 24))) / sigma (k - 24) 0 =
      coeff n ((deltaZ ^ 2 * Z₂ : ℤ⟦X⟧)) := by
    rw [hm2, mul_smul_comm, ← map_pow, ← map_mul, coeff_smul, smul_eq_mul,
      mul_div_cancel_left₀ _ hc2]
    simp only [coeff_map, Int.coe_castRingHom]
  have hm1 : PowerSeries.mk (sigma (k - 12)) = sigma (k - 12) 0 •
      PowerSeries.mk (fun i => sigma (k - 12) i / sigma (k - 12) 0) := by
    ext i
    simp only [coeff_mk, coeff_smul, smul_eq_mul]
    exact (div_mul_cancel₀ _ h01).symm.trans (mul_comm _ _)
  have hS : PowerSeries.mk (fun i => sigma (k - 12) i / sigma (k - 12) 0) =
      L_A.map (Int.castRingHom ℚ) + v • (deltaZ * Z₂).map (Int.castRingHom ℚ) := by
    ext i
    simp only [coeff_mk, map_add, coeff_map, coeff_smul, smul_eq_mul,
      Int.coe_castRingHom]
    exact hEv i
  have hb1 : coeff n (deltaZ.map (Int.castRingHom ℚ) * PowerSeries.mk (sigma (k - 12))) /
      sigma (k - 12) 0 =
      coeff n (deltaZ * L_A) + v * coeff n ((deltaZ ^ 2 * Z₂ : ℤ⟦X⟧)) := by
    have eB : deltaZ * (deltaZ * Z₂) = deltaZ ^ 2 * Z₂ := by ring
    rw [hm1, mul_smul_comm, hS, mul_add, mul_smul_comm, ← map_mul, ← map_mul, eB,
      coeff_smul, smul_eq_mul, mul_div_cancel_left₀ _ h01]
    simp only [map_add, coeff_smul, smul_eq_mul, coeff_map, Int.coe_castRingHom]
  have hσ : sigma k n = sigma k 0 * (sigma k n / sigma k 0) := by
    rw [mul_comm (sigma k 0) _, div_mul_cancel₀ _ h0k]
  rw [hb1, hb2]
  obtain ⟨z, hz⟩ : ∃ z : ℤ, sigma k n - ((coeff n (deltaZ * L_A) +
      v * coeff n ((deltaZ ^ 2 * Z₂ : ℤ⟦X⟧))) +
      (2 ^ (k - 1) + 25 - 1 / sigma (k - 12) 0) * coeff n ((deltaZ ^ 2 * Z₂ : ℤ⟦X⟧))) =
      sigma k 0 * z := by
    refine ⟨coeff n L - coeff 1 L * coeff n (deltaZ * L_A) +
      ((coeff 1 L_A - 24) * coeff 1 L - coeff 2 L) * coeff n (deltaZ ^ 2 * Z₂), ?_⟩
    rw [hσ, hEk n]
    subst ha
    subst hb
    subst hv
    push_cast
    field_simp [h0k, h01]
    ring
  rw [hz]
  exact coprime_den hd z

end
end eisenstein_congr_delta_mul_eisenstein_dim_one

open eisenstein_congr_delta_mul_eisenstein_dim_one

/-- **Lu's one-term congruence for $G_k$.** Let $k \in \{12, 16, 18, 20, 22, 26\}$.
For $w, n \in \mathbb{N}$ let $\sigma_{-1}(n)$ be $1$ if $n = 0$ and $0$ otherwise; for $w \ge 1$
let $\sigma_{w-1}(0) = -B_w/(2w)$, where $B_w$ is the $w$-th Bernoulli number, and
$\sigma_{w-1}(n) = \sum_{d \mid n} d^{w-1}$ for $n \ge 1$. In $\mathbb{Q}[[q]]$ let
$G_w = \sum_{n \ge 0} \sigma_{w-1}(n) q^n$, let $E_w = G_w/\sigma_{w-1}(0)$ for even $w$, and let
$\Delta = q \prod_{j \ge 1} (1 - q^j)^{24}$; for $i, n \in \mathbb{N}$ write $b_i(n)$ for the
coefficient of $q^n$ in $\Delta^i E_{k-12i}$. Let $N_w = 1$ for $w \le 2$, let $N_w$ be the
absolute value of the numerator of $\sigma_{w-1}(0)$ for $w \ge 3$, and let $N'_k$ be the largest
divisor of $N_k$ that is coprime to $N_{k-12i}$ for every $1 \le i \le \lfloor k/12 \rfloor$. For
rationals $x, y$ and a positive integer $N$, $x \equiv y \pmod{N}$ means that $(x - y)/N$ has
denominator coprime to $N$. Then
$\sigma_{k-1}(n) \equiv b_1(n) \pmod{N'_k}$ for every $n \ge 0$, that is,
$G_k \equiv \Delta E_{k-12} \pmod{N'_k}$ coefficientwise; in particular the congruence holds for
every $n \ge 1$.

Source: Qing Lu, *Explicit Congruences for Modular Forms of Higher Weights*, Journal of
Integer Sequences 29 (2026), Article 26.5.1, Corollary 5 (`jis-2026-26.5.1-cor-5`). -/
public theorem eisenstein_congr_delta_mul_eisenstein_dim_one (k : ℕ)
    (hk : k ∈ ({12, 16, 18, 20, 22, 26} : Finset ℕ)) :
    let σ₀ : ℕ → ℕ → ℚ := fun w n => if w = 0 then (if n = 0 then 1 else 0)
      else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    let b : ℕ → ℕ → ℚ := fun i n =>
      coeff n (Δ ^ i * PowerSeries.mk (σ₀ (k - 12 * i))) / σ₀ (k - 12 * i) 0
    let Nw : ℕ → ℕ := fun w => if w ≤ 2 then 1 else (σ₀ w 0).num.natAbs
    let N' : ℕ := ((Nat.divisors (Nw k)).filter fun d =>
      ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id
    (∀ n : ℕ, ((σ₀ k n - b 1 n) / N').den.Coprime N') ∧
      ∀ n : ℕ, 1 ≤ n → ((σ₀ k n - b 1 n) / N').den.Coprime N' := by
  intro σ₀ Δ b Nw N'
  have h3 : 3 ≤ k := by fin_cases hk <;> decide
  have he : Even k := by fin_cases hk <;> decide
  have hNk : Nw k = (sigma k 0).num.natAbs := ite_eq_right (by omega)
  have hpos : Nw k ≠ 0 := by simpa [hNk] using sigma_zero_ne h3 he
  let s := (Nat.divisors (Nw k)).filter fun d =>
    ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))
  have hs : s.Nonempty := ⟨1, by simp [s, hpos]⟩
  obtain ⟨d, hd, heq⟩ := Finset.sup_mem_of_nonempty (f := id) hs
  have hdiv : N' ∣ (sigma k 0).num.natAbs := by
    change s.sup id ∣ _
    rw [← heq, ← hNk]
    exact Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
  have hall (n : ℕ) := coefficient_congruence k hk N' hdiv n
  have H (n : ℕ) : ((σ₀ k n - b 1 n) / N').den.Coprime N' := by
    change ((sigma k n - coeff n (Δ ^ 1 * PowerSeries.mk (sigma (k - 12 * 1))) /
      sigma (k - 12 * 1) 0) / N').den.Coprime N'
    simpa only [pow_one, mul_one, Δ, ← deltaZ_rat] using hall n
  exact ⟨H, fun n _ => H n⟩

/-- **Lu's two-term congruence for $G_k$.** Let $k \in \{24, 28, 30, 32, 34, 38\}$.
For $w, n \in \mathbb{N}$ let $\sigma_{-1}(n)$ be $1$ if $n = 0$ and $0$ otherwise; for $w \ge 1$
let $\sigma_{w-1}(0) = -B_w/(2w)$, where $B_w$ is the $w$-th Bernoulli number, and
$\sigma_{w-1}(n) = \sum_{d \mid n} d^{w-1}$ for $n \ge 1$. In $\mathbb{Q}[[q]]$ let
$G_w = \sum_{n \ge 0} \sigma_{w-1}(n) q^n$, let $E_w = G_w/\sigma_{w-1}(0)$ for even $w$, and let
$\Delta = q \prod_{j \ge 1} (1 - q^j)^{24}$; for $i, n \in \mathbb{N}$ write $b_i(n)$ for the
coefficient of $q^n$ in $\Delta^i E_{k-12i}$. Let $N_w = 1$ for $w \le 2$, let $N_w$ be the
absolute value of the numerator of $\sigma_{w-1}(0)$ for $w \ge 3$, and let $N'_k$ be the largest
divisor of $N_k$ that is coprime to $N_{k-12i}$ for every $1 \le i \le \lfloor k/12 \rfloor$. For
rationals $x, y$ and a positive integer $N$, $x \equiv y \pmod{N}$ means that $(x - y)/N$ has
denominator coprime to $N$. Let
$\gamma_2 = 2^{k-1} + 25 - 1/\sigma_{k-13}(0)$. Then
$\sigma_{k-1}(n) \equiv b_1(n) + \gamma_2 b_2(n) \pmod{N'_k}$ for every $n \ge 0$, that is,
$G_k \equiv \Delta E_{k-12} + \gamma_2 \Delta^2 E_{k-24} \pmod{N'_k}$ coefficientwise; in
particular the congruence holds for every $n \ge 1$.

Source: Qing Lu, *Explicit Congruences for Modular Forms of Higher Weights*, Journal of
Integer Sequences 29 (2026), Article 26.5.1, Corollary 6 (`jis-2026-26.5.1-cor-6`). -/
public theorem eisenstein_congr_delta_mul_eisenstein_dim_two (k : ℕ)
    (hk : k ∈ ({24, 28, 30, 32, 34, 38} : Finset ℕ)) :
    let σ₀ : ℕ → ℕ → ℚ := fun w n => if w = 0 then (if n = 0 then 1 else 0)
      else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    let b : ℕ → ℕ → ℚ := fun i n =>
      coeff n (Δ ^ i * PowerSeries.mk (σ₀ (k - 12 * i))) / σ₀ (k - 12 * i) 0
    let Nw : ℕ → ℕ := fun w => if w ≤ 2 then 1 else (σ₀ w 0).num.natAbs
    let N' : ℕ := ((Nat.divisors (Nw k)).filter fun d =>
      ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id
    let γ₂ : ℚ := 2 ^ (k - 1) + 25 - 1 / σ₀ (k - 12) 0
    (∀ n : ℕ, ((σ₀ k n - (b 1 n + γ₂ * b 2 n)) / N').den.Coprime N') ∧
      ∀ n : ℕ, 1 ≤ n → ((σ₀ k n - (b 1 n + γ₂ * b 2 n)) / N').den.Coprime N'
    := by
  intro σ₀ Δ b Nw N' γ₂
  have h3 : 3 ≤ k := by fin_cases hk <;> decide
  have he : Even k := by fin_cases hk <;> decide
  have hNk : Nw k = (sigma k 0).num.natAbs := ite_eq_right (by omega)
  have hpos : Nw k ≠ 0 := by simpa [hNk] using sigma_zero_ne h3 he
  let s := (Nat.divisors (Nw k)).filter fun d =>
    ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))
  have hs : s.Nonempty := ⟨1, by simp [s, hpos]⟩
  obtain ⟨d, hd, heq⟩ := Finset.sup_mem_of_nonempty (f := id) hs
  have hdiv : N' ∣ (sigma k 0).num.natAbs := by
    change s.sup id ∣ _
    rw [← heq, ← hNk]
    exact Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
  have hall (n : ℕ) := coefficient_congruence_two k hk N' hdiv n
  have e1 : k - 12 * 1 = k - 12 := by omega
  have e2 : k - 12 * 2 = k - 24 := by omega
  have H (n : ℕ) : ((σ₀ k n - (b 1 n + γ₂ * b 2 n)) / N').den.Coprime N' := by
    change ((sigma k n - (coeff n (Δ ^ 1 * PowerSeries.mk (sigma (k - 12 * 1))) /
      sigma (k - 12 * 1) 0 + (2 ^ (k - 1) + 25 - 1 / sigma (k - 12) 0) *
      (coeff n (Δ ^ 2 * PowerSeries.mk (sigma (k - 12 * 2))) / sigma (k - 12 * 2) 0))) /
      N').den.Coprime N'
    simpa only [e1, e2, pow_one, Δ, ← deltaZ_rat] using hall n
  exact ⟨H, fun n _ => H n⟩

/-- **Lu's three-term congruence for $G_k$.** Let $k \in \{36, 40, 42, 44, 46, 50\}$.
For $w, n \in \mathbb{N}$ let $\sigma_{-1}(n)$ be $1$ if $n = 0$ and $0$ otherwise; for $w \ge 1$
let $\sigma_{w-1}(0) = -B_w/(2w)$, where $B_w$ is the $w$-th Bernoulli number, and
$\sigma_{w-1}(n) = \sum_{d \mid n} d^{w-1}$ for $n \ge 1$. In $\mathbb{Q}[[q]]$ let
$G_w = \sum_{n \ge 0} \sigma_{w-1}(n) q^n$, let $E_w = G_w/\sigma_{w-1}(0)$ for even $w$, and let
$\Delta = q \prod_{j \ge 1} (1 - q^j)^{24}$; for $i, n \in \mathbb{N}$ write $b_i(n)$ for the
coefficient of $q^n$ in $\Delta^i E_{k-12i}$. Let $N_w = 1$ for $w \le 2$, let $N_w$ be the
absolute value of the numerator of $\sigma_{w-1}(0)$ for $w \ge 3$, and let $N'_k$ be the largest
divisor of $N_k$ that is coprime to $N_{k-12i}$ for every $1 \le i \le \lfloor k/12 \rfloor$. For
rationals $x, y$ and a positive integer $N$, $x \equiv y \pmod{N}$ means that $(x - y)/N$ has
denominator coprime to $N$. Let
$\gamma_2 = 2^{k-1} + 25 - 1/\sigma_{k-13}(0)$ and
$\gamma_3 = 3^{k-1} + 48 \cdot 2^{k-1} + 949 - (2^{k-13} + 25)/\sigma_{k-13}(0) -
(2^{k-1} + 25)/\sigma_{k-25}(0) + 1/\bigl(\sigma_{k-13}(0)\,\sigma_{k-25}(0)\bigr)$. Then
$\sigma_{k-1}(n) \equiv b_1(n) + \gamma_2 b_2(n) + \gamma_3 b_3(n) \pmod{N'_k}$ for every
$n \ge 0$, that is,
$G_k \equiv \Delta E_{k-12} + \gamma_2 \Delta^2 E_{k-24} + \gamma_3 \Delta^3 E_{k-36}
\pmod{N'_k}$ coefficientwise; in particular the congruence holds for every $n \ge 1$.

Source: Qing Lu, *Explicit Congruences for Modular Forms of Higher Weights*, Journal of
Integer Sequences 29 (2026), Article 26.5.1, Corollary 7 (`jis-2026-26.5.1-cor-7`). -/
public theorem eisenstein_congr_delta_mul_eisenstein_dim_three (k : ℕ)
    (hk : k ∈ ({36, 40, 42, 44, 46, 50} : Finset ℕ)) :
    let σ₀ : ℕ → ℕ → ℚ := fun w n => if w = 0 then (if n = 0 then 1 else 0)
      else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    let b : ℕ → ℕ → ℚ := fun i n =>
      coeff n (Δ ^ i * PowerSeries.mk (σ₀ (k - 12 * i))) / σ₀ (k - 12 * i) 0
    let Nw : ℕ → ℕ := fun w => if w ≤ 2 then 1 else (σ₀ w 0).num.natAbs
    let N' : ℕ := ((Nat.divisors (Nw k)).filter fun d =>
      ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id
    let γ₂ : ℚ := 2 ^ (k - 1) + 25 - 1 / σ₀ (k - 12) 0
    let γ₃ : ℚ := 3 ^ (k - 1) + 2 ^ (k - 1) * 48 + 949 - (2 ^ (k - 13) + 25) / σ₀ (k - 12) 0 -
      (2 ^ (k - 1) + 25) / σ₀ (k - 24) 0 + 1 / (σ₀ (k - 12) 0 * σ₀ (k - 24) 0)
    (∀ n : ℕ, ((σ₀ k n - (b 1 n + γ₂ * b 2 n + γ₃ * b 3 n)) / N').den.Coprime N') ∧
      ∀ n : ℕ, 1 ≤ n → ((σ₀ k n - (b 1 n + γ₂ * b 2 n + γ₃ * b 3 n)) / N').den.Coprime N' := by
  intro σ₀ Δ b Nw N' γ₂ γ₃
  have hk₃₆ : 36 ≤ k := by fin_cases hk <;> decide
  have he : Even k := by fin_cases hk <;> decide
  have hNk : Nw k = (sigma k 0).num.natAbs := ite_eq_right (by omega)
  have hpos : Nw k ≠ 0 := by simpa [hNk] using sigma_zero_ne (by omega : 3 ≤ k) he
  let s := (Nat.divisors (Nw k)).filter fun d =>
    ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))
  have hs : s.Nonempty := ⟨1, by simp [s, hpos]⟩
  obtain ⟨d, hd, heq⟩ := Finset.sup_mem_of_nonempty (f := id) hs
  obtain ⟨hdvd, hcop⟩ := Finset.mem_filter.mp hd
  have hN' : d = N' := heq
  have hdiv : N' ∣ (sigma k 0).num.natAbs := by
    rw [← hN', ← hNk]
    exact Nat.dvd_of_mem_divisors hdvd
  have hC (i : ℕ) (hi₁ : 1 ≤ i) (hi₃ : i ≤ 3) :
      (sigma (k - 12 * i) 0).num.natAbs.Coprime N' := by
    have hi : i ∈ Finset.Icc 1 (k / 12) := Finset.mem_Icc.mpr ⟨hi₁, by omega⟩
    have hwi : k - 12 * i = 0 ∨ 3 ≤ k - 12 * i := by
      interval_cases i <;> fin_cases hk <;> decide
    rcases hwi with hwi | hwi
    · simp [hwi, sigma]
    have hi' : Nw (k - 12 * i) = (sigma (k - 12 * i) 0).num.natAbs := ite_eq_right (by omega)
    rw [← hN', ← hi']
    exact (hcop i hi).symm
  have hs₁ : sigma (k - 12) 0 ≠ 0 :=
    sigma_zero_ne (by omega) (by fin_cases hk <;> decide)
  have hs₂ : sigma (k - 24) 0 ≠ 0 :=
    sigma_zero_ne (by omega) (by fin_cases hk <;> decide)
  have hb (i n : ℕ) : b i n = coeff n (basisRat k i) := by
    change coeff n (Δ ^ i * PowerSeries.mk (sigma (k - 12 * i))) / sigma (k - 12 * i) 0 = _
    simp only [Δ, ← deltaZ_rat, basisRat, eisensteinRat, mul_smul_comm, coeff_smul, smul_eq_mul,
      div_eq_mul_inv]
    ring
  have H (n : ℕ) : ((σ₀ k n - (b 1 n + γ₂ * b 2 n + γ₃ * b 3 n)) / N').den.Coprime N' := by
    have hcoef : coeff n (cancelThree k (PowerSeries.mk (sigma k))) =
        σ₀ k n - (b 1 n + γ₂ * b 2 n + γ₃ * b 3 n) := by
      rw [hb, hb, hb]
      exact coeff_cancelThree_sigma hk₃₆ hs₁ hs₂ n
    rw [← hcoef]
    exact coefficient_congruence_three k hk N' hdiv hC n
  exact ⟨H, fun n _ => H n⟩

section GeneralCongruence

open UpperHalfPlane EisensteinSeries ModularForm
open scoped MatrixGroups

noncomputable section

private lemma isRatExpansion_sum_smul {ι : Type*} {k : ℕ} (s : Finset ι)
    (x : ι → ℚ) (B : ι → ℚ⟦X⟧) (hB : ∀ i, IsRatExpansion k (B i)) :
    IsRatExpansion k (∑ i ∈ s, x i • B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp [qExpansion_zero]⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, add_comm]
    have hneg : (-x i) • B i = -(x i • B i) := neg_smul _ _
    simpa only [hneg, sub_neg_eq_add] using ih.sub_smul (hB i) (-x i)

-- With determinant one the inverse is an adjugate, so it stays in the same subring.
private lemma inv_mem_subring_of_det_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Subring ℚ) (C : Matrix ι ι ℚ) (hdet : C.det = 1) (hC : ∀ i j, C i j ∈ S)
    (i j : ι) : C⁻¹ i j ∈ S := by
  let D : Matrix ι ι S := fun i j => ⟨C i j, hC i j⟩
  have hD : S.subtype.mapMatrix D = C := rfl
  rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul, ← hD, ← RingHom.map_adjugate]
  exact (D.adjugate i j).property

-- As in `coefficient_congruence_three`, compare with an integral form and use
-- `qExpansion_eq_zero_of_order` to identify the residual expansion.
private lemma coefficient_congruence_general (k m N : ℕ) (hk : 12 ≤ k) (he : Even k)
    (hkm : 12 * m ≤ k) (hw : k - 12 * m ∈ ({0, 4, 6, 8, 10, 14} : Finset ℕ))
    (hinner : ∀ i : Fin m, k - 12 * (i.val + 1) = 0 ∨ 3 ≤ k - 12 * (i.val + 1))
    (hd : N ∣ (sigma k 0).num.natAbs)
    (hcop : ∀ i : Fin m, (sigma (k - 12 * (i.val + 1)) 0).num.natAbs.Coprime N)
    (n : ℕ) :
    let B (i : Fin m) := basisRat k (i.val + 1)
    let C : Matrix (Fin m) (Fin m) ℚ := fun i j => coeff (j.val + 1) (B i)
    let γ := Matrix.vecMul (fun j : Fin m => sigma k (j.val + 1)) C⁻¹
    ((sigma k n - ∑ i : Fin m, γ i * coeff n (B i)) / N).den.Coprime N := by
  intro B C γ
  let w := k - 12 * m
  have hwt : (k : ℤ) = (w : ℤ) + 12 * (m : ℤ) := by dsimp [w]; omega
  obtain ⟨H, Z, hZ, hH, -⟩ := integral_eisenstein hw
  obtain ⟨F₄, Z₄, hZ₄, hF₄, -⟩ := integral_eisenstein (w := 4) (by decide)
  let L := (Z₄ ^ (3 * m) * Z).map (Int.castRingHom ℚ)
  have hL : IsRatExpansion k L := by
    refine ⟨ModularForm.mcast (by push_cast; omega) ((F₄.pow (3 * m)).mul H), ?_⟩
    simp only [ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos
      one_mem_strictPeriods_SL, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      hF₄, hH, L, map_int_rat_complex, map_mul, map_pow]
  have hL₀ : coeff 0 L = 1 := by
    dsimp only [L]
    rw [coeff_map, coeff_zero_eq_constantCoeff_apply, map_mul, map_pow,
      ← coeff_zero_eq_constantCoeff_apply Z, ← coeff_zero_eq_constantCoeff_apply Z₄, hZ, hZ₄]
    simp
  have heven (i : Fin m) : Even (k - 12 * (i.val + 1)) := by
    obtain ⟨t, ht⟩ := he
    exact even_iff_two_dvd.mpr (by omega)
  have hs (i : Fin m) : sigma (k - 12 * (i.val + 1)) 0 ≠ 0 := by
    rcases hinner i with h | h
    · simp [h, sigma]
    · exact sigma_zero_ne h (heven i)
  have hB (i : Fin m) : IsRatExpansion k (B i) := by
    suffices ∃ F : ModularForm 𝒮ℒ (↑(k - 12 * (i.val + 1)) : ℤ),
        qExpansion 1 F = (eisensteinRat (k - 12 * (i.val + 1))).map ratToComplex by
      obtain ⟨F, hF⟩ := this
      exact isRatExpansion_basis k (i.val + 1) (by have := i.isLt; omega) F hF
    rcases hinner i with h | h
    · rw [h]
      refine ⟨(1 : ModularForm 𝒮ℒ 0), ?_⟩
      rw [ModularForm.qExpansion_one]
      ext j
      simp [coeff_eisensteinRat, sigma, coeff_one]
    · exact ⟨E h, qExpansion_eisensteinRat h (heven i)⟩
  have htri (i : Fin m) (j : ℕ) (hj : j ≤ i.val + 1) :
      coeff j (B i) = if j = i.val + 1 then 1 else 0 :=
    coeff_basisRat_le k _ j hj (hs i)
  have hB₀ (i : Fin m) : coeff 0 (B i) = 0 := by
    rw [htri i 0 (by omega), ite_eq_right (by omega)]
  have hdiag (i : Fin m) : coeff (i.val + 1) (B i) = 1 := by
    rw [htri i _ le_rfl, ite_eq_left rfl]
  have hdet : C.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (show C.IsUpperTriangular from fun i j hij ↦ by
      change coeff (j.val + 1) (B i) = 0
      have h : j.val < i.val := hij
      rw [htri i (j.val + 1) (by omega), ite_eq_right (by omega)])]
    simp [C, hdiag]
  let G := PowerSeries.mk (sigma k)
  let A := G - sigma k 0 • L
  let v (P : ℚ⟦X⟧) := Matrix.vecMul (fun j : Fin m => coeff (j.val + 1) P) C⁻¹
  let T (P : ℚ⟦X⟧) := ∑ i : Fin m, v P i • B i
  have hA : IsRatExpansion k A := (isRatExpansion_sigma (by omega) he).sub_smul hL _
  obtain ⟨F, hF⟩ : IsRatExpansion k (A - T A) := by
    simpa only [one_smul] using hA.sub_smul (isRatExpansion_sum_smul Finset.univ (v A) B hB) 1
  have hunit : IsUnit C.det := by rw [hdet]; exact isUnit_one
  have hrow : Matrix.vecMul (v A) C = fun j : Fin m => coeff (j.val + 1) A := by
    dsimp only [v]
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hunit, Matrix.vecMul_one]
  have hvanish (j : ℕ) (hj : j < m + 1) : coeff j (A - T A) = 0 := by
    by_cases hj₀ : j = 0
    · subst j
      simp only [A, G, T, map_sub, map_sum, coeff_smul, smul_eq_mul, hL₀, hB₀, coeff_mk,
        mul_one, mul_zero, Finset.sum_const_zero, sub_self]
    · let i : Fin m := ⟨j - 1, by omega⟩
      have hi : i.val + 1 = j := by dsimp [i]; omega
      have h := congrFun hrow i
      change Matrix.vecMul (v A) C i = coeff (i.val + 1) A at h
      rw [Matrix.vecMul_apply_eq_sum] at h
      simp only [C, hi] at h
      simpa only [T, map_sub, map_sum, coeff_smul, smul_eq_mul] using sub_eq_zero.mpr h.symm
  let F' := F.mcast hwt
  have hF' : qExpansion 1 F' = (A - T A).map ratToComplex := by
    simpa only [F', ModularForm.qExpansion_mcast] using hF
  have hOrder : (m : ℕ∞) < (qExpansion 1 F').order := by
    refine (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self m)).trans_le
      (PowerSeries.nat_le_order _ _ ?_)
    intro j hj
    rw [hF', coeff_map, hvanish j hj, map_zero]
  have hH₀ : coeff 0 (qExpansion 1 H) = 1 := by rw [hH, coeff_map, hZ, map_one]
  have hr : Module.rank ℂ (ModularForm 𝒮ℒ (w : ℤ)) = 1 := by
    suffices ∀ u : ℕ, u ∈ ({0, 4, 6, 8, 10, 14} : Finset ℕ) →
        Module.rank ℂ (ModularForm 𝒮ℒ (u : ℤ)) = 1 from this w hw
    intro u hu
    have heu : Even u := by fin_cases hu <;> decide
    rw [dimension_level_one u heu]
    fin_cases hu <;> norm_num [Nat.modEq_iff_dvd]
  have hEq : A = T A := sub_eq_zero.mp ((PowerSeries.map_eq_zero _ ratToComplex).mp
    (hF'.symm.trans (qExpansion_eq_zero_of_order H hH₀ hr m F' hOrder)))
  have hvA : v A = v G - sigma k 0 • v L := by
    have h : (fun j : Fin m => coeff (j.val + 1) A) =
        (fun j : Fin m => coeff (j.val + 1) G) - sigma k 0 • (fun j => coeff (j.val + 1) L) := by
      funext j
      simp only [A, map_sub, coeff_smul, Pi.sub_apply, Pi.smul_apply]
    dsimp only [v]
    rw [h, Matrix.sub_vecMul, Matrix.smul_vecMul]
  have hTA : T A = T G - sigma k 0 • T L := by
    simp only [T, hvA, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, smul_smul,
      Finset.sum_sub_distrib, Finset.smul_sum]
  have hGL : G - T G = sigma k 0 • (L - T L) := by
    calc
      G - T G = (A - T A) + sigma k 0 • (L - T L) := by
        rw [hTA, smul_sub]
        dsimp only [A]
        abel
      _ = _ := by rw [sub_eq_zero.mpr hEq, zero_add]
  let S := coprimeDenRing N
  have hBmem (i : Fin m) (j : ℕ) : coeff j (B i) ∈ S :=
    coeff_basisRat_mem_coprimeDenRing (hs i) (hcop i) j
  have hvmem (i : Fin m) : v L i ∈ S := by
    dsimp only [v]
    rw [Matrix.vecMul_apply_eq_sum]
    exact S.sum_mem fun j _ => S.mul_mem (coeff_map_int_mem_coprimeDenRing N _ _)
      (inv_mem_subring_of_det_one S C hdet (fun i j => hBmem i (j.val + 1)) j i)
  have hTmem : coeff n (L - T L) ∈ S := by
    simp only [T, map_sub, map_sum, coeff_smul, smul_eq_mul]
    exact S.sub_mem (coeff_map_int_mem_coprimeDenRing N _ _)
      (S.sum_mem fun i _ => S.mul_mem (hvmem i) (hBmem i n))
  have hcN : sigma k 0 / N ∈ S := by
    change (sigma k 0 / N).den.Coprime N
    simpa using coprime_den hd 1
  have hcoeff : coeff n (G - T G) / N ∈ S := by
    rw [hGL, coeff_smul, smul_eq_mul, mul_comm, mul_div_assoc]
    exact S.mul_mem hTmem hcN
  change (sigma k n - ∑ i : Fin m, γ i * coeff n (B i)) / N ∈ S
  simpa only [G, T, v, γ, map_sub, map_sum, coeff_smul, smul_eq_mul, coeff_mk] using hcoeff

end
end GeneralCongruence

/-- **Lu's congruence for the Eisenstein series $G_k$.** Let $k \ge 12$ be even with $k \ne 14$.
For $w, n \in \mathbb{N}$ let $\sigma_{-1}(n)$ be $1$ if $n = 0$ and $0$ otherwise; for $w \ge 1$
let $\sigma_{w-1}(0) = -B_w/(2w)$, where $B_w$ is the $w$-th Bernoulli number, and
$\sigma_{w-1}(n) = \sum_{d \mid n} d^{w-1}$ for $n \ge 1$. In $\mathbb{Q}[[q]]$ let
$G_w = \sum_{n \ge 0} \sigma_{w-1}(n) q^n$, let $E_w = G_w/\sigma_{w-1}(0)$ for even $w$, and let
$\Delta = q \prod_{j \ge 1} (1 - q^j)^{24}$; for $i, n \in \mathbb{N}$ write $b_i(n)$ for the
coefficient of $q^n$ in $\Delta^i E_{k-12i}$. Let $N_w = 1$ for $w \le 2$, let $N_w$ be the
absolute value of the numerator of $\sigma_{w-1}(0)$ for $w \ge 3$, and let $N'_k$ be the largest
divisor of $N_k$ that is coprime to $N_{k-12i}$ for every $1 \le i \le \lfloor k/12 \rfloor$. For
rationals $x, y$ and a positive integer $N$, $x \equiv y \pmod{N}$ means that $(x - y)/N$ has
denominator coprime to $N$. Let $m = \lfloor k/12 \rfloor - 1$ if
$k \equiv 2 \pmod{12}$ and $m = \lfloor k/12 \rfloor$ otherwise, let $C$ be the $m \times m$ matrix
$(b_i(j))_{1 \le i, j \le m}$, and let
$(\gamma_1, \dots, \gamma_m) = (\sigma_{k-1}(1), \dots, \sigma_{k-1}(m))\, C^{-1}$. Then
$\sigma_{k-1}(n) \equiv \sum_{i=1}^m \gamma_i b_i(n) \pmod{N'_k}$ for every $n \ge 0$, that is,
$G_k \equiv \sum_{i=1}^m \gamma_i \Delta^i E_{k-12i} \pmod{N'_k}$ coefficientwise.

Source: Qing Lu, *Explicit Congruences for Modular Forms of Higher Weights*, Journal of
Integer Sequences 29 (2026), Article 26.5.1, Theorem 1 (`jis-2026-26.5.1-thm-1`). -/
public theorem eisenstein_congr_sum_delta_pow_mul_eisenstein (k : ℕ) (hk : 12 ≤ k)
    (hke : Even k) (hk14 : k ≠ 14) :
    let σ₀ : ℕ → ℕ → ℚ := fun w n => if w = 0 then (if n = 0 then 1 else 0)
      else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    let b : ℕ → ℕ → ℚ := fun i n =>
      coeff n (Δ ^ i * PowerSeries.mk (σ₀ (k - 12 * i))) / σ₀ (k - 12 * i) 0
    let Nw : ℕ → ℕ := fun w => if w ≤ 2 then 1 else (σ₀ w 0).num.natAbs
    let N' : ℕ := ((Nat.divisors (Nw k)).filter fun d =>
      ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id
    let m : ℕ := if k % 12 = 2 then k / 12 - 1 else k / 12
    let C : Matrix (Fin m) (Fin m) ℚ := fun i j => b (i.val + 1) (j.val + 1)
    let γ : Fin m → ℚ := Matrix.vecMul (fun j => σ₀ k (j.val + 1)) C⁻¹
    ∀ n : ℕ, ((σ₀ k n - ∑ i : Fin m, γ i * b (i.val + 1) n) / N').den.Coprime N' := by
  intro σ₀ Δ b Nw N' m C γ n
  have hNk : Nw k = (sigma k 0).num.natAbs := ite_eq_right (by omega)
  have hpos : Nw k ≠ 0 := by simpa [hNk] using sigma_zero_ne (by omega : 3 ≤ k) hke
  let s := (Nat.divisors (Nw k)).filter fun d =>
    ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))
  have hs : s.Nonempty := ⟨1, by simp [s, hpos]⟩
  have hN : N' ∈ s := by
    obtain ⟨d, hd, heq⟩ := Finset.sup_mem_of_nonempty (f := id) hs
    change d = N' at heq
    exact heq ▸ hd
  obtain ⟨hd, hcop⟩ := Finset.mem_filter.mp hN
  have hdiv : N' ∣ (sigma k 0).num.natAbs := hNk ▸ Nat.dvd_of_mem_divisors hd
  obtain ⟨t, ht⟩ := hke
  have hm : m ≤ k / 12 := by dsimp [m]; split_ifs <;> omega
  have hm₂ (h : k % 12 = 2) : m + 1 = k / 12 := by
    have h24 : 24 ≤ k := by
      by_contra! hlt
      exact hk14 (by omega)
    dsimp [m]
    rw [ite_eq_left h]
    omega
  have hw : k - 12 * m ∈ ({0, 4, 6, 8, 10, 14} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases h : k % 12 = 2
    · have := hm₂ h
      omega
    · dsimp [m]
      rw [ite_eq_right h]
      omega
  have hinner (i : Fin m) : k - 12 * (i.val + 1) = 0 ∨ 3 ≤ k - 12 * (i.val + 1) := by
    have hi := i.isLt
    dsimp [m] at hi
    split_ifs at hi <;> omega
  have hlocal (i : Fin m) : (sigma (k - 12 * (i.val + 1)) 0).num.natAbs.Coprime N' := by
    rcases hinner i with h | h
    · simp [h, sigma]
    · have hNw : Nw (k - 12 * (i.val + 1)) = (sigma (k - 12 * (i.val + 1)) 0).num.natAbs :=
        ite_eq_right (by omega)
      rw [← hNw]
      exact (hcop (i.val + 1) (Finset.mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩)).symm
  have hσ (w j : ℕ) : σ₀ w j = sigma w j := rfl
  have hb (i j : ℕ) : b i j = coeff j (basisRat k i) := by
    change coeff j (Δ ^ i * PowerSeries.mk (sigma (k - 12 * i))) / sigma (k - 12 * i) 0 = _
    rw [show Δ = deltaRat from deltaZ_rat.symm, basisRat, eisensteinRat, mul_smul_comm,
      coeff_smul, smul_eq_mul, div_eq_mul_inv]
    exact mul_comm _ _
  let D : Matrix (Fin m) (Fin m) ℚ := fun i j => coeff (j.val + 1) (basisRat k (i.val + 1))
  have hC : C = D := funext fun i => funext fun j => hb _ _
  have hγ : γ = Matrix.vecMul (fun j : Fin m => sigma k (j.val + 1)) D⁻¹ := by
    simp only [γ, hC, hσ]
  simpa only [hγ, hb, hσ, D] using
    coefficient_congruence_general k m N' hk ⟨t, ht⟩ (by omega) hw hinner hdiv hlocal n

/-- **Lu's congruence for the divisor sums $\sigma_{k-1}(n)$.** Let $k \ge 12$ be even with
$k \ne 14$. For $w, n \in \mathbb{N}$ let $\sigma_{-1}(n)$ be $1$ if $n = 0$ and $0$ otherwise;
for $w \ge 1$ let $\sigma_{w-1}(0) = -B_w/(2w)$, where $B_w$ is the $w$-th Bernoulli number, and
$\sigma_{w-1}(n) = \sum_{d \mid n} d^{w-1}$ for $n \ge 1$. In $\mathbb{Q}[[q]]$ let
$G_w = \sum_{n \ge 0} \sigma_{w-1}(n) q^n$ and $\Delta = q \prod_{j \ge 1} (1 - q^j)^{24}$, and
for $i, n \in \mathbb{N}$ let $c_i(n)$ be the coefficient of $q^n$ in $\Delta^i G_{k-12i}$, that
is, the additive convolution $(\tau^{*i} * \sigma_{k-12i-1})(n)$, where $\tau(n)$ is the
coefficient of $q^n$ in $\Delta$. Let $N_w = 1$ for $w \le 2$, let $N_w$ be the absolute value of
the numerator of $\sigma_{w-1}(0)$ for $w \ge 3$, and let $N'_k$ be the largest divisor of $N_k$
that is coprime to $N_{k-12i}$ for every $1 \le i \le \lfloor k/12 \rfloor$. For rationals $x, y$
and a positive integer $N$, $x \equiv y \pmod{N}$ means that $(x - y)/N$ has denominator coprime
to $N$. Let $m = \lfloor k/12 \rfloor - 1$ if $k \equiv 2 \pmod{12}$ and
$m = \lfloor k/12 \rfloor$ otherwise, let $C$ be the $m \times m$ matrix
$\bigl(c_i(j)/\sigma_{k-12i-1}(0)\bigr)_{1 \le i, j \le m}$, and let
$(\gamma_1, \dots, \gamma_m) = (\sigma_{k-1}(1), \dots, \sigma_{k-1}(m))\, C^{-1}$. Then for every
$n \ge 1$, $\sigma_{k-1}(n) \equiv
\sum_{i=1}^m \bigl(\gamma_i/\sigma_{k-12i-1}(0)\bigr)\, c_i(n) \pmod{N'_k}$.

Source: Qing Lu, *Explicit Congruences for Modular Forms of Higher Weights*, Journal of
Integer Sequences 29 (2026), Article 26.5.1, Corollary 3 (`jis-2026-26.5.1-cor-3`). -/
public theorem sigma_congr_sum_tau_conv_sigma (k : ℕ) (hk : 12 ≤ k) (hke : Even k)
    (hk14 : k ≠ 14) :
    let σ₀ : ℕ → ℕ → ℚ := fun w n => if w = 0 then (if n = 0 then 1 else 0)
      else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    let conv : ℕ → ℕ → ℚ := fun i n => coeff n (Δ ^ i * PowerSeries.mk (σ₀ (k - 12 * i)))
    let Nw : ℕ → ℕ := fun w => if w ≤ 2 then 1 else (σ₀ w 0).num.natAbs
    let N' : ℕ := ((Nat.divisors (Nw k)).filter fun d =>
      ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id
    let m : ℕ := if k % 12 = 2 then k / 12 - 1 else k / 12
    let C : Matrix (Fin m) (Fin m) ℚ := fun i j =>
      conv (i.val + 1) (j.val + 1) / σ₀ (k - 12 * (i.val + 1)) 0
    let γ : Fin m → ℚ := Matrix.vecMul (fun j => σ₀ k (j.val + 1)) C⁻¹
    ∀ n : ℕ, 1 ≤ n → ((σ₀ k n - ∑ i : Fin m,
      γ i / σ₀ (k - 12 * (i.val + 1)) 0 * conv (i.val + 1) n) / N').den.Coprime N' := by
  intro σ₀ Δ conv Nw N' m C γ n _
  have h := eisenstein_congr_sum_delta_pow_mul_eisenstein k hk hke hk14 n
  change ((σ₀ k n - ∑ i : Fin m,
    γ i * (conv (i.val + 1) n / σ₀ (k - 12 * (i.val + 1)) 0)) / N').den.Coprime N' at h
  simpa only [← mul_div_assoc, div_mul_eq_mul_div] using h

end MetaMathlibExt
