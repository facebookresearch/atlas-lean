/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Instances.Rat
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import MathlibExt.NumberTheory.GeneralizedTau
import MathlibExt.NumberTheory.ModularForms.QParamProduct

/-!
# Lu's one-term Eisenstein congruence

In the six weights with a one-dimensional cusp space, the coefficients of the Eisenstein
series are congruent to those of the discriminant times a normalized Eisenstein series.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

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

end MetaMathlibExt
