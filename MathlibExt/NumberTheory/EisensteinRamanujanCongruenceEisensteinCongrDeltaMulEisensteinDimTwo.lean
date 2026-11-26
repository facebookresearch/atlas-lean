/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Bernoulli
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import MathlibExt.NumberTheory.GeneralizedTau
import MathlibExt.NumberTheory.ModularForms.QParamProduct

/-!
# Lu's two-term Eisenstein congruence

In the six weights with a two-dimensional cusp space, the coefficients of the Eisenstein
series are congruent to those of the discriminant times a normalized Eisenstein series plus
an explicit multiple of the squared discriminant times another normalized Eisenstein series.

Statements from Qing Lu, *Explicit Congruences for Modular Forms of Higher Weights*, Journal of
Integer Sequences 29 (2026), Article 26.5.1.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

namespace eisenstein_congr_delta_mul_eisenstein_dim_two

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
  · simp [sigma, hn, show k ≠ 0 by omega, div_eq_mul_inv, mul_comm, mul_left_comm]

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

private lemma coeff_one_mul (f g : ℤ⟦X⟧) :
    coeff 1 (f * g) = coeff 0 f * coeff 1 g + coeff 1 f * coeff 0 g := by
  rw [coeff_mul]
  simp only [show Finset.antidiagonal 1 = {(0, 1), (1, 0)} by decide,
    Finset.sum_pair (by decide : (0, 1) ≠ (1, 0))]

private lemma coeff_one_pentagonal : coeff 1 (pentagonalSeries ℤ) = -1 := by
  have h1 : pentagonal 1 = 1 := by norm_num [pentagonal_def]
  rw [← h1, coeff_pentagonalSeries_pentagonal]
  decide

private lemma const_pow_pentagonal (m : ℕ) :
    constantCoeff (pentagonalSeries ℤ ^ m) = 1 := by
  rw [map_pow, constantCoeff_pentagonalSeries_int, one_pow]

private lemma coeff_one_pow_pentagonal (m : ℕ) :
    coeff 1 (pentagonalSeries ℤ ^ m) = -(m : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [pow_succ, coeff_one_mul, coeff_zero_eq_constantCoeff_apply,
      const_pow_pentagonal, coeff_one_pentagonal, ih, constantCoeff_pentagonalSeries_int]
    push_cast
    ring

private lemma deltaZ_coeff_zero : coeff 0 deltaZ = 0 := by
  rw [deltaZ, coeff_zero_eq_constantCoeff_apply, map_mul]
  simp

private lemma deltaZ_coeff_one : coeff 1 deltaZ = 1 := by
  have h : (1 : ℕ) = 0 + 1 := rfl
  rw [h, deltaZ, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, map_pow,
    constantCoeff_pentagonalSeries_int]
  simp

private lemma deltaZ_coeff_two : coeff 2 deltaZ = -24 := by
  have h : (2 : ℕ) = 1 + 1 := rfl
  rw [h, deltaZ, coeff_succ_X_mul]
  simpa using coeff_one_pow_pentagonal 24

private lemma sigma_one {k : ℕ} (hk : k ≠ 0) : sigma k 1 = 1 := by
  simp [sigma, hk]

private lemma sigma_two {k : ℕ} (hk : k ≠ 0) : sigma k 2 = 1 + 2 ^ (k - 1) := by
  have h2 : ArithmeticFunction.sigma (k - 1) 2 = 1 + 2 ^ (k - 1) := by
    rw [ArithmeticFunction.sigma_apply, show Nat.divisors 2 = {1, 2} by decide,
      Finset.sum_pair (by decide)]
    simp
  simp [sigma, hk, show (2 : ℕ) ≠ 0 by decide, h2]

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
    rw [mul_assoc, coeff_succ_X_mul, coeff_one_mul, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, const_pow_pentagonal, coeff_one_pow_pentagonal, hAc0]
    push_cast
    ring
  have hs1 : sigma k 1 = 1 := sigma_one hk0
  have hs2 : sigma k 2 = 1 + 2 ^ (k - 1) := sigma_two hk0
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
end eisenstein_congr_delta_mul_eisenstein_dim_two

open eisenstein_congr_delta_mul_eisenstein_dim_two

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

end MetaMathlibExt
