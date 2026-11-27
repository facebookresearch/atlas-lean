/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.lean`,
`P2M/Sol/S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.lean`,
`Theorems/Thm_ModularCurve_exists_aeval_jq_sub_holomorphicAtInfty.lean`,
`P2M/Sol/S_ModularCurve_exists_aeval_jq_sub_holomorphicAtInfty.lean`,
`Theorems/Thm_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant.lean`,
and
`P2M/Sol/S_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.JExpansion
public import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.PhiGen
public import MathlibExt.NumberTheory.ModularForms.LevelNAlgebra
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

noncomputable section

open UpperHalfPlane Complex Filter Topology Function
open scoped MatrixGroups ModularForm

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

namespace Realized

variable {h : ℝ} {F : ℍ → ℂ} {c : ℕ → ℂ}

private lemma hasSum_cuspFunction_punctured (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) {q : ℂ} (hq : ‖q‖ < 1)
    (hq1 : q ≠ 0) : HasSum (fun m : ℕ => c m * q ^ m) (cuspFunction h F q) := by
  have h1 := Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq1
  let τ : ℍ := ⟨Periodic.invQParam h q, h1⟩
  have h2 := Periodic.cuspFunction_eq_of_ne_zero h (F ∘ ofComplex) hq1
  have h3 : cuspFunction h F q = F τ := by
    simpa [τ, cuspFunction, UpperHalfPlane.ofComplex_apply_of_im_pos h1] using h2
  have h4 : 𝕢 h (τ : ℂ) = q := Periodic.qParam_right_inv hh.ne' hq1
  rw [h3, ← h4]
  exact hF τ

private lemma hasFPowerSeriesOnBall_update (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    HasFPowerSeriesOnBall (update (cuspFunction h F) 0 (c 0)) (.ofScalars ℂ c) 0 1 := by
  constructor
  · refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
    rcases eq_or_ne r 0 with rfl | hr'
    · simp
    · lift r to NNReal using hr.ne_top
      let : FiniteDimensional ℝ ℂ := basisOneI.finiteDimensional_of_finite
      apply FormalMultilinearSeries.le_radius_of_summable
      simpa [norm_mul, mul_comm] using
        (hasSum_cuspFunction_punctured hh hF (q := r) (by simpa using hr)
          (mod_cast hr')).summable.norm
  · simp
  · intro y hy
    rw [zero_add]
    rw [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one, mem_ball_zero_iff] at hy
    rcases eq_or_ne y 0 with rfl | hy'
    · simpa +contextual [zero_pow_eq] using hasSum_ite_eq 0 (c 0)
    · simpa [update_of_ne hy', mul_comm] using hasSum_cuspFunction_punctured hh hF hy hy'

private def discFun (h : ℝ) (F : ℍ → ℂ) (c : ℕ → ℂ) : ℂ → ℂ := update (cuspFunction h F) 0 (c 0)

private lemma hasSum_discFun (hh : 0 < h) (hF : ∀ τ : ℍ,
    HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ))
    {q : ℂ} (hq : ‖q‖ < 1) : HasSum (fun m : ℕ => c m * q ^ m) (discFun h F c q) := by
  have hy : q ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.coe_one, Metric.eball_coe]; simpa using hq
  have h := (hasFPowerSeriesOnBall_update hh hF).hasSum hy
  rw [zero_add] at h
  simpa [discFun, mul_comm] using h

private lemma apply_eq_discFun (hh : 0 < h) (hF : ∀ τ : ℍ,
    HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ))
    (τ : ℍ) : F τ = discFun h F c (𝕢 h (τ : ℂ)) :=
  (hF τ).unique (hasSum_discFun hh hF (Periodic.norm_qParam_lt_one hh τ.im_pos))

private lemma differentiableOn_discFun (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    DifferentiableOn ℂ (discFun h F c) (Metric.ball 0 1) := by
  have h1 := (hasFPowerSeriesOnBall_update hh hF).differentiableOn
  rwa [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one] at h1

private lemma continuousAt_discFun (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) {q : ℂ} (hq : ‖q‖ < 1) :
    ContinuousAt (discFun h F c) q :=
  ((differentiableOn_discFun hh hF).differentiableAt
    (Metric.isOpen_ball.mem_nhds (by simpa using hq))).continuousAt

private lemma discFun_zero : discFun h F c 0 = c 0 := by simp [discFun]

private theorem mdifferentiable (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h1 : DifferentiableOn ℂ (fun z : ℂ => discFun h F c (𝕢 h z)) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hzq : ‖𝕢 h z‖ < 1 := Periodic.norm_qParam_lt_one hh hz
    exact (((differentiableOn_discFun hh hF).differentiableAt
      (Metric.isOpen_ball.mem_nhds (by simpa using hzq))).comp z
      ((Periodic.differentiable_qParam (h := h)) z)).differentiableWithinAt
  refine h1.congr fun z hz => ?_
  simp only [Function.comp_apply, apply_eq_discFun hh hF, ofComplex_apply_of_im_pos hz]

private theorem tendsto_atImInfty (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    Tendsto F atImInfty (𝓝 (c 0)) := by
  have h1 : Tendsto (fun τ : ℍ => discFun h F c (𝕢 h (τ : ℂ))) atImInfty (𝓝 (discFun h F c 0)) :=
    (continuousAt_discFun hh hF (q := 0) (by simp)).tendsto.comp (qParam_tendsto_atImInfty hh)
  rw [discFun_zero] at h1
  exact h1.congr fun τ => (apply_eq_discFun hh hF τ).symm

private theorem isBoundedAtImInfty (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ)) :
    IsBoundedAtImInfty F :=
  (tendsto_atImInfty hh hF).isBigO_one ℝ

private theorem coeff_unique {d : ℕ → ℂ} (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℕ => c m * 𝕢 h (τ : ℂ) ^ m) (F τ))
    (hF' : ∀ τ : ℍ, HasSum (fun m : ℕ => d m * 𝕢 h (τ : ℂ) ^ m) (F τ)) : c = d := by
  have hc := hasFPowerSeriesOnBall_update hh hF
  have hd := hasFPowerSeriesOnBall_update hh hF'
  have hlim : ∀ {e : ℕ → ℂ},
      HasFPowerSeriesOnBall (update (cuspFunction h F) 0 (e 0)) (.ofScalars ℂ e) 0 1 →
      Tendsto (cuspFunction h F) (𝓝[≠] 0) (𝓝 (e 0)) := by
    intro e he
    have h1 : Tendsto (update (cuspFunction h F) 0 (e 0)) (𝓝[≠] 0) (𝓝 (e 0)) := by
      have := he.hasFPowerSeriesAt.continuousAt.tendsto
      rw [update_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz using update_of_ne hz ..
  have h0 : c 0 = d 0 := tendsto_nhds_unique (hlim hc) (hlim hd)
  have hd' : HasFPowerSeriesOnBall (update (cuspFunction h F) 0 (c 0)) (.ofScalars ℂ d) 0 1 :=
      h0 ▸ hd
  have heq := hc.hasFPowerSeriesAt.eq_formalMultilinearSeries hd'.hasFPowerSeriesAt
  funext m
  simpa using congr_arg (FormalMultilinearSeries.coeff · m) heq

end Realized

end ModularCurve

open ModularCurve in
theorem ModularCurve.coeff_eq_zero_of_hasSum_of_slash_invariant {F : UpperHalfPlane → ℂ}
    {c : ℕ → ℂ}
    (hF : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ => c m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ))
    (hinv : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane), F (γ • τ) = F τ)
    {m : ℕ} (hm : m ≠ 0) : c m = 0 := by
  have hslash : ∀ γ : SL(2, ℤ), F ∣[(0 : ℤ)] γ = F := fun γ => by
    funext τ
    rw [ModularForm.SL_slash_apply, hinv, neg_zero, zpow_zero, mul_one]
  let f : ModularForm 𝒮ℒ 0 :=
    { toFun := F
      slash_action_eq' := fun A hA => by
        obtain ⟨γ, rfl⟩ := hA
        exact hslash γ
      holo' := Realized.mdifferentiable one_pos hF
      bdd_at_cusps' := fun {cusp} hc => by
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [hslash γ]
        exact Realized.isBoundedAtImInfty one_pos hF }
  obtain ⟨κ, hκ⟩ := ModularForm.eq_const_of_weight_zero f
  have hFκ : ∀ τ : ℍ, F τ = κ := fun τ => by
    exact congr_fun hκ τ
  have hF' : ∀ τ : ℍ, HasSum (fun m : ℕ => (Pi.single (M :=
      fun _ => ℂ) 0 κ m) * 𝕢 1 (τ : ℂ) ^ m) (F τ) := by
    intro τ
    rw [hFκ τ]
    have := hasSum_ite_eq 0 κ
    refine this.congr_fun fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]
  have heq := Realized.coeff_unique one_pos hF hF'
  rw [heq, Pi.single_apply, ite_eq_right hm]

end

noncomputable section

open Polynomial

namespace ModularCurve

private theorem poleOrderLE_sub_aeval_jq_succ {f : LaurentSeries ℚ} {n : ℕ}
    (hf : PoleOrderLE f (n + 1)) :
    PoleOrderLE
      (f - Polynomial.aeval jq
        (Polynomial.C (f.coeff (-(n + 1 : ℕ) : ℤ)) * Polynomial.X ^ (n + 1))) n := by
  intro k hk
  rw [HahnSeries.coeff_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
    algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul]
  rcases (show k ≤ -((n + 1 : ℕ) : ℤ) by omega).eq_or_lt with heq | hlt
  · rw [heq, coeff_jq_pow_self, mul_one, sub_self]
  · rw [hf k hlt, coeff_jq_pow_of_lt hlt, mul_zero, sub_zero]

theorem exists_aeval_jq_sub_holomorphicAtInfty (n : ℕ) :
    ∀ f : LaurentSeries ℚ, PoleOrderLE f n →
      ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ PoleOrderLE (f - Polynomial.aeval jq P) 0 := by
  induction n with
  | zero =>
    intro f hf
    exact ⟨0, by simp, by simpa using hf⟩
  | succ n ih =>
    intro f hf
    obtain ⟨Q, hQdeg, hQ⟩ := ih _ (poleOrderLE_sub_aeval_jq_succ hf)
    refine ⟨Polynomial.C (f.coeff (-(n + 1 : ℕ) : ℤ)) * Polynomial.X ^ (n + 1) + Q, ?_, ?_⟩
    · refine le_trans (Polynomial.natDegree_add_le _ _)
        (max_le (Polynomial.natDegree_C_mul_X_pow_le _ _) ?_)
      omega
    · intro k hk
      rw [map_add, sub_add_eq_sub_sub]
      exact hQ k hk

end ModularCurve


noncomputable section

open UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

def RealL (h : ℝ) (A : LaurentSeries ℂ) (F : ℍ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun m : ℤ => A.coeff m * 𝕢 h (τ : ℂ) ^ m) (F τ)

namespace RealL

variable {h : ℝ} {A B : LaurentSeries ℂ} {F G : ℍ → ℂ}

lemma add (hA : RealL h A F) (hB : RealL h B G) : RealL h (A + B) (F + G) := fun τ => by
  simpa [add_mul] using (hA τ).add (hB τ)

lemma neg (hA : RealL h A F) : RealL h (-A) (-F) := fun τ => by
  simpa [neg_mul] using (hA τ).neg

lemma sub (hA : RealL h A F) (hB : RealL h B G) : RealL h (A - B) (F - G) := fun τ => by
  simpa [sub_mul] using (hA τ).sub (hB τ)

lemma mul (hh : 0 < h) (hA : RealL h A F) (hB : RealL h B G) : RealL h (A * B) (F * G) :=
    fun τ =>
  hasSum_qParam_mul_laurent h hh A B F G hA hB τ

lemma single (h : ℝ) (a : ℂ) (n : ℤ) :
    RealL h (HahnSeries.single n a) (fun τ => a * 𝕢 h (τ : ℂ) ^ n) := fun τ => by
  refine (hasSum_ite_eq n (a * 𝕢 h (τ : ℂ) ^ n)).congr_fun fun m => ?_
  by_cases hm : m = n
  · subst hm; simp
  · simp [HahnSeries.coeff_single_of_ne hm, hm]

lemma C (h : ℝ) (a : ℂ) : RealL h (HahnSeries.C a) (fun _ => a) := by
  simpa using single h a 0

lemma congr {A' : LaurentSeries ℂ} {F' : ℍ → ℂ} (hA : RealL h A F) (h1 : A = A') (h2 : ∀ τ,
    F τ = F' τ) :
    RealL h A' F' := fun τ => by rw [← h1, ← h2]; exact hA τ

lemma one (h : ℝ) : RealL h 1 1 :=
  (C h 1).congr (map_one _) fun _ => rfl

lemma zero (h : ℝ) : RealL h 0 0 := fun τ => by simp [hasSum_zero]

lemma coeff_prod_X_sub_C (hh : 0 < h) {ι : Type} (s : Finset ι) {a : ι → LaurentSeries ℂ}
    {α : ι → ℍ → ℂ} (haα : ∀ i ∈ s, RealL h (a i) (α i)) (k : ℕ) :
    RealL h ((∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff k)
      (fun τ => (∏ i ∈ s, (Polynomial.X - Polynomial.C (α i τ))).coeff k) := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Polynomial.coeff_one]
    by_cases hk : k = 0
    · subst hk
      exact (one h).congr (by simp) fun _ => by simp
    · exact (zero h).congr (by simp [hk]) fun _ => by simp [hk]
  | insert b s hb ih =>
    have ih' := fun k => ih (fun i hi => haα i (Finset.mem_insert_of_mem hi)) k
    have hb' := haα b (Finset.mem_insert_self b s)
    have hA : (∏ i ∈ insert b s, (Polynomial.X - Polynomial.C (a i))) =
        (∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))) * (Polynomial.X - Polynomial.C (a b)) :=
      (Finset.prod_insert hb).trans (mul_comm (G := Polynomial (LaurentSeries ℂ)) _ _)
    have hfun : ∀ τ : ℍ, (∏ i ∈ insert b s, (Polynomial.X - Polynomial.C (α i τ))) =
        (∏ i ∈ s, (Polynomial.X - Polynomial.C (α i τ))) * (Polynomial.X - Polynomial.C (α b τ)) :=
      fun τ => (Finset.prod_insert hb).trans (mul_comm (G := Polynomial ℂ) _ _)
    cases k with
    | zero =>
      refine ((ih' 0).mul hh hb').neg.congr ?_ fun τ => ?_
      · rw [hA, Polynomial.mul_coeff_zero, Polynomial.coeff_sub, Polynomial.coeff_X_zero,
          Polynomial.coeff_C_zero, zero_sub]
        exact (mul_neg (α := LaurentSeries ℂ) _ _).symm
      · simp only [hfun τ, Polynomial.mul_coeff_zero, Pi.neg_apply, Pi.mul_apply,
          Polynomial.coeff_sub,
          Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, mul_neg]
    | succ k =>
      refine ((ih' k).sub ((ih' (k + 1)).mul hh hb')).congr ?_ fun τ => ?_
      · rw [hA, Polynomial.coeff_mul_X_sub_C]
      · simp only [hfun τ, Polynomial.coeff_mul_X_sub_C, Pi.sub_apply, Pi.mul_apply]

end RealL

section JT

def jqC : LaurentSeries ℂ := coeffMap (Rat.castHom ℂ) jq

lemma jqC_coeff (m : ℤ) : jqC.coeff m = ((jq.coeff m : ℚ) : ℂ) := rfl

lemma realL_jqC : RealL 1 jqC WLight.jFunction := fun τ => ModularCurve.hasSum_jq_qParam τ

end JT

section JOut

private lemma jFunction_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    WLight.jFunction (γ • τ) = WLight.jFunction τ :=
  ModularCurve.E4_cube_div_discriminant_smul γ τ

private lemma realL_aeval_jq (P : Polynomial ℚ) :
    RealL 1 (coeffMap (Rat.castHom ℂ) (Polynomial.aeval jq P))
      (fun τ => (P.map (Rat.castHom ℂ)).eval (WLight.jFunction τ)) := by
  induction P using Polynomial.induction_on with
  | C a =>
    refine (RealL.C 1 (a : ℂ)).congr ?_ fun τ => ?_
    · rw [Polynomial.aeval_C, algebraMap_laurentSeries_eq_single, coeffMap_single]
      rfl
    · simp
  | add P Q hP hQ =>
    refine (hP.add hQ).congr ?_ fun τ => ?_
    · rw [map_add, map_add]
    · simp
  | monomial n a ih =>
    refine (ih.mul one_pos realL_jqC).congr ?_ fun τ => ?_
    · unfold jqC
      rw [← map_mul]
      congr 1
      symm
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    · simp [pow_succ, mul_assoc]

theorem mem_adjoin_jq_of_hasSum_of_slash_invariant (f : LaurentSeries ℚ) (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m) (F τ))
    (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), F (γ • τ) = F τ) : f ∈ Algebra.adjoin ℚ {jq} := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, PoleOrderLE f n := by
    by_cases hf0 : f = 0
    · exact ⟨0, fun m _ => by simp [hf0]⟩
    refine ⟨(-f.order).toNat,
        fun m hm => HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hm ?_)⟩
    have := Int.self_le_toNat (-f.order)
    omega
  obtain ⟨P, -, he⟩ := ModularCurve.exists_aeval_jq_sub_holomorphicAtInfty n f hn
  set e : LaurentSeries ℚ := f - Polynomial.aeval jq P with he_def
  have he0 : ∀ m : ℤ, m < 0 → e.coeff m = 0 := fun m hm => he m (by simpa using hm)
  have hfR : RealL 1 (coeffMap (Rat.castHom ℂ) f) F := hF
  have hE : RealL 1 (coeffMap (Rat.castHom ℂ) e)
      (F - fun τ => (P.map (Rat.castHom ℂ)).eval (WLight.jFunction τ)) := by
    rw [he_def, map_sub]
    exact hfR.sub (realL_aeval_jq P)
  have hEinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ),
      (F - fun τ => (P.map (Rat.castHom ℂ)).eval (WLight.jFunction τ)) (γ • τ) = (F - fun τ =>
          (P.map (Rat.castHom ℂ)).eval (WLight.jFunction τ)) τ := by
    intro γ τ
    simp only [Pi.sub_apply, hinv γ τ, jFunction_smul γ τ]
  have hEN : ∀ τ : ℍ, HasSum (fun n : ℕ => ((e.coeff n : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ n)
      ((F - fun τ => (P.map (Rat.castHom ℂ)).eval (WLight.jFunction τ)) τ) := by
    intro τ
    have h := hE τ
    rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff] at h
    · exact h
    · intro m hm
      have hm' : m < 0 := by
        by_contra hge
        push Not at hge
        exact hm ⟨m.toNat, Int.toNat_of_nonneg hge⟩
      rw [coeffMap_coeff, he0 m hm', map_zero, zero_mul]
  have hvan : ∀ n : ℕ, n ≠ 0 → e.coeff n = 0 := fun n hn => by
    have := coeff_eq_zero_of_hasSum_of_slash_invariant hEN hEinv hn
    exact_mod_cast this
  have heconst : e = HahnSeries.single 0 (e.coeff 0) := by
    ext m
    rcases lt_trichotomy m 0 with hm | rfl | hm
    · rw [he0 m hm, HahnSeries.coeff_single_of_ne hm.ne]
    · rw [HahnSeries.coeff_single_same]
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm.le
      rw [HahnSeries.coeff_single_of_ne (by exact_mod_cast hm.ne')]
      exact hvan n (by exact_mod_cast hm.ne')
  have hck : f = algebraMap ℚ (LaurentSeries ℚ) (e.coeff 0) + Polynomial.aeval jq P := by
    rw [algebraMap_laurentSeries_eq_single, ← heconst, he_def, sub_add_cancel]
  rw [hck]
  exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
      (Polynomial.aeval_mem_adjoin_singleton ℚ jq)

end JOut

end ModularCurve

end
