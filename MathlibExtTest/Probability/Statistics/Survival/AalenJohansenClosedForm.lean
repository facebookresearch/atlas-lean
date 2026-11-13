/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.AalenJohansenClosedForm
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Filter
open MathlibExt.Probability.Statistics.Censoring
open MathlibExt.Probability.Statistics.SurvivalConsistency
open MathlibExt.Probability.Statistics.AalenJohansenCLT
open MathlibExt.Probability.Statistics.AalenJohansenClosedForm

namespace MathlibExtTest.Probability.Statistics.AalenJohansenClosedForm

/-- The independent-censoring law is a probability measure (local instance for the examples). -/
private theorem isProbabilityMeasure_indepCauseLaw {k r : ℕ} (pTJ : PMF (Fin k × Fin r))
    (pC : PMF (Fin k)) : IsProbabilityMeasure (indepCauseLaw pTJ pC) := by
  unfold indepCauseLaw; infer_instance

attribute [local instance] isProbabilityMeasure_indepCauseLaw

/-! ### Definitions on concrete cell vectors -/

/-- A cell vector on `Cell 2 1` with every event coordinate `1` and every at-risk coordinate
`4`. -/
private noncomputable def u₀ : EuclideanSpace ℝ (Cell 2 1) :=
  WithLp.toLp 2 fun
    | Sum.inl _ => 1
    | Sum.inr _ => 4

/-- The ratio is event over at-risk, `1 / 4`. -/
example (l : Fin 2) (c : Fin 1) : cellRatio u₀ l c = 1 / 4 := by
  simp [cellRatio, u₀]

/-- The increment of the cell vector of a subject failing at `0` from cause `0`, centred by `u₀`:
`1 - (1/4) · 1 = 3/4` at grid index `0`. -/
example : cellIncrement u₀ (cellVector (((0 : Fin 2), (0 : Fin 1)), (1 : Fin 2))) 0 0 = 3 / 4 := by
  simp [cellIncrement, cellRatio, u₀, cellVector]
  norm_num

/-- The increment of that subject at grid index `1`, where it is neither at risk nor failing,
is `0`. -/
example : cellIncrement u₀ (cellVector (((0 : Fin 2), (0 : Fin 1)), (1 : Fin 2))) 1 0 = 0 := by
  simp [cellIncrement, cellRatio, u₀, cellVector]

/-- The survival before the first grid index is the empty product `1`. -/
example (u : EuclideanSpace ℝ (Cell 3 2)) : survivalBefore u 0 = 1 := by
  simp [survivalBefore]

/-- The cumulative incidence at the first grid index is the first ratio. -/
example (u : EuclideanSpace ℝ (Cell 3 2)) (c : Fin 2) :
    cumIncidence u c 0 = cellRatio u 0 c := by
  have h : univ.filter (· ≤ (0 : Fin 3)) = {0} := by decide
  rw [cumIncidence, h, sum_singleton]
  simp [survivalBefore]

/-- Boundary: the Kaplan–Meier coefficient beyond `j` vanishes (from the definition). -/
example (u : EuclideanSpace ℝ (Cell 3 2)) : kmCoeff u 0 2 = 0 := by
  simp [kmCoeff]

/-- On a one-point grid the Kaplan–Meier coefficient is `-1 / u_0` (empty product). -/
example (u : EuclideanSpace ℝ (Cell 1 2)) : kmCoeff u 0 0 = -1 / u (Sum.inr 0) := by
  simp [kmCoeff]

/-- Boundary: the Aalen–Johansen coefficient beyond `j` vanishes (from the definition). -/
example (u : EuclideanSpace ℝ (Cell 3 2)) (c c' : Fin 2) : ajCoeff u 0 c 2 c' = 0 := by
  have h : univ.filter (fun l' : Fin 3 => l' ≤ 0 ∧ 2 < l') = ∅ := by decide
  rw [ajCoeff, h]
  simp

/-- The Kaplan–Meier coordinate of the influence coefficients is `kmCoeff`, constant in the
cause. -/
example (u : EuclideanSpace ℝ (Cell 3 2)) (j : {j : Fin 3 // j ≤ 2}) (l : Fin 3) (c : Fin 2) :
    influenceCoeff u 2 (none, j) l c = kmCoeff u j.1 l := rfl

/-- One grid index and one cause: the Gram form is the binomial `γγ' (e - e² / y)`. -/
example (u : EuclideanSpace ℝ (Cell 1 1)) (γ γ' : Fin 1 → Fin 1 → ℝ) :
    incrementCov u γ γ' = γ 0 0 * γ' 0 0 * u (Sum.inl (0, 0)) -
      γ 0 0 * u (Sum.inl (0, 0)) * (γ' 0 0 * u (Sum.inl (0, 0))) / u (Sum.inr 0) := by
  simp [incrementCov]

/-- Boundary: with no causes the Gram form vanishes. -/
example (u : EuclideanSpace ℝ (Cell 3 0)) (γ γ' : Fin 3 → Fin 0 → ℝ) :
    incrementCov u γ γ' = 0 := by
  simp [incrementCov]

/-! ### A concrete law: `T` uniform on `{0, 1}`, one cause, censoring at `1` -/

/-- `(T, J)` uniform on `{0, 1} × {0}`. -/
private noncomputable def pTJ : PMF (Fin 2 × Fin 1) :=
  PMF.ofFintype (fun _ => 2⁻¹) (by
    rw [sum_const, card_univ]
    simp only [Fintype.card_prod, Fintype.card_fin, mul_one, nsmul_eq_mul, Nat.cast_ofNat]
    exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top)

/-- Censoring at the last grid index. -/
private noncomputable def pC : PMF (Fin 2) := PMF.pure 1

private noncomputable def μ₁ : Measure ((Fin 2 × Fin 1) × Fin 2) := indepCauseLaw pTJ pC

private instance : IsProbabilityMeasure μ₁ := isProbabilityMeasure_indepCauseLaw pTJ pC

private lemma survivalMass_pC_zero : survivalMass pC 0 = 1 := by
  simp [survivalMass, pC, PMF.toMeasure_pure]

/-- The event mass at `0` is `P(T = 0) P(C ≥ 0) = 1/2`, computed from the definitions. -/
private lemma cellMean_inl : cellMean μ₁ (Sum.inl (0, 0)) = 1 / 2 := by
  change causeEventMass (indepCauseLaw pTJ pC) 0 0 = 1 / 2
  rw [causeEventMass_indepCauseLaw, survivalMass_pC_zero]
  simp [pTJ, PMF.ofFintype_apply]

/-- The at-risk mass at `0` is `1`, computed from the definitions. -/
private lemma cellMean_inr : cellMean μ₁ (Sum.inr 0) = 1 := by
  change causeAtRiskMass (indepCauseLaw pTJ pC) 0 = 1
  have hs : {ω : (Fin 2 × Fin 1) × Fin 2 | (0 : Fin 2) ≤ min ω.1.1 ω.2} = Set.univ :=
    Set.eq_univ_of_forall fun ω => Fin.zero_le _
  rw [causeAtRiskMass, hs, probReal_univ]

private lemma hm₁ : causeAtRiskMass μ₁ 0 ≠ 0 := by
  change cellMean μ₁ (Sum.inr 0) ≠ 0
  rw [cellMean_inr]
  norm_num

/-- Non-vacuity of the Greenwood hypothesis: `d_0 = 1/2 ≠ 1 = y_0`. -/
private lemma hd₁ : ∀ l : Fin 2, l ≤ (0 : Fin 2) → l ≤ (0 : Fin 2) →
    ∑ c, cellMean μ₁ (Sum.inl (l, c)) ≠ cellMean μ₁ (Sum.inr l) := by
  intro l hl _
  have : l = 0 := le_antisymm hl (Fin.zero_le _)
  subst this
  rw [Fin.sum_univ_one, cellMean_inl, cellMean_inr]
  norm_num

private lemma filter_zero : univ.filter (fun l : Fin 2 => l ≤ 0 ∧ l ≤ 0) = {0} := by decide

/-- The Kaplan–Meier survival at `0` of the mean cell vector is `1 - 1/2 = 1/2`. -/
private lemma ajMap_none_zero : ajMap (0 : Fin 2) (cellMean μ₁) (none, ⟨0, le_rfl⟩) = 1 / 2 := by
  have h : univ.filter (· ≤ (0 : Fin 2)) = {0} := by decide
  rw [ajMap_none_eq]
  simp only [h, prod_singleton, factor, Fin.sum_univ_one, cellMean_inl, cellMean_inr]
  norm_num

/-- **Greenwood on a binomial example.** `Ŝ(0)` is one minus a binomial proportion with success
probability `1/2`, so its asymptotic variance is `p (1 - p) = 1/4`; Greenwood's closed form
`S(0)² d_0 / (y_0 (y_0 - d_0)) = (1/4) (1/2) / (1/2)` gives the same. -/
example : cov[fun w => influence μ₁ 0 w (none, ⟨0, le_rfl⟩),
    fun w => influence μ₁ 0 w (none, ⟨0, le_rfl⟩); μ₁] = 1 / 4 := by
  rw [covariance_influence_km 0 hm₁ ⟨0, le_rfl⟩ ⟨0, le_rfl⟩ hd₁, filter_zero, sum_singleton,
    ajMap_none_zero, Fin.sum_univ_one, cellMean_inl, cellMean_inr]
  norm_num

/-- With one cause `F_0(0) = 1 - S(0)`, so the Aalen–Johansen variance is the same `1/4`:
`S(0-)² (e_0 y_0 - e_0²) / y_0³ = 1/2 - 1/4`. -/
example : cov[fun w => influence μ₁ 0 w (some 0, ⟨0, le_rfl⟩),
    fun w => influence μ₁ 0 w (some 0, ⟨0, le_rfl⟩); μ₁] = 1 / 4 := by
  rw [covariance_influence_aj 0 hm₁ 0 0 ⟨0, le_rfl⟩ ⟨0, le_rfl⟩ hd₁, filter_zero, sum_singleton]
  simp only [sub_self, zero_mul, zero_div, ite_true, cellMean_inl, cellMean_inr, survivalBefore]
  have h : univ.filter (· < (0 : Fin 2)) = ∅ := by decide
  simp only [h, prod_empty]
  norm_num

/-- With one cause `F_0(0) = 1 - S(0)`, so the cross covariance is `-Var = -1/4`:
`S(0) (0 - S(0-) e_0 / y_0²) = (1/2) (-1/2)`. -/
example : cov[fun w => influence μ₁ 0 w (none, ⟨0, le_rfl⟩),
    fun w => influence μ₁ 0 w (some 0, ⟨0, le_rfl⟩); μ₁] = -1 / 4 := by
  rw [covariance_influence_km_aj 0 hm₁ 0 ⟨0, le_rfl⟩ ⟨0, le_rfl⟩ hd₁, filter_zero, sum_singleton,
    ajMap_none_zero]
  simp only [sub_self, zero_mul, zero_div, zero_sub, cellMean_inl, cellMean_inr, survivalBefore]
  have h : univ.filter (· < (0 : Fin 2)) = ∅ := by decide
  simp only [h, prod_empty]
  norm_num

/-- The general closed form agrees with the Greenwood entry on this law: the Gram form of the
Kaplan–Meier coefficients at `0` is `1/4`, computed from the definitions of `incrementCov` and
`kmCoeff`. -/
example : incrementCov (cellMean μ₁) (influenceCoeff (cellMean μ₁) 0 (none, ⟨0, le_rfl⟩))
    (influenceCoeff (cellMean μ₁) 0 (none, ⟨0, le_rfl⟩)) = 1 / 4 := by
  have h : (univ.filter (· ≤ (0 : Fin 2))).erase 0 = ∅ := by decide
  have h1 : ¬ (1 : Fin 2) ≤ 0 := by decide
  simp only [incrementCov, Fin.sum_univ_two, Fin.sum_univ_one, influenceCoeff, kmCoeff, h,
    prod_empty, le_refl, ite_true, h1, ite_false, cellMean_inl, cellMean_inr]
  norm_num

/-! ### The Gaussian limit on the canonical sequence space -/

private lemma hasLaw_eval (i : ℕ) :
    HasLaw (fun ω : ℕ → (Fin 2 × Fin 1) × Fin 2 => ω i) μ₁ (Measure.infinitePi fun _ : ℕ => μ₁) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => μ₁) i).hasLaw

private lemma iIndep_eval :
    iIndepFun (fun i (ω : ℕ → (Fin 2 × Fin 1) × Fin 2) => ω i)
      (Measure.infinitePi fun _ : ℕ => μ₁) :=
  iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id

/-- Non-vacuity of the limit form: the Gaussian limit of the merged joint CLT for i.i.d.
subjects with law `μ₁` has Kaplan–Meier variance `1/4` at grid index `0`, by Greenwood. -/
example : ∃ Y : EuclideanSpace ℝ (Cell 2 1) → Coord 2 1 (0 : Fin 2) → ℝ,
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) •
        (estimator 0 (empiricalCauseData (fun i ω => ω i) n ω) - ajMap 0 (cellMean μ₁)))
      atTop Y (fun _ => Measure.infinitePi fun _ : ℕ => μ₁)
      (stdGaussian (EuclideanSpace ℝ (Cell 2 1))) ∧
    cov[fun z => Y z (none, ⟨0, le_rfl⟩), fun z => Y z (none, ⟨0, le_rfl⟩);
      stdGaussian (EuclideanSpace ℝ (Cell 2 1))] = 1 / 4 := by
  obtain ⟨Y, -, hY, hconv⟩ := tendstoInDistribution_estimator iIndep_eval hasLaw_eval 0 hm₁
  refine ⟨Y, hconv, ?_⟩
  rw [covariance_limit_km (W := fun i (ω : ℕ → (Fin 2 × Fin 1) × Fin 2) => ω i) (hasLaw_eval 0)
    0 hm₁ hY ⟨0, le_rfl⟩ ⟨0, le_rfl⟩ hd₁, filter_zero, sum_singleton, ajMap_none_zero,
    Fin.sum_univ_one, cellMean_inl, cellMean_inr]
  norm_num

end MathlibExtTest.Probability.Statistics.AalenJohansenClosedForm
