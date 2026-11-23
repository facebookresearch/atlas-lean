/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.StoreyPRDS
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Tests for Storey-BH under PRDS

* a model with two identical valid null p-values (perfect positive dependence, PRDS) on which the
  FDR of Storey-BH at `q = 1/5`, `lam = 2/5` is computed from the definitions:
  `FDR = 6/25 > 1/5 = q`, so the level-`q` guarantee of the independent case fails under PRDS,
  and `6/25 = q (1 - lam) |H0|`, so the PRDS bound is attained;
* the PRDS theorem applies to that model (non-vacuity) and to independent p-values;
* concrete checks of the monotonicity lemma.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics
open MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.Adaptive.StoreyPRDS

/-! ### Evaluation helpers for two p-values -/

theorem numBelow_two (v : Fin 2 → ℝ) (t : ℝ) :
    numBelow v t = (if v 0 ≤ t then 1 else 0) + (if v 1 ≤ t then 1 else 0) := by
  rw [numBelow, Finset.card_filter, Fin.sum_univ_two]

theorem numAbove_two (v : Fin 2 → ℝ) (lam : ℝ) :
    (Finset.univ.filter fun j => lam < v j).card =
      (if lam < v 0 then 1 else 0) + (if lam < v 1 then 1 else 0) := by
  rw [Finset.card_filter, Fin.sum_univ_two]

/-! ### The comonotone model

`Ω = Bool`. With probability `6/25` both p-values equal `6/25`, otherwise both equal `1`. Each is
a valid p-value (`P(p ≤ t) ≤ t`), both hypotheses are true nulls, and the vector is a
nondecreasing function of either coordinate, hence PRDS. -/

/-- Point masses. -/
noncomputable def r : Bool → ℝ := fun b => if b then 6 / 25 else 19 / 25

theorem r_nonneg (b : Bool) : 0 ≤ r b := by cases b <;> norm_num [r]

theorem sum_ofReal_r : ∑ b, ENNReal.ofReal (r b) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg fun b _ => r_nonneg b, Fintype.sum_bool]
  norm_num [r]

/-- The law of the coin. -/
noncomputable def μ : Measure Bool :=
  (PMF.ofFintype (fun b => ENNReal.ofReal (r b)) sum_ofReal_r).toMeasure

instance : IsProbabilityMeasure μ := by unfold μ; infer_instance

/-- Two identical p-values. -/
noncomputable def P : Fin 2 → Bool → ℝ := fun _ ω => if ω then 6 / 25 else 1

theorem μ_apply (S : Set Bool) : μ S = ENNReal.ofReal (∑ b, S.indicator r b) := by
  rw [μ, PMF.toMeasure_apply_fintype, ENNReal.ofReal_sum_of_nonneg fun b _ => by
    by_cases h : b ∈ S <;> simp [h, r_nonneg]]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : b ∈ S <;> simp [h]

theorem μ_real_singleton (b : Bool) : μ.real {b} = r b := by
  rw [measureReal_def, μ_apply, ENNReal.toReal_ofReal (Finset.sum_nonneg fun x _ => by
    by_cases h : x ∈ ({b} : Set Bool) <;> simp [h, r_nonneg])]
  simp [Set.indicator_apply]

theorem measurable_P (i : Fin 2) : Measurable (P i) := measurable_of_countable _

/-- Both p-values are valid. -/
theorem isValidPValue_P (i : Fin 2) : IsValidPValue μ (P i) := by
  intro t ht
  rw [μ_apply]
  apply ENNReal.ofReal_le_ofReal
  obtain ⟨ht0, ht1⟩ := ht
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Fintype.sum_bool, P, ite_true,
    Bool.false_eq_true, ite_false]
  split_ifs with h1 h2 h2 <;> norm_num [r] at * <;> linarith

/-- The vector is PRDS on both nulls: it is the nondecreasing map `u ↦ (u, u)` of either
coordinate (`isPRDSOn_of_monotone_comp`). -/
theorem isPRDSOn_P : IsPRDSOn μ P Finset.univ :=
  isPRDSOn_of_monotone_comp μ P measurable_P _ fun _ _ =>
    ⟨fun u _ => u, fun _ _ h _ => h, fun _ => rfl⟩

/-! ### Storey-BH on the two outcomes, from the definitions -/

/-- On the small outcome no p-value exceeds `lam = 2/5`, so `π̂₀ = 1 / ((3/5) · 2) = 5/6`. -/
theorem storeyPi0Plus1_small : storeyPi0Plus1 (2 / 5) (fun i => P i true) = 5 / 6 := by
  rw [storeyPi0Plus1, numAbove_two]; norm_num [P]

/-- The second threshold is `min (2/5) ((1/5) / (5/6) · 2 / 2) = 6/25`. -/
theorem storeyThreshold_small :
    storeyThreshold (1 / 5) (2 / 5) (fun i => P i true) 2 = 6 / 25 := by
  rw [storeyThreshold, storeyPi0Plus1_small, min_eq_right (by norm_num)]
  norm_num

/-- Both p-values `6/25` are at most the second threshold, so Storey-BH rejects both. -/
theorem storeyBHIndex_small : storeyBHIndex (1 / 5) (2 / 5) (fun i => P i true) = 2 := by
  refine le_antisymm (storeyBHIndex_le _ _ _) (le_storeyBHIndex le_rfl ?_)
  rw [storeyThreshold_small, numBelow_two]
  norm_num [P]

theorem storeyBHRejections_small :
    storeyBHRejections (1 / 5) (2 / 5) (fun i => P i true) = Finset.univ := by
  ext i
  rw [mem_storeyBHRejections, storeyBHIndex_small, storeyThreshold_small]
  simp [P]

/-- On the large outcome both p-values exceed `lam`, and Storey-BH rejects nothing. -/
theorem storeyBHRejections_large :
    storeyBHRejections (1 / 5) (2 / 5) (fun i => P i false) = ∅ :=
  Finset.eq_empty_of_forall_notMem fun i hi =>
    absurd (le_of_mem_storeyBHRejections hi) (by norm_num [P])

theorem fdp_small : falseDiscoveryProportion Finset.univ
    (storeyBHRejections (1 / 5) (2 / 5) fun i => P i true) = 1 := by
  rw [storeyBHRejections_small, falseDiscoveryProportion]
  norm_num

theorem fdp_large : falseDiscoveryProportion Finset.univ
    (storeyBHRejections (1 / 5) (2 / 5) fun i => P i false) = 0 := by
  rw [storeyBHRejections_large, falseDiscoveryProportion]
  simp

/-- **The FDR of Storey-BH in the comonotone model**, computed from the definitions:
`6/25 · 1 + 19/25 · 0 = 6/25`. -/
theorem fdr_storeyBH_P :
    ∫ ω, falseDiscoveryProportion Finset.univ
      (storeyBHRejections (1 / 5) (2 / 5) fun i => P i ω) ∂μ = 6 / 25 := by
  rw [integral_fintype Integrable.of_finite, Fintype.sum_bool, μ_real_singleton,
    μ_real_singleton, smul_eq_mul, smul_eq_mul, fdp_small, fdp_large]
  norm_num [r]

/-- **Storey-BH does not control the FDR at `q` under PRDS.** In a PRDS model with valid null
p-values, Storey-BH at `q = 1/5`, `lam = 2/5` has `FDR = 6/25 > q`. -/
theorem not_fdr_storeyBH_le_q_of_isPRDSOn :
    IsPRDSOn μ P Finset.univ ∧ (∀ i, IsValidPValue μ (P i)) ∧
      ¬ (∫ ω, falseDiscoveryProportion Finset.univ
        (storeyBHRejections (1 / 5) (2 / 5) fun i => P i ω) ∂μ ≤ 1 / 5) := by
  refine ⟨isPRDSOn_P, isValidPValue_P, ?_⟩
  rw [fdr_storeyBH_P]
  norm_num

/-- **The PRDS bound is attained**: the FDR in the model equals `q (1 - lam) |H0| = 6/25`. -/
theorem fdr_storeyBH_P_eq_bound :
    ∫ ω, falseDiscoveryProportion Finset.univ
      (storeyBHRejections (1 / 5) (2 / 5) fun i => P i ω) ∂μ =
      1 / 5 * (1 - 2 / 5) * (Finset.univ : Finset (Fin 2)).card := by
  rw [fdr_storeyBH_P]
  norm_num

/-- Non-vacuity: the PRDS theorem applies to the comonotone model. -/
example : ∫ ω, falseDiscoveryProportion Finset.univ
      (storeyBHRejections (1 / 5) (2 / 5) fun i => P i ω) ∂μ ≤
      1 / 5 * (1 - 2 / 5) * (Finset.univ : Finset (Fin 2)).card :=
  integral_falseDiscoveryProportion_storeyBHRejections_le_of_isPRDSOn μ P measurable_P _
    isPRDSOn_P (fun i _ => isValidPValue_P i) (by norm_num) (by norm_num)

/-- Independent p-values are PRDS (`isPRDSOn_of_iIndepFun`), so the PRDS theorem also applies to
them, with the weaker bound `q (1 - lam) |H0|` in place of the independent-case bound `q`. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ' : Measure Ω) [IsProbabilityMeasure μ']
    (p : Fin 3 → Ω → ℝ) (hp : ∀ i, Measurable (p i)) (hindep : iIndepFun p μ')
    (hnull : ∀ i, IsValidPValue μ' (p i)) :
    ∫ ω, falseDiscoveryProportion Finset.univ (storeyBHRejections (1 / 10) (1 / 2)
      fun i => p i ω) ∂μ' ≤ 1 / 10 * (1 - 1 / 2) * (Finset.univ : Finset (Fin 3)).card :=
  integral_falseDiscoveryProportion_storeyBHRejections_le_of_isPRDSOn μ' p hp _
    (isPRDSOn_of_iIndepFun μ' p hp hindep _) (fun i _ => hnull i) (by norm_num) (by norm_num)

/-! ### Monotonicity on concrete vectors -/

/-- Raising the second p-value from `6/25` to `1` raises `π̂₀(2/5)` from `5/6` to `5/3`. -/
example : storeyPi0Plus1 (2 / 5) (![6 / 25, 1] : Fin 2 → ℝ) = 5 / 3 := by
  rw [storeyPi0Plus1, numAbove_two]; norm_num

/-- Raising both p-values from `6/25` to `1` lowers the number of rejections from `2` to `0`,
as `storeyBHIndex_antitone` predicts. -/
example : storeyBHIndex (1 / 5) (2 / 5) (fun i => P i false) = 0 ∧
    storeyBHIndex (1 / 5) (2 / 5) (fun i => P i true) = 2 := by
  refine ⟨?_, storeyBHIndex_small⟩
  rw [← card_storeyBHRejections (by norm_num) (by norm_num), storeyBHRejections_large]
  rfl

example : storeyBHIndex (1 / 5) (2 / 5) (fun i => P i false) ≤
    storeyBHIndex (1 / 5) (2 / 5) (fun i => P i true) :=
  storeyBHIndex_antitone (by norm_num) (by norm_num) fun i => by norm_num [P]

end MathlibExtTest.Probability.Statistics.MultipleTesting.Adaptive.StoreyPRDS
