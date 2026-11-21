/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.GeneralizationBounds.SGDStability
import Mathlib.Analysis.Calculus.Deriv.Mul

open MeasureTheory

namespace CSLibExt.MachineLearning.GeneralizationBounds

-- Growth recursion for two identity updates (`η = 1`, `σ = 0`).
example (v w : ℝ) : ‖id v - id w‖ ≤ min 1 1 * ‖v - w‖ + 2 * 0 :=
  norm_sub_le_min_mul_add_two_mul (fun v w => by simp) (fun w => by simp) (fun w => by simp) v w

-- With zero steps, SGM never moves.
example (S : Fin 3 → Bool) (ι : ℕ → Fin 3) (t : ℕ) :
    sgmIterate (fun (w : ℝ) (z : Bool) => if z then w else -w) (fun _ => 0) 5 S ι t = 5 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [sgmIterate, ih]

/-- The signed linear loss `ℓ(w, z) = ± w`. -/
private noncomputable def signedLoss (w : ℝ) (z : Bool) : ℝ := if z then w else -w

private theorem signedLoss_false : (fun w => signedLoss w false) = -id := by
  funext w; simp [signedLoss]

private theorem signedLoss_true : (fun w => signedLoss w true) = id := by
  funext w; simp [signedLoss]

private theorem gradient_signedLoss (z : Bool) :
    gradient (fun w => signedLoss w z) = fun _ => if z then 1 else -1 := by
  funext w
  cases z
  · rw [signedLoss_false]
    simpa using ((hasDerivAt_id w).neg).hasGradientAt.gradient
  · rw [signedLoss_true]
    simpa using (hasDerivAt_id w).hasGradientAt.gradient

-- Theorem 3.8 applies to the signed linear loss (convex, `1`-smooth, `1`-Lipschitz) with unit
-- steps: `E |ℓ(w_T, z) - ℓ(w'_T, z)| ≤ (2 / n) T`.
example (T : ℕ) (S : Fin 4 → Bool) (k : Fin 4) (z' z : Bool) :
    ∫ κ, |signedLoss (sgmOutput signedLoss (fun _ => 1) 0 S T κ) z -
        signedLoss (sgmOutput signedLoss (fun _ => 1) 0 (Function.update S k z') T κ) z|
        ∂(indexMeasure 4 T) ≤
      2 * ((1 : NNReal) : ℝ) ^ 2 / (4 : ℕ) * ∑ t ∈ Finset.range T, (fun _ => (1 : ℝ)) t := by
  refine integral_abs_sgmOutput_sub_le one_pos (fun z => ?_) (fun z => ?_) (fun z => ?_)
    (fun z => ?_) (fun _ => zero_le_one) (fun _ => by norm_num) 0 T S k z' z
  · cases z
    · rw [signedLoss_false]; exact (concaveOn_id convex_univ).neg
    · rw [signedLoss_true]; exact convexOn_id convex_univ
  · cases z
    · rw [signedLoss_false]; exact differentiable_id.neg
    · rw [signedLoss_true]; exact differentiable_id
  · rw [gradient_signedLoss]; exact (LipschitzWith.const _).weaken (zero_le)
  · cases z
    · rw [signedLoss_false]; exact LipschitzWith.id.neg
    · rw [signedLoss_true]; exact LipschitzWith.id

-- The generalization bound for SGM applies to the signed linear loss, which is not constant in `w`
-- and vanishes at the start `w₀ = 0`: for every law `ν` of the labels, the expected gap of four
-- unit steps on four examples is at most `(2 / 4) · 4 = 2`.
example (ν : Measure Bool) [IsProbabilityMeasure ν] :
    |∫ S, (empiricalRisk (fun (S : Fin 4 → Bool) z => ∫ κ,
          signedLoss (sgmOutput signedLoss (fun _ => 1) 0 S 4 κ) z ∂(indexMeasure 4 4)) S S -
        risk (fun (S : Fin 4 → Bool) z => ∫ κ,
          signedLoss (sgmOutput signedLoss (fun _ => 1) 0 S 4 κ) z ∂(indexMeasure 4 4)) ν S)
        ∂(Measure.pi fun _ : Fin 4 => ν)| ≤
      2 * ((1 : NNReal) : ℝ) ^ 2 / (4 : ℕ) * ∑ t ∈ Finset.range 4, (fun _ => (1 : ℝ)) t := by
  refine abs_integral_empiricalRisk_sub_risk_sgm_le one_pos (fun z => ?_) (fun z => ?_)
    (fun z => ?_) (fun z => ?_) (fun _ => zero_le_one) (fun _ => by norm_num) 0 4 (M := 0)
    (fun z => by cases z <;> simp [signedLoss]) (fun κ => Measurable.of_discrete)
  · cases z
    · rw [signedLoss_false]; exact (concaveOn_id convex_univ).neg
    · rw [signedLoss_true]; exact convexOn_id convex_univ
  · cases z
    · rw [signedLoss_false]; exact differentiable_id.neg
    · rw [signedLoss_true]; exact differentiable_id
  · rw [gradient_signedLoss]; exact (LipschitzWith.const _).weaken zero_le
  · cases z
    · rw [signedLoss_false]; exact LipschitzWith.id.neg
    · rw [signedLoss_true]; exact LipschitzWith.id

/-! The index law needs a nonempty sample: for `n = 0` and `T = 1` there is no index sequence
and the product measure would have mass `0`, so it does not elaborate. -/

/--
error: failed to synthesize instance of type class
  NeZero 0

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
noncomputable example : MeasureTheory.Measure (Fin 1 → Fin 0) := indexMeasure 0 1

end CSLibExt.MachineLearning.GeneralizationBounds
