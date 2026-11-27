/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.GeneralizationBounds.DeletionStability

open MeasureTheory Real
open CSLibExt.MachineLearning.GeneralizationBounds

namespace CSLibExtTest.DeletionStability

-- Both fits ignore their inputs, but the loss jumps by one between sizes.
example :
    let L := fun (w : ℝ) (_ : Unit) => w
    let A := fun _ : Fin 1 → Unit => (1 : ℝ)
    let B := fun _ : Fin 0 → Unit => (0 : ℝ)
    IsUniformlyStable L A 0 ∧ IsUniformlyStable L B 0 ∧
      IsDeletionStable L A B 1 ∧ ¬IsDeletionStable L A B 0 := by
  dsimp only
  refine ⟨fun _ _ _ _ => by norm_num, fun _ _ _ _ => by norm_num,
    fun _ _ _ => by norm_num, fun h => ?_⟩
  have bad := h (fun _ => ()) 0 ()
  norm_num at bad

-- At m = 1 the test observation is passed to the loss, not to the learner.
example {Z H : Type*} (L : H → Z → ℝ) (B : (Fin 0 → Z) → H) (S : Fin 1 → Z) :
    leaveOneOutRisk L B S = L (B Fin.elim0) (S 0) := by
  simp [leaveOneOutRisk, Subsingleton.elim (Fin.removeNth 0 S) (Fin.elim0 : Fin 0 → Z)]

private def bit (z : Bool) : ℝ := if z then 1 else 0
private noncomputable def loss (w : ℝ) (z : Bool) := |w - bit z|
private noncomputable def pairFit (S : Fin 2 → Bool) := (bit (S 0) + bit (S 1)) / 2
private def singleFit (T : Fin 1 → Bool) := bit (T 0)

-- On two distinct bits, testing the singleton fit on its own bit would give zero.
-- The two held-out losses are both one, and the full-sample average loss is one half.
example :
    let S : Fin 2 → Bool := ![false, true]
    leaveOneOutRisk loss singleFit S = 1 ∧ empiricalRisk loss S (pairFit S) = 1 / 2 := by
  constructor
  · change (1 / 2 : ℝ) * (∑ i : Fin 2, loss (singleFit (i.removeNth ![false, true]))
        (![false, true] i)) = 1
    rw [Fin.sum_univ_two]
    change (1 / 2 : ℝ) * (|1 - 0| + |0 - 1|) = 1
    norm_num
  · norm_num [empiricalRisk, Fin.sum_univ_two, loss, pairFit, bit]

private lemma stablePair : IsDeletionStable loss pairFit singleFit (1 / 2) := by
  intro S i z
  fin_cases i <;> cases z <;> cases h₀ : S 0 <;> cases h₁ : S 1 <;>
    norm_num [loss, pairFit, singleFit, Fin.removeNth, Fin.succAbove, bit, h₀, h₁]

-- Instantiating both statements at m=2, β=1/2, M=1 gives the coefficient 5 and
-- the denominator 4; the offsets are 1 and 1/2. Each projection bounds its own event.
example (ν : Measure Bool) [IsProbabilityMeasure ν] {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1) :
    let t := 5 * √(log (1 / δ) / 4)
    let P := Measure.pi fun _ : Fin 2 => ν
    (1 - δ ≤ P.real {S | risk loss ν (pairFit S) ≤ empiricalRisk loss S (pairFit S) + 1 + t}) ∧
    (1 - δ ≤ P.real {S | risk loss ν (pairFit S) ≤ leaveOneOutRisk loss singleFit S + 1 / 2 + t}) := by
  have ha (S : Fin 2 → Bool) (z : Bool) : loss (pairFit S) z ∈ Set.Icc 0 1 := by
    cases z <;> cases h₀ : S 0 <;> cases h₁ : S 1 <;> norm_num [loss, pairFit, bit, h₀, h₁]
  have hb (T : Fin 1 → Bool) (z : Bool) : loss (singleFit T) z ∈ Set.Icc 0 1 := by
    cases z <;> cases h : T 0 <;> norm_num [loss, singleFit, bit, h]
  convert stablePair.highProbability_generalization ν (measurable_of_finite _)
    (measurable_of_finite _) ha hb hδ using 1
  norm_num

-- Both concentration width and offsets vanish; the theorem still applies at size one.
example {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) [IsProbabilityMeasure ν]
    (A : (Fin 1 → Z) → Unit) (B : (Fin 0 → Z) → Unit) {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1) :
    let L := fun (_ : Unit) (_ : Z) => (0 : ℝ)
    let P := Measure.pi fun _ : Fin 1 => ν
    (1 - δ ≤ P.real {S | risk L ν (A S) ≤ empiricalRisk L S (A S)}) ∧
    (1 - δ ≤ P.real {S | risk L ν (A S) ≤ leaveOneOutRisk L B S}) := by
  let L := fun (_ : Unit) (_ : Z) => (0 : ℝ)
  have hd : IsDeletionStable L A B 0 := fun _ _ _ => by simp [L]
  simpa only [mul_zero, zero_add, add_zero, zero_mul] using
    hd.highProbability_generalization ν measurable_const measurable_const (M := 0)
      (fun _ _ => ⟨le_rfl, le_rfl⟩) (fun _ _ => ⟨le_rfl, le_rfl⟩) hδ

end CSLibExtTest.DeletionStability
