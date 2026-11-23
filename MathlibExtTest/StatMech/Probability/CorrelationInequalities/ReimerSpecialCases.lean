/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerSpecialCases

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerSpecialCases`

* `evXor`, `evXnor` computed at configurations of `ConfigSpace (Fin 2)`;
* `reimer_xor_xnor_inequality` at `p = 1/2` (no other hypotheses), and
  `reimer_inequality_of_inter_empty` for `evXor, evXnor` using `evXor_inter_evXnor`;
* `NegativelyCorrelated` proved for `evXor, evXnor` and fed to `reimer_wprob_of_negCorr`;
* the slice inequalities for increasing events, `slice_disjointOccurrence_le_of_isIncreasing`, at `n
  = 1`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerSpecialCases

open _root_.StatMech

/-- The event "coordinate `0` is open" on `Fin 2`, used for the slice step. -/
def open0 : Set (ConfigSpace (Fin (1 + 1))) := {ω | ω 0 = true}

-- `open0` is increasing.
theorem isIncreasing_open0 : IsIncreasing open0 := by
  intro x y hxy hx
  have h := hxy 0
  simp only [open0, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

/-- The uniform coordinate weight on `Fin 2`. -/
noncomputable def half : Fin 2 → Bool → ℝ := fun _ _ => 1 / 2

-- `(1, 0) ∈ evXor` and `(1, 1) ∈ evXnor`.
example : ![true, false] ∈ evXor ∧ ![true, true] ∈ evXnor := by
  simp [evXor, evXnor]

-- `(1, 1) ∉ evXor`.
example : ![true, true] ∉ evXor := by simp [evXor]

-- `evXor` is neither increasing nor decreasing.
example : ¬ IsIncreasing evXor ∧ ¬ IsDecreasing evXor :=
  ⟨not_isIncreasing_evXor, not_isDecreasing_evXor⟩

-- `reimer_xor_xnor_inequality` at `p = 1/2`.
example : (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real
      (disjointOccurrence evXor evXnor)
    ≤ (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real evXor
      * (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real evXnor :=
  reimer_xor_xnor_inequality _

-- `reimer_inequality_of_inter_empty` with its hypothesis discharged by `evXor_inter_evXnor`.
example : (bernoulliProductMeasure (E := Fin 2) 1 le_rfl).real (disjointOccurrence evXor evXnor)
    ≤ (bernoulliProductMeasure (E := Fin 2) 1 le_rfl).real evXor
      * (bernoulliProductMeasure (E := Fin 2) 1 le_rfl).real evXnor :=
  reimer_inequality_of_inter_empty _ evXor_inter_evXnor

-- `NegativelyCorrelated` holds for the disjoint events `evXor, evXnor`.
theorem negCorr_xor_xnor : NegativelyCorrelated half evXor evXnor := by
  unfold NegativelyCorrelated
  rw [evXor_inter_evXnor]
  have h0 : wprob half ∅ = 0 := by simp [wprob]
  rw [h0]
  exact mul_nonneg (wprob_nonneg (fun _ _ => by norm_num [half]) _)
    (wprob_nonneg (fun _ _ => by norm_num [half]) _)

-- `reimer_wprob_of_negCorr` from that instance.
example : wprob half (disjointOccurrence evXor evXnor) ≤ wprob half evXor * wprob half evXnor :=
  reimer_wprob_of_negCorr (fun _ _ => by norm_num [half]) negCorr_xor_xnor

-- The slice inequalities hold for increasing events (here `n = 1`, `A = B = open0`).
example : wprob (fun (_ : Fin 1) (_ : Bool) => (1 / 2 : ℝ))
      (disjointOccurrence (slice open0 false) (slice open0 false))
    ≤ wprob (fun (_ : Fin 1) (_ : Bool) => (1 / 2 : ℝ))
      (disjointOccurrence (slice open0 false) (slice open0 true)
        ∩ disjointOccurrence (slice open0 true) (slice open0 false)) :=
  (slice_disjointOccurrence_le_of_isIncreasing 1 _ (fun _ _ => by norm_num) (fun _ => by norm_num)
    open0 open0 isIncreasing_open0 isIncreasing_open0).1

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerSpecialCases
