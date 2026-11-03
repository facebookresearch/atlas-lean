/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.KingmanSigned.MaximalErgodic

/-!
# Tests for `MathlibExt.Dynamics.Ergodic.KingmanSigned.MaximalErgodic`

* `StatMech.GarsiaMax.maxPartialSum`: computed for the identity map and the constant `1`
  (`max_{1 ≤ n ≤ 2} S_n 1 = 2`).
* `StatMech.GarsiaMax.garsia_maximal_inequality`: instantiated for the identity map on an
  arbitrary measure space, and for `f = 1` on a probability space, where it gives a positive
  lower bound.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Dynamics.Ergodic.KingmanSigned.MaximalErgodic

open MeasureTheory
open _root_.StatMech _root_.StatMech.GarsiaMax

variable {α : Type*}

/-- `max_{1 ≤ n ≤ 2} S_n 1 = 2` for the identity map. -/
example (y : α) : maxPartialSum id (fun _ => (1 : ℝ)) 2 (by norm_num) y = 2 := by
  apply le_antisymm
  · obtain ⟨n, -, hn2, heq⟩ :=
      exists_eq_maxPartialSum (T := id) (f := fun _ => (1 : ℝ)) (by norm_num : 1 ≤ 2) y
    rw [← heq]
    simpa [birkhoffSum] using (Nat.cast_le (α := ℝ)).2 hn2
  · have := birkhoffSum_le_maxPartialSum (T := id) (f := fun _ => (1 : ℝ))
      (by norm_num : 1 ≤ 2) (n := 2) (by norm_num) le_rfl y
    simpa [birkhoffSum, Finset.sum_range_succ, one_add_one_eq_two] using this

variable [MeasurableSpace α]

/-- Garsia's inequality for the identity map. -/
example (μ : Measure α) (f : α → ℝ) (hf : Integrable f μ) (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ ∫ x in {x | 0 < maxPartialSum id f N hN x}, f x ∂μ :=
  garsia_maximal_inequality (MeasurePreserving.id μ) hf hN

/-- For `f = 1` on a probability space the maximal set is everything and the bound is `0 ≤ 1`. -/
example (μ : Measure α) [IsProbabilityMeasure μ] :
    0 ≤ ∫ _ in {x | 0 < maxPartialSum id (fun _ => (1 : ℝ)) 1 le_rfl x}, (1 : ℝ) ∂μ :=
  garsia_maximal_inequality (MeasurePreserving.id μ) (integrable_const 1) le_rfl

end MathlibExtTest.StatMech.Dynamics.Ergodic.KingmanSigned.MaximalErgodic
