/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Medoid
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for `L²`-medoids

* The sample `0, 1, 5` of reals with `d x y = |x - y|`: `1` is its unique `L²`-medoid, with mean
  squared distance `17 / 3`.
* A repeated sample point is still one point of the medoid set.
* The empty sample has no `L²`-medoid.
-/

@[expose] public section

open Finset MathlibExt.Probability.Statistics.Medoid

namespace MathlibExtTest.Probability.Statistics.Medoid

/-- `1` is an `L²`-medoid of the sample `0, 1, 5` for the distance `|x - y|`. -/
example : (1 : ℝ) ∈ l2MedoidSet (fun x y : ℝ => |x - y|) ![0, 1, 5] := by
  refine ⟨⟨1, rfl⟩, fun k => ?_⟩
  fin_cases k <;> norm_num [Fin.sum_univ_three]

/-- `0` is not an `L²`-medoid of that sample: its sum of squared distances is `26`, against `17`
for `1`. -/
example : (0 : ℝ) ∉ l2MedoidSet (fun x y : ℝ => |x - y|) ![0, 1, 5] := by
  rintro ⟨-, h⟩
  have := h 1
  norm_num [Fin.sum_univ_three] at this

/-- The mean squared distance from the medoid `1` to the sample `0, 1, 5` is `17 / 3`. -/
example : meanSquaredDistance (fun x y : ℝ => |x - y|) ![0, 1, 5] 1 = 17 / 3 := by
  norm_num [meanSquaredDistance, Fin.sum_univ_three]

/-- With a repeated point, the medoid set of `2, 2, 7` contains `2`. -/
example : (2 : ℝ) ∈ l2MedoidSet (fun x y : ℝ => |x - y|) ![2, 2, 7] := by
  refine ⟨⟨0, rfl⟩, fun k => ?_⟩
  fin_cases k <;> norm_num [Fin.sum_univ_three]

/-- The empty sample has no `L²`-medoid, so the hypothesis `0 < s` of `l2MedoidSet_nonempty` is
needed. -/
example (d : ℝ → ℝ → ℝ) (T : Fin 0 → ℝ) : l2MedoidSet d T = ∅ := by
  ext x
  simp only [l2MedoidSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨k, -⟩
  exact k.elim0

/-- A nonempty sample has an `L²`-medoid, whatever the distance. -/
example (d : ℕ → ℕ → ℝ) : (l2MedoidSet d ![3, 1, 4, 1, 5]).Nonempty :=
  l2MedoidSet_nonempty d _ (by norm_num)

end MathlibExtTest.Probability.Statistics.Medoid
