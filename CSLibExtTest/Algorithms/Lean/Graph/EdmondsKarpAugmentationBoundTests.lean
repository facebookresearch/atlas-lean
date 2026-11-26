/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.EdmondsKarpAugmentationBound
import Mathlib.Tactic.NormNum

/-! Non-vacuity tests for the Edmonds–Karp augmentation bound. -/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.EdmondsKarpAugmentationBoundTests

open EdmondsKarp

private def onePathCapacity : Fin 3 → Fin 3 → ℕ
  | 0, 1 => 3
  | 1, 2 => 3
  | _, _ => 0

/-- The hypothesis of the bound holds with `m = 1`: the sink is reachable from the zero flow. -/
private theorem reachable_zero :
    (residualGraph onePathCapacity (zeroFlow 3)).Reachable 0 2 := by
  have e01 : (residualGraph onePathCapacity (zeroFlow 3)).Edge 0 1 := by
    rw [residualGraph_edge_iff]; decide
  have e12 : (residualGraph onePathCapacity (zeroFlow 3)).Edge 1 2 := by
    rw [residualGraph_edge_iff]; decide
  exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single e01) e12

example : 4 * 1 ≤ 3 ^ 3 - 3 :=
  four_mul_le_of_reachable (capacity := onePathCapacity) (source := 0) (sink := 2)
    (by decide) (zeroFlow 3)
    (fun i hi => by
      obtain rfl : i = 0 := by omega
      simpa using reachable_zero)

/-- On three vertices the algorithm stops within `(27 - 3) / 4 = 6` augmentations. -/
example : ∃ i ≤ 6,
    ¬ (residualGraph onePathCapacity
      ((step onePathCapacity 0 2)^[i] (zeroFlow 3))).Reachable 0 2 := by
  simpa using exists_not_reachable_iterate_step (capacity := onePathCapacity)
    (source := 0) (sink := 2) (by decide) (zeroFlow 3)

/-- The sharp count `C(3, 2) ⌊3 / 2⌋ = 3`. -/
example {m : ℕ} (h : ∀ i < m, (residualGraph onePathCapacity
      ((step onePathCapacity 0 2)^[i] (zeroFlow 3))).Reachable 0 2) : m ≤ 3 := by
  simpa using le_choose_mul_of_reachable (source := 0) (sink := 2) (by decide) (zeroFlow 3) h

example : edgeDelta [(0 : Fin 3), 1, 2] 0 1 = 1 :=
  edgeDelta_eq_one_of_mem (by decide) (by simp [pathEdges])

example : edgeDelta [(0 : Fin 3), 1] 2 0 = 0 :=
  edgeDelta_eq_zero_of_not_mem (by decide)

end Cslib.Algorithms.Lean.EdmondsKarpAugmentationBoundTests
