/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.Function.Iterate
import Mathlib.Data.Fin.VecNotation

/-! A forest on `Fin 6` with trees `0 ← 1 ← 2 ← 3` and `4 ← 5`; the roots `0` and `4` are fixed. -/

/-- The parent map. -/
private def parent : Fin 6 → Fin 6 := ![0, 0, 1, 2, 4, 4]

/-- Node depths: the number of parent steps to the root. -/
private def depth : Fin 6 → ℕ := ![0, 1, 2, 3, 0, 1]

private theorem parent_depth : ∀ x, parent x ≠ x → depth (parent x) + 1 = depth x := by
  decide

/-- A non-root ancestor: `1` is `depth 3 - depth 1 = 2` parent steps above `3`. -/
example : parent^[depth 3 - depth 1] 3 = 1 :=
  Function.iterate_depth_sub_eq_of_iterate_eq parent_depth (k := 2) (by decide)

example : depth 3 - depth 1 = 2 := by decide

/-- A root is fixed by every jump. -/
example : parent^[7] 4 = 4 := Function.iterate_fixed (by decide) 7

/-- A jump beyond the root stops there; the theorem recovers the exact distance `3`. -/
example : parent^[10] 3 = 0 := by decide

example : parent^[depth 3 - depth 0] 3 = 0 :=
  Function.iterate_depth_sub_eq_of_iterate_eq parent_depth (k := 10) (by decide)

/-- The second tree: `5` reaches its root `4` in one step. -/
example : parent^[depth 5 - depth 4] 5 = 4 :=
  Function.iterate_depth_sub_eq_of_iterate_eq parent_depth (k := 1) (by decide)

/-- From a root, the only point reached is the root itself, after zero steps. -/
example : parent^[depth 0 - depth 0] 0 = 0 :=
  Function.iterate_depth_sub_eq_of_iterate_eq parent_depth (k := 5) (by decide)
