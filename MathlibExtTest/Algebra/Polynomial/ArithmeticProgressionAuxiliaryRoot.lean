/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.ArithmeticProgressionAuxiliaryRoot
import Mathlib.Tactic.NormNum

/-!
# Boundary case of the auxiliary equation

At the minimum degree parameter `m = 2` with `a = d = 1`, the cubic coefficient vanishes.
-/

example : ∃! x : ℝ, 1 < x ∧ x ^ 4 - 4 * x - 3 = 0 := by
  obtain ⟨hunique, hbound⟩ :=
    MetaMathlibExt.arithProgPoly_eq3_existsUnique_pos (m := 2) (a := 1) (d := 1)
      (by decide) (by decide) le_rfl
  norm_num at hunique hbound
  obtain ⟨r, ⟨hr, hroot⟩, hu⟩ := hunique
  exact ⟨r, ⟨hbound r hr hroot, hroot⟩, fun x ⟨hx, heq⟩ ↦ hu x ⟨zero_lt_one.trans hx, heq⟩⟩
