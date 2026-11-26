/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FiniteStateTreeAutomorphism
import Mathlib.Logic.Equiv.List

/-! # Tests for the finite-state subgroup and its sections -/

namespace MathlibExtTest.GroupTheory.FiniteStateTreeAutomorphism

open MathlibExt.GroupTheory
open FiniteStateTree

-- The membership criterion includes the tree with only its root.
example : IsFiniteStateAut (1 : Equiv.Perm (List (Fin 0))) :=
  (mem_finiteStateAutomorphisms_iff _).mp (finiteStateAutomorphisms 0).one_mem

-- A predicate hypothesis can be used in a subgroup calculation and recovered afterwards.
example {d : ℕ} {g h : Equiv.Perm (List (Fin d))} (hg : IsFiniteStateAut g)
    (hh : IsFiniteStateAut h) : IsFiniteStateAut (g * h⁻¹) := by
  rw [← mem_finiteStateAutomorphisms_iff] at hg hh ⊢
  exact (finiteStateAutomorphisms d).mul_mem hg ((finiteStateAutomorphisms d).inv_mem hh)

-- Swapping the root with its child distinguishes the two section conventions.
private def swapRoot : Equiv.Perm (List (Fin 1)) := Equiv.swap [] [0]

example : treeSection swapRoot [] [] = [0] ∧
    FiniteStateIrreducibleGeneratorsKourovka16Problem86Wanted.treeSection swapRoot [] [] = [] := by
  decide

end MathlibExtTest.GroupTheory.FiniteStateTreeAutomorphism
