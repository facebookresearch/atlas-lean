/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_ModularCurve_SerreImage_contains_SL2.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

import MathlibExt.GroupTheory.IrreducibleUnipotentSL2

open Matrix MatrixGroups Subgroup

namespace IrreducibleUnipotentSL2Test

/-- Consumer with the original binders: an irreducible subgroup of
`GL(2, ZMod p)` containing a nontrivial square-zero unipotent contains
the image of `SL(2, ZMod p)`. -/
theorem exactSource {p : ℕ} [Fact p.Prime]
    (H : Subgroup (GL (Fin 2) (ZMod p)))
    (hirr : ∀ v : Fin 2 → ZMod p, v ≠ 0 → ∃ g ∈ H, ∀ c : ZMod p,
      ((g : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)).mulVec v ≠ c • v)
    (hunip : ∃ u ∈ H, ((u : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) ^ 2 = 0 ∧ u ≠ 1) :
    (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod p)).range ≤ H :=
  SL2.range_toGL_le_of_irreducible_of_exists_unipotent H hirr hunip

/-- The trivial subgroup contains no nontrivial unipotent, so the
unipotent hypothesis cannot be dropped in favour of the conclusion for
every subgroup. -/
theorem bot_has_no_nontrivial_unipotent {p : ℕ} [Fact p.Prime] :
    ¬ ∃ u ∈ (⊥ : Subgroup (GL (Fin 2) (ZMod p))),
      ((u : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) ^ 2 = 0 ∧ u ≠ 1 := by
  rintro ⟨u, hu, -, hu1⟩
  exact hu1 (Subgroup.mem_bot.mp hu)

/-- In characteristic five, Mathlib's transvection with entry `1` is a nontrivial
square-zero unipotent of `GL(2, ZMod 5)`, so the unipotent hypothesis can hold. -/
theorem top_has_nontrivial_unipotent_example :
    ∃ u ∈ (⊤ : Subgroup (GL (Fin 2) (ZMod 5))),
      ((u : Matrix (Fin 2) (Fin 2) (ZMod 5)) - 1) ^ 2 = 0 ∧ u ≠ 1 := by
  refine ⟨Matrix.SpecialLinearGroup.toGL
    (SpecialLinearGroup.transvection zero_ne_one (1 : ZMod 5)), Subgroup.mem_top _, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> decide
  · intro h
    have h01 := congrArg (fun M : GL (Fin 2) (ZMod 5) =>
      (M : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1) h
    simp [SpecialLinearGroup.transvection_coe] at h01
    exact (by decide : (1 : ZMod 5) ≠ 0) h01

end IrreducibleUnipotentSL2Test
