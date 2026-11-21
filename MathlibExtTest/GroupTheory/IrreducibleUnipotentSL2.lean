/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
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

/-- The elementary matrices multiply by adding their entries, and the
zero elementary matrix is the identity. -/
theorem upperElem_add_example (a b : ZMod 5) :
    SL2.upperElem a * SL2.upperElem b = SL2.upperElem (a + b) :=
  SL2.upperElem_mul a b

theorem upperElem_zero_example :
    SL2.upperElem (0 : ZMod 5) = 1 :=
  SL2.upperElem_zero

/-- In characteristic five, the upper elementary matrix with entry `1`
is a nontrivial square-zero unipotent in `SL(2, ZMod 5)`. -/
theorem upperElem_one_unipotent_example :
    (((SL2.upperElem (1 : ZMod 5) : SL(2, ZMod 5)) :
        Matrix (Fin 2) (Fin 2) (ZMod 5)) - 1) ^ 2 = 0 ∧
      SL2.upperElem (1 : ZMod 5) ≠ 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> decide
  · intro h
    have h01 := congrArg (fun M : SL(2, ZMod 5) => (M : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1) h
    simp only [SL2.upperElem_coe, Matrix.one_apply_eq] at h01
    exact (by decide : (1 : ZMod 5) ≠ 0) h01

end IrreducibleUnipotentSL2Test
