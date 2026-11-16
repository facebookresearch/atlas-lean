/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Native closed homogeneous cochains as shifted morphisms

A closed degree-n cochain is realized in the literal native target
shift G[n]. Every component is the same cochain component, and the
native (-1)^n shift differential is retained. This is a completed
construction; no arbitrary shift comparison is supplied.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public section

namespace MathlibExt.Algebra.Homology.ClosedCochainShifts

open CategoryTheory CategoryTheory.Preadditive
open CochainComplex CochainComplex.HomComplex

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
    {F G : CochainComplex C ℤ} {n : ℤ}

/-- A native closed degree-n cochain is the actual morphism into G[n]. -/
noncomputable def homToShift (z : Cocycle F G n) : F ⟶ G⟦n⟧ where
  f i := (z : Cochain F G n).v i (i + n) rfl
  comm' := by
    rintro i j rfl
    symm
    change F.d i (i + 1) ≫ (z : Cochain F G n).v (i + 1) (i + 1 + n) rfl =
      (z : Cochain F G n).v i (i + n) rfl ≫
        (n.negOnePow • G.d (i + n) (i + 1 + n))
    have hz := Cochain.congr_v (Cocycle.δ_eq_zero z (n + 1)) i (i + 1 + n) (by omega)
    rw [δ_v n (n + 1) rfl _ i (i + 1 + n) (by omega)
      (i + n) (i + 1) (by omega) rfl] at hz
    have h : (z : Cochain F G n).v i (i + n) rfl ≫ G.d (i + n) (i + 1 + n) =
        n.negOnePow • (F.d i (i + 1) ≫ (z : Cochain F G n).v (i + 1) (i + 1 + n) rfl) := by
      simpa only [Cochain.zero_v, Int.negOnePow_succ, Units.neg_smul,
        Linear.units_smul_comp, ← sub_eq_add_neg, sub_eq_zero] using hz
    calc
      _ = n.negOnePow •
          (n.negOnePow • (F.d i (i + 1) ≫ (z : Cochain F G n).v (i + 1) (i + 1 + n) rfl)) := by
        rw [smul_smul, Int.units_mul_self, one_smul]
      _ = n.negOnePow •
          ((z : Cochain F G n).v i (i + n) rfl ≫ G.d (i + n) (i + 1 + n)) := by rw [← h]
      _ = _ := by rw [Linear.comp_units_smul]

/-- The native target-shift comparison recovers the exact original homogeneous component. -/
theorem homToShift_component (z : Cocycle F G n) (i : ℤ) :
    (homToShift z).f i ≫ (shiftFunctorObjXIso G n i (i + n) rfl).hom =
      (z : Cochain F G n).v i (i + n) rfl := by
  change (z : Cochain F G n).v i (i + n) rfl ≫ 𝟙 _ = _
  exact Category.comp_id _

end MathlibExt.Algebra.Homology.ClosedCochainShifts
