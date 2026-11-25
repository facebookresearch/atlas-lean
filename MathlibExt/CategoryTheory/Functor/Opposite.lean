/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Opposites

/-!
# Opposite functors and natural isomorphisms

An opposite functor preserves zero morphisms when the given functor does. A natural isomorphism
between functors from an opposite category induces a natural isomorphism between their rightOp
functors, with the direction reversed.
-/

@[expose] public section

namespace CategoryTheory.Functor

open CategoryTheory.Limits

universe uC vC uD vD

variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]
  {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]

/-- Opposite functors preserve zero morphisms whenever the functor does. -/
instance preservesZeroMorphisms_op (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    F.op.PreservesZeroMorphisms where
  map_zero X Y := by
    change (F.map (0 : Y.unop ⟶ X.unop)).op = 0
    rw [F.map_zero, op_zero]

end CategoryTheory.Functor


namespace CategoryTheory.NatIso

universe uC vC uD vD

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- A natural isomorphism induces a rightOp natural isomorphism in the reverse direction. -/
def rightOp {F G : Cᵒᵖ ⥤ D} (e : F ≅ G) : G.rightOp ≅ F.rightOp where
  hom := NatTrans.rightOp e.hom
  inv := NatTrans.rightOp e.inv
  hom_inv_id := by
    rw [← NatTrans.rightOp_comp, e.inv_hom_id, NatTrans.rightOp_id]
  inv_hom_id := by
    rw [← NatTrans.rightOp_comp, e.hom_inv_id, NatTrans.rightOp_id]

end CategoryTheory.NatIso
