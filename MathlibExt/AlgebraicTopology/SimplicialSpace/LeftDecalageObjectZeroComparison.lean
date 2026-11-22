/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectZeroFibre
import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectRowFibration

/-!
# The exact original zero row of the fixed-object decalage

The first-vertex augmentation in shifted degree zero is the original
source face. The whole evaluated pullback is therefore precisely the
original source-edge object. Its right-block projection is the original
target face, retaining both prescribed endpoints and every original edge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

private theorem pullback_congr_fst {X Y Z : SSet.{u}} {f g : X ⟶ Z}
    (h : f = g) (b : Y ⟶ Z) :
    (pullback.congrHom h (show b = b from rfl)).hom ≫ pullback.fst g b = pullback.fst f b := by
  subst g
  simp [pullback.congrHom_hom, pullback.map]

/-- The original first-vertex augmentation at shifted zero degree is the literal source face. -/
theorem augmentation_zero (W : SimplicialSpace.{u}) :
    (CategoryTheory.SimplicialObject.LeftDecalage.augmentation W.diagram).app
        (op (SimplexCategory.mk 0)) = W.diagram.δ (1 : Fin 2) := by
  change W.diagram.map (CategoryTheory.SimplicialObject.LeftDecalage.firstVertex.app
    (SimplexCategory.mk 0)).op = W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op
  apply congrArg W.diagram.map
  apply Quiver.Hom.unop_inj
  ext i
  fin_cases i
  rfl

/-- The whole original fixed-object zero row is precisely its original source-edge pullback. -/
def zeroRowIso (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (diagram W x).obj (op (SimplexCategory.mk 0)) ≅ sourceEdges W x :=
  rowIso W x 0 ≪≫ pullback.congrHom (augmentation_zero W) rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
/-- The whole original zero-row comparison retains its actual source edge. -/
theorem zeroRowIso_fst (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
      (zeroRowIso W x).hom ≫ pullback.fst _ _ = (toDecalage W x).app (op (SimplexCategory.mk 0)) := by
  have hi := pullback_congr_fst (augmentation_zero W) (SSet.yonedaEquiv.symm x)
  change ((rowIso W x 0).hom ≫ (pullback.congrHom (augmentation_zero W)
    (show SSet.yonedaEquiv.symm x = SSet.yonedaEquiv.symm x from rfl)).hom) ≫ _ = _
  calc
    _ = (rowIso W x 0).hom ≫ ((pullback.congrHom (augmentation_zero W)
        (show SSet.yonedaEquiv.symm x = SSet.yonedaEquiv.symm x from rfl)).hom ≫ _) :=
      Category.assoc _ _ _
    _ = (rowIso W x 0).hom ≫ pullback.fst
        ((SimplicialObject.LeftDecalage.augmentation W.diagram).app (op (SimplexCategory.mk 0)))
        (SSet.yonedaEquiv.symm x) := congrArg (fun q => (rowIso W x 0).hom ≫ q) hi
    _ = _ := rowIso_fst W x 0

set_option backward.isDefEq.respectTransparency false in
/-- The actual original zero-row path projection is exactly the original target face. -/
theorem zeroRowIso_target (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (zeroRowIso W x).hom ≫ sourceEdgesTarget W x = (projection W x).app (op (SimplexCategory.mk 0)) := by
  rw [sourceEdgesTarget, ← Category.assoc, zeroRowIso_fst]
  rfl

end SimplicialSpace.LeftDecalageObject
