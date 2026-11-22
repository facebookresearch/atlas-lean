/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeSectionReadback

/-!
# The original diagonal section is the same retained basepoint map

The original section in every degree is the actual constant-row extension
of its original zero-row identity edge. Its diagonal is therefore the
literal retained diagonal basepoint map, with the original constant
diagonal isomorphism.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

set_option backward.isDefEq.respectTransparency false in
/-- The original whole section is its literal original zero-row constant extension. -/
theorem nativeSection_eq_constantExtension (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    nativeSection W x = (SimplicialObject.const SSet.{u}).map (sectionZero W x) ≫
      SSet.EquifibredDiagonal.vertexConstantDiagramMap (diagram W x) (SimplexCategory.mk 0) 0 := by
  apply NatTrans.ext
  funext n
  change (extraDegeneracy W x).s' ≫
      (diagram W x).map (SimplexCategory.isTerminalZero.from n.unop).op =
    sectionZero W x ≫ (diagram W x).map (SimplexCategory.const n.unop (SimplexCategory.mk 0) 0).op
  rw [← sectionZero_eq_extraDegeneracy_section]
  congr 2

/-- The actual diagonal section is the same original identity-edge basepoint map. -/
theorem diagonal_nativeSection (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.simplicialDiagonalFunctor.map (nativeSection W x) =
      (SSet.diagonalConstIso (Δ[0] : SSet.{u})).hom ≫ diagonalBasepointMap W x := by
  rw [nativeSection_eq_constantExtension, SSet.simplicialDiagonalFunctor.map_comp]
  have hn := CategoryTheory.SimplicialObject.diagonalConstIso_naturality (Type u) (sectionZero W x)
  change SSet.simplicialDiagonalFunctor.map ((SimplicialObject.const SSet.{u}).map (sectionZero W x)) ≫
      (SSet.diagonalConstIso ((diagram W x).obj (op (SimplexCategory.mk 0)))).hom =
    (SSet.diagonalConstIso (Δ[0] : SSet.{u})).hom ≫ sectionZero W x at hn
  have hc := congrArg (fun q => q ≫
      (SSet.diagonalConstIso ((diagram W x).obj (op (SimplexCategory.mk 0)))).inv ≫
      SSet.simplicialDiagonalFunctor.map
        (SSet.EquifibredDiagonal.vertexConstantDiagramMap (diagram W x) (SimplexCategory.mk 0) 0)) hn
  simpa only [diagonalBasepointMap, SSet.EquifibredDiagonal.rowVertexToDiagonal,
    Category.assoc, Iso.hom_inv_id_assoc] using hc

/-- The original diagonal augmentation-section roundtrip is the original constant basepoint map. -/
theorem diagonal_nativeRetraction (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.simplicialDiagonalFunctor.map (nativeRetraction W x) =
      diagonalAugmentation W x ≫ diagonalBasepointMap W x := by
  rw [nativeRetraction, SSet.simplicialDiagonalFunctor.map_comp, diagonal_nativeSection]
  rfl

end SimplicialSpace.LeftDecalageObject
