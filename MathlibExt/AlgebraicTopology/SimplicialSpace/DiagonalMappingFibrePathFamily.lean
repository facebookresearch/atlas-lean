/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.DiagonalMappingFibreHomotopy
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyMap

/-!
# The actual realized original mapping-edge path family

Realize the complete original interval cylinder and curry its two-variable
map into compact-open paths. This retains the entire original mapping
fibre, original diagonal and all original carried interval values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Topology
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The whole original diagonal interval cylinder realized with its original mapping parameter. -/
def realizedMappingFibreCylinder (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    TopCat.I.{u} ⨯ SSet.toTop.obj (mappingFibre W x y) ⟶
      SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram) :=
  SSet.realizeHomotopyMap (mappingFibre W x y) _
    (mappingFibreDiagonalSource W x y) (mappingFibreDiagonalTarget W x y)
    (mappingFibreDiagonalHomotopy W x y)

/-- The actual complete original mapping edge as a compact-open path family. -/
def mappingFibreDiagonalPathFamily (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.toTop.obj (mappingFibre W x y) ⟶
      TopCat.pathObject (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram)) :=
  TopCat.ofHom <| ContinuousMap.curry <|
    (realizedMappingFibreCylinder W x y).hom.comp
      ((TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj (mappingFibre W x y))).inv.hom.comp
        ⟨fun z => (z.2, z.1), by fun_prop⟩)

/-- The whole path family reads back the literal realized cylinder at every original point and time. -/
theorem mappingFibreDiagonalPathFamily_apply (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (z : SSet.toTop.obj (mappingFibre W x y))
    (t : TopCat.I.{u}) :
    mappingFibreDiagonalPathFamily W x y z t =
      realizedMappingFibreCylinder W x y
        ((TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj (mappingFibre W x y))).inv (t, z)) := rfl

end SimplicialSpace.LeftDecalageObject
