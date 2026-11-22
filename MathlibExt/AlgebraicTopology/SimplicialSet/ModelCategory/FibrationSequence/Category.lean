/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence

/-!
# The actual category and whole functors of pointed Kan fibration sequences

The original bundled sequence and its original pointed square form a
category. All three whole simplicial-set functors retain the literal total,
base and strict-fiber objects and maps. The full original fiber inclusion is
natural. This is the source category for original native pointed-fibration
Arrows and the complete chosen-level exact-sequence comparison.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory

namespace SSet.FibrationSequence.Geometry

/-- Equality of both actual square maps determines the entire pointed fibration-sequence map. -/
theorem hom_ext {S T : SSet.FibrationSequence.{u}} {f g : SSet.FibrationSequenceHom S T}
    (hTotal : f.totalMap = g.totalMap) (hBase : f.baseMap = g.baseMap) : f = g := by
  cases f
  cases g
  cases hTotal
  cases hBase
  rfl

/-- The original pointed fibration sequences and complete original squares form a category. -/
instance category : Category.{u} SSet.FibrationSequence.{u} where
  Hom := SSet.FibrationSequenceHom
  id := SSet.FibrationSequenceHom.id
  comp := SSet.FibrationSequenceHom.comp
  id_comp f := by
    apply hom_ext
    · exact Category.id_comp f.totalMap
    · exact Category.id_comp f.baseMap
  comp_id f := by
    apply hom_ext
    · exact Category.comp_id f.totalMap
    · exact Category.comp_id f.baseMap
  assoc f g h := by
    apply hom_ext
    · exact Category.assoc f.totalMap g.totalMap h.totalMap
    · exact Category.assoc f.baseMap g.baseMap h.baseMap

/-- The full actual original total-space object and map form a functor. -/
def totalFunctor : SSet.FibrationSequence.{u} ⥤ SSet.{u} where
  obj S := S.E
  map f := f.totalMap
  map_id S := (rfl : (SSet.FibrationSequenceHom.id S).totalMap = 𝟙 S.E)
  map_comp f g := (rfl : (SSet.FibrationSequenceHom.comp f g).totalMap = f.totalMap ≫ g.totalMap)

/-- The full actual original base-space object and map form a functor. -/
def baseFunctor : SSet.FibrationSequence.{u} ⥤ SSet.{u} where
  obj S := S.B
  map f := f.baseMap
  map_id S := (rfl : (SSet.FibrationSequenceHom.id S).baseMap = 𝟙 S.B)
  map_comp f g := (rfl : (SSet.FibrationSequenceHom.comp f g).baseMap = f.baseMap ≫ g.baseMap)

/-- The full actual original strict-fiber objects and complete maps form a functor. -/
def fiberFunctor : SSet.FibrationSequence.{u} ⥤ SSet.{u} where
  obj S := S.fiber
  map f := f.fiberMap
  map_id S := SSet.FibrationSequenceHom.id_fiberMap S
  map_comp f g := SSet.FibrationSequenceHom.comp_fiberMap f g

/-- Every original total functor map is the exact original total component. -/
theorem totalFunctor_map {S T : SSet.FibrationSequence.{u}} (f : S ⟶ T) :
    totalFunctor.map f = f.totalMap := rfl

/-- Every original base functor map is the exact original base component. -/
theorem baseFunctor_map {S T : SSet.FibrationSequence.{u}} (f : S ⟶ T) :
    baseFunctor.map f = f.baseMap := rfl

/-- Every original fiber functor map is the exact original full strict-fiber map. -/
theorem fiberFunctor_map {S T : SSet.FibrationSequence.{u}} (f : S ⟶ T) :
    fiberFunctor.map f = f.fiberMap := rfl

/-- Both original total/base square components retain their entire projection naturality. -/
def projectionNatTrans : totalFunctor.{u} ⟶ baseFunctor where
  app S := S.p
  naturality {S T} f := (f : SSet.FibrationSequenceHom S T).comm

/-- The entire original native strict-fiber inclusion is natural in every original square. -/
def inclusionNatTrans : fiberFunctor.{u} ⟶ totalFunctor where
  app S := S.fiberIncl
  naturality {S T} f := SSet.FibrationSequenceHom.fiberMap_ι (S := S) (T := T) f

end SSet.FibrationSequence.Geometry
