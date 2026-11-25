/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.CGWH.Path

/-!
# Owner tests for the native CGWH interval and path functor
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

namespace MathlibExtTest.Topology.Category.CGWH.PathTests

-- Exact fourteen-name public surface, in provider order.
#check CGWH.interval
#check CGWH.intervalZero
#check CGWH.intervalOne
#check CGWH.intervalBoundary
#check CGWH.intervalAugmentation
#check CGWH.path
#check CGWH.pathEvalZero
#check CGWH.pathEvalOne
#check CGWH.pathEndpoints
#check CGWH.pathConstant
#check CGWH.pathEndpoints_fst
#check CGWH.pathEndpoints_snd
#check CGWH.pathConstant_evalZero
#check CGWH.pathConstant_evalOne

section EndpointOrientation

example : CGWH.intervalZero.{u, v} =
    (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
      SSet.toCGWH.{u, v}.map
        (SSet.stdSimplex.δ (1 : Fin 2)) :=
  rfl

example : CGWH.intervalOne.{u, v} =
    (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
      SSet.toCGWH.{u, v}.map
        (SSet.stdSimplex.δ (0 : Fin 2)) :=
  rfl

#guard_msgs (error, substring := true) in
example : CGWH.intervalZero.{u, v} =
    (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
      SSet.toCGWH.{u, v}.map
        (SSet.stdSimplex.δ (0 : Fin 2)) := by
  rfl

#guard_msgs (error, substring := true) in
example : CGWH.intervalOne.{u, v} =
    (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
      SSet.toCGWH.{u, v}.map
        (SSet.stdSimplex.δ (1 : Fin 2)) := by
  rfl

example :
    (coprod.inl : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫
        CGWH.intervalBoundary.{u, v} =
      CGWH.intervalZero.{u, v} := by
  simp [CGWH.intervalBoundary]

example :
    (coprod.inr : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫
        CGWH.intervalBoundary.{u, v} =
      CGWH.intervalOne.{u, v} := by
  simp [CGWH.intervalBoundary]

example :
    CGWH.intervalZero.{u, v} ≫ CGWH.intervalAugmentation.{u, v} =
      𝟙 CGWH.point.{u, v} :=
  CGWH.point_isTerminal.hom_ext _ _

example :
    CGWH.intervalOne.{u, v} ≫ CGWH.intervalAugmentation.{u, v} =
      𝟙 CGWH.point.{u, v} :=
  CGWH.point_isTerminal.hom_ext _ _

end EndpointOrientation

section FunctorAndNaturality

variable {X Y Z : CGWH.{u, v}} (f : X ⟶ Y) (g : Y ⟶ Z)

example (B : CGWH.{u, v}) :
    CGWH.path.{u, v}.obj B =
      CGWH.internalHom CGWH.interval B :=
  CGWH.ihom_obj_eq_internalHom CGWH.interval B

example :
    CGWH.path.{u, v}.map (𝟙 X) = 𝟙 (CGWH.path.obj X) :=
  CGWH.path.map_id X

example :
    CGWH.path.{u, v}.map (f ≫ g) =
      CGWH.path.map f ≫ CGWH.path.map g :=
  CGWH.path.map_comp f g

example (B : CGWH.{u, v}) :
    CGWH.path.{u, v}.obj B ⟶ B :=
  CGWH.pathEvalZero.app B

example (B : CGWH.{u, v}) :
    CGWH.path.{u, v}.obj B ⟶ B :=
  CGWH.pathEvalOne.app B

example (B : CGWH.{u, v}) :
    CGWH.path.{u, v}.obj B ⟶ B ⊗ B :=
  CGWH.pathEndpoints.app B

example (B : CGWH.{u, v}) :
    B ⟶ CGWH.path.{u, v}.obj B :=
  CGWH.pathConstant.app B

example :
    CGWH.path.map f ≫ CGWH.pathEvalZero.app Y =
      CGWH.pathEvalZero.app X ≫ f :=
  CGWH.pathEvalZero.naturality f

example :
    CGWH.path.map f ≫ CGWH.pathEvalOne.app Y =
      CGWH.pathEvalOne.app X ≫ f :=
  CGWH.pathEvalOne.naturality f

example :
    CGWH.path.map f ≫ CGWH.pathEndpoints.app Y =
      CGWH.pathEndpoints.app X ≫ (f ⊗ₘ f) :=
  CGWH.pathEndpoints.naturality f

example :
    f ≫ CGWH.pathConstant.app Y =
      CGWH.pathConstant.app X ≫ CGWH.path.map f :=
  CGWH.pathConstant.naturality f

end FunctorAndNaturality

section ConcreteNonidentity

example :
    CGWH.path.map CGWH.intervalAugmentation ≫
        CGWH.pathEvalZero.app CGWH.point =
      CGWH.pathEvalZero.app CGWH.interval ≫
        CGWH.intervalAugmentation :=
  CGWH.pathEvalZero.naturality CGWH.intervalAugmentation

example :
    CGWH.intervalAugmentation ≫ CGWH.pathConstant.app CGWH.point =
      CGWH.pathConstant.app CGWH.interval ≫
        CGWH.path.map CGWH.intervalAugmentation :=
  CGWH.pathConstant.naturality CGWH.intervalAugmentation

end ConcreteNonidentity

section CharacteristicLaws

variable (B : CGWH.{u, v})

example :
    CGWH.pathEndpoints.app B ≫
        CartesianMonoidalCategory.fst B B =
      CGWH.pathEvalZero.app B :=
  CGWH.pathEndpoints_fst B

example :
    CGWH.pathEndpoints.app B ≫
        CartesianMonoidalCategory.snd B B =
      CGWH.pathEvalOne.app B :=
  CGWH.pathEndpoints_snd B

example :
    CGWH.pathConstant.app B ≫ CGWH.pathEvalZero.app B = 𝟙 B :=
  CGWH.pathConstant_evalZero B

example :
    CGWH.pathConstant.app B ≫ CGWH.pathEvalOne.app B = 𝟙 B :=
  CGWH.pathConstant_evalOne B

end CharacteristicLaws

section UniverseMatrix

#check CGWH.interval.{0, 0}
#check CGWH.intervalZero.{0, 0}
#check CGWH.path.{0, 0}
#check CGWH.pathEvalZero.{0, 0}
#check CGWH.pathEvalOne.{0, 0}
#check CGWH.pathEndpoints.{0, 0}
#check CGWH.pathConstant.{0, 0}

#check CGWH.interval.{1, 1}
#check CGWH.intervalZero.{1, 1}
#check CGWH.path.{1, 1}
#check CGWH.pathEvalZero.{1, 1}
#check CGWH.pathEvalOne.{1, 1}
#check CGWH.pathEndpoints.{1, 1}
#check CGWH.pathConstant.{1, 1}

#check CGWH.interval.{0, 1}
#check CGWH.intervalZero.{0, 1}
#check CGWH.path.{0, 1}
#check CGWH.pathEvalZero.{0, 1}
#check CGWH.pathEvalOne.{0, 1}
#check CGWH.pathEndpoints.{0, 1}
#check CGWH.pathConstant.{0, 1}

#check CGWH.interval.{1, 0}
#check CGWH.intervalZero.{1, 0}
#check CGWH.path.{1, 0}
#check CGWH.pathEvalZero.{1, 0}
#check CGWH.pathEvalOne.{1, 0}
#check CGWH.pathEndpoints.{1, 0}
#check CGWH.pathConstant.{1, 0}

#check CGWH.interval.{u, v}
#check CGWH.intervalZero.{u, v}
#check CGWH.path.{u, v}
#check CGWH.pathEvalZero.{u, v}
#check CGWH.pathEvalOne.{u, v}
#check CGWH.pathEndpoints.{u, v}
#check CGWH.pathConstant.{u, v}

end UniverseMatrix

-- No top-level endpoint adapter or compatibility facade is exposed.
#guard_msgs (error, substring := true) in
#check CGWH.intervalZeroFromUnit
#guard_msgs (error, substring := true) in
#check CGWH.intervalOneFromUnit
#guard_msgs (error, substring := true) in
#check CGWH.intervalPointIso
#guard_msgs (error, substring := true) in
#check CGWH.pathObject
#guard_msgs (error, substring := true) in
#check CGWH.homotopyFiber
#guard_msgs (error, substring := true) in
#check DeltaGenerated.pathObject

#print axioms CGWH.interval
#print axioms CGWH.intervalZero
#print axioms CGWH.intervalOne
#print axioms CGWH.intervalBoundary
#print axioms CGWH.intervalAugmentation
#print axioms CGWH.path
#print axioms CGWH.pathEvalZero
#print axioms CGWH.pathEvalOne
#print axioms CGWH.pathEndpoints
#print axioms CGWH.pathConstant
#print axioms CGWH.pathEndpoints_fst
#print axioms CGWH.pathEndpoints_snd
#print axioms CGWH.pathConstant_evalZero
#print axioms CGWH.pathConstant_evalOne

end MathlibExtTest.Topology.Category.CGWH.PathTests
