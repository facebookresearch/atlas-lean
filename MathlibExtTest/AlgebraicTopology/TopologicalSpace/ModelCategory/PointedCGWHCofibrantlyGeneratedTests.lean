/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHCofibrantlyGenerated

/-!
# Tests for cofibrant generation of pointed CGWH spaces

These owners pin the literal costar generators, both right-lifting
orientations, fixed-cardinal generation data, free-point equations, universe
polymorphism, and the absence of global instances or category-specific
secondary wrappers.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits
open CategoryTheory.MorphismProperty HomotopicalAlgebra

namespace MathlibExtTest.PointedCGWHCofibrantlyGeneratedTests

section PublicSurfaceAndUniverses

#check PointedCGWH.realizedBoundaryInclusions
#check PointedCGWH.realizedHornInclusions
#check PointedCGWH.realizedBoundaryInclusions_rlp
#check PointedCGWH.realizedHornInclusions_rlp
#check PointedCGWH.cofibrantGenerationData

#check @PointedCGWH.realizedBoundaryInclusions.{u, v}
#check @PointedCGWH.realizedBoundaryInclusions.{0, 0}
#check @PointedCGWH.realizedBoundaryInclusions.{1, 1}
#check @PointedCGWH.realizedBoundaryInclusions.{0, 1}
#check @PointedCGWH.realizedBoundaryInclusions.{1, 0}

#check @PointedCGWH.realizedHornInclusions.{u, v}
#check @PointedCGWH.realizedHornInclusions.{0, 0}
#check @PointedCGWH.realizedHornInclusions.{1, 1}
#check @PointedCGWH.realizedHornInclusions.{0, 1}
#check @PointedCGWH.realizedHornInclusions.{1, 0}

#check @PointedCGWH.realizedBoundaryInclusions_rlp.{u, v}
#check @PointedCGWH.realizedBoundaryInclusions_rlp.{0, 0}
#check @PointedCGWH.realizedBoundaryInclusions_rlp.{1, 1}
#check @PointedCGWH.realizedBoundaryInclusions_rlp.{0, 1}
#check @PointedCGWH.realizedBoundaryInclusions_rlp.{1, 0}

#check @PointedCGWH.realizedHornInclusions_rlp.{u, v}
#check @PointedCGWH.realizedHornInclusions_rlp.{0, 0}
#check @PointedCGWH.realizedHornInclusions_rlp.{1, 1}
#check @PointedCGWH.realizedHornInclusions_rlp.{0, 1}
#check @PointedCGWH.realizedHornInclusions_rlp.{1, 0}

#check @PointedCGWH.cofibrantGenerationData.{u, v}
#check @PointedCGWH.cofibrantGenerationData.{0, 0}
#check @PointedCGWH.cofibrantGenerationData.{1, 1}
#check @PointedCGWH.cofibrantGenerationData.{0, 1}
#check @PointedCGWH.cofibrantGenerationData.{1, 0}

end PublicSurfaceAndUniverses

section NoSelectedScope

example : True := by
  fail_if_success
    let _ : ModelCategory CGWH.{u, v} := inferInstance
  fail_if_success
    let _ : ModelCategory PointedCGWH.{u, v} := inferInstance
  fail_if_success
    let _ : PointedCGWH.realizedBoundaryInclusions.{u, v}
        .IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
      inferInstance
  fail_if_success
    let _ : PointedCGWH.realizedHornInclusions.{u, v}
        .IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
      inferInstance
  fail_if_success
    let _ : PointedCGWH.realizedBoundaryInclusions.{u, v}
        .HasSmallObjectArgument := inferInstance
  fail_if_success
    let _ : PointedCGWH.realizedHornInclusions.{u, v}
        .HasSmallObjectArgument := inferInstance
  trivial

end NoSelectedScope

section SelectedModel

open scoped CGWH.modelCategory

#synth ModelCategory CGWH.{u, v}
#synth ModelCategory PointedCGWH.{u, v}

example : PointedCGWH.cofibrantGenerationData.{u, v}.I =
    PointedCGWH.realizedBoundaryInclusions.{u, v} := rfl

example : PointedCGWH.cofibrantGenerationData.{u, v}.J =
    PointedCGWH.realizedHornInclusions.{u, v} := rfl

example : MorphismProperty.IsCardinalForSmallObjectArgument
    PointedCGWH.realizedBoundaryInclusions.{u, v}
      realizedGeneratorCardinal.{v} :=
  PointedCGWH.cofibrantGenerationData.{u, v}.I_smallObject

example : MorphismProperty.IsCardinalForSmallObjectArgument
    PointedCGWH.realizedHornInclusions.{u, v}
      realizedGeneratorCardinal.{v} :=
  PointedCGWH.cofibrantGenerationData.{u, v}.J_smallObject

example : PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp =
    CGWH.realizedBoundaryInclusions.{u, v}.rlp.inverseImage
      PointedCGWH.pointedToCGWH.{u, v} :=
  PointedCGWH.realizedBoundaryInclusions_rlp

example : CGWH.realizedBoundaryInclusions.{u, v}.rlp.inverseImage
      PointedCGWH.pointedToCGWH.{u, v} =
    PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp :=
  PointedCGWH.realizedBoundaryInclusions_rlp.symm

example : PointedCGWH.realizedHornInclusions.{u, v}.rlp =
    CGWH.realizedHornInclusions.{u, v}.rlp.inverseImage
      PointedCGWH.pointedToCGWH.{u, v} :=
  PointedCGWH.realizedHornInclusions_rlp

example : CGWH.realizedHornInclusions.{u, v}.rlp.inverseImage
      PointedCGWH.pointedToCGWH.{u, v} =
    PointedCGWH.realizedHornInclusions.{u, v}.rlp :=
  PointedCGWH.realizedHornInclusions_rlp.symm

example : PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp =
    trivialFibrations PointedCGWH.{u, v} :=
  PointedCGWH.cofibrantGenerationData.{u, v}.I_rlp

example : trivialFibrations PointedCGWH.{u, v} =
    PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp :=
  PointedCGWH.cofibrantGenerationData.{u, v}.I_rlp.symm

example : PointedCGWH.realizedHornInclusions.{u, v}.rlp =
    fibrations PointedCGWH.{u, v} :=
  PointedCGWH.cofibrantGenerationData.{u, v}.J_rlp

example : fibrations PointedCGWH.{u, v} =
    PointedCGWH.realizedHornInclusions.{u, v}.rlp :=
  PointedCGWH.cofibrantGenerationData.{u, v}.J_rlp.symm

example {X Y : PointedCGWH.{u, v}} {f : X ⟶ Y}
    (hf : PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp f) :
    trivialFibrations PointedCGWH.{u, v} f := by
  change PointedCGWH.cofibrantGenerationData.{u, v}.I.rlp f at hf
  rw [PointedCGWH.cofibrantGenerationData.I_rlp] at hf
  exact hf

example {X Y : PointedCGWH.{u, v}} {f : X ⟶ Y}
    (hf : trivialFibrations PointedCGWH.{u, v} f) :
    PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp f := by
  change PointedCGWH.cofibrantGenerationData.{u, v}.I.rlp f
  rw [PointedCGWH.cofibrantGenerationData.I_rlp]
  exact hf

example {X Y : PointedCGWH.{u, v}} {f : X ⟶ Y}
    (hf : PointedCGWH.realizedHornInclusions.{u, v}.rlp f) :
    fibrations PointedCGWH.{u, v} f := by
  change PointedCGWH.cofibrantGenerationData.{u, v}.J.rlp f at hf
  rw [PointedCGWH.cofibrantGenerationData.J_rlp] at hf
  exact hf

example {X Y : PointedCGWH.{u, v}} {f : X ⟶ Y}
    (hf : fibrations PointedCGWH.{u, v} f) :
    PointedCGWH.realizedHornInclusions.{u, v}.rlp f := by
  change PointedCGWH.cofibrantGenerationData.{u, v}.J.rlp f
  rw [PointedCGWH.cofibrantGenerationData.J_rlp]
  exact hf

example : True := by
  fail_if_success
    let _ : IsCombinatorialModelCategory.{v} PointedCGWH.{u, v} :=
      inferInstance
  trivial

end SelectedModel

section CostarGeometry

example (A : CGWH.{u, v}) :
    ((Under.costar CGWH.point.{u, v}).obj A).right =
      Limits.coprod CGWH.point.{u, v} A := rfl

example (A : CGWH.{u, v}) :
    ((Under.costar CGWH.point.{u, v}).obj A).hom =
      Limits.coprod.inl ≫
        Limits.coprod.desc Limits.coprod.inl
          (𝟙 (Limits.coprod CGWH.point.{u, v} A)) :=
  Under.costar_obj_hom _ _

example {A B : CGWH.{u, v}} (f : A ⟶ B) :
    ((Under.costar CGWH.point.{u, v}).map f).right =
      Limits.coprod.map (𝟙 CGWH.point.{u, v}) f := rfl

example {A B : CGWH.{u, v}} (f : A ⟶ B) :
    ((Under.costar CGWH.point.{u, v}).obj A).hom ≫
        ((Under.costar CGWH.point.{u, v}).map f).right =
      ((Under.costar CGWH.point.{u, v}).obj B).hom :=
  Under.w _

example {A B : CGWH.{u, v}} (f : A ⟶ B) :
    PointedCGWH.pointedToCGWH.{u, v}.map
        ((Under.costar CGWH.point.{u, v}).map f) =
      Limits.coprod.map (𝟙 CGWH.point.{u, v}) f := rfl

example : PointedCGWH.realizedBoundaryInclusions.{u, v}
    ((Under.costar CGWH.point.{u, v}).map
      (CGWH.realizedBoundaryInclusion.{v, u} 0)) := by
  exact MorphismProperty.strictMap.map
    (CGWH.boundary_mem_realizedBoundaryInclusions.{u, v} 0)

example : PointedCGWH.realizedHornInclusions.{u, v}
    ((Under.costar CGWH.point.{u, v}).map
      (CGWH.realizedHornInclusion.{v, u} 0 (0 : Fin 2))) := by
  exact MorphismProperty.strictMap.map
    (CGWH.horn_mem_realizedHornInclusions.{u, v} 0 (0 : Fin 2))

end CostarGeometry

section ScopeTeardown

example : True := by
  fail_if_success
    let _ : ModelCategory CGWH.{u, v} := inferInstance
  fail_if_success
    let _ : ModelCategory PointedCGWH.{u, v} := inferInstance
  trivial

end ScopeTeardown

section Nonclaims

#guard_msgs (error, substring := true) in
#check PointedCGWH.instIsCardinalForSmallObjectArgumentRealizedBoundaryInclusions

#guard_msgs (error, substring := true) in
#check PointedCGWH.instIsCardinalForSmallObjectArgumentRealizedHornInclusions

#guard_msgs (error, substring := true) in
#check PointedCGWH.instHasSmallObjectArgumentRealizedBoundaryInclusions

#guard_msgs (error, substring := true) in
#check PointedCGWH.instHasSmallObjectArgumentRealizedHornInclusions

#guard_msgs (error, substring := true) in
#check PointedCGWH.functorialFactorizationData

#guard_msgs (error, substring := true) in
#check PointedCGWH.instIsLeftProper

#guard_msgs (error, substring := true) in
#check PointedCGWH.instIsRightProper

#guard_msgs (error, substring := true) in
#check PointedCGWH.instIsCombinatorialModelCategory

#guard_msgs (error, substring := true) in
#check PointedCGWH.factorization

end Nonclaims

#print axioms PointedCGWH.realizedBoundaryInclusions
#print axioms PointedCGWH.realizedHornInclusions
#print axioms PointedCGWH.realizedBoundaryInclusions_rlp
#print axioms PointedCGWH.realizedHornInclusions_rlp
#print axioms PointedCGWH.cofibrantGenerationData

end MathlibExtTest.PointedCGWHCofibrantlyGeneratedTests
