/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHPointCofibrant

/-!
# Tests for cofibrancy of the point in CGWH
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MorphismProperty
open HomotopicalAlgebra

namespace MathlibExtTest.CGWH.PointCofibrantTests

section PublicSurface

#check CGWH.realizedBoundaryInclusion_zero_arrowIso
#check CGWH.point_isCofibrant

end PublicSurface

section ScopeOff

example : True := by
  fail_if_success
    have := (inferInstance : HomotopicalAlgebra.ModelCategory CGWH.{0, 0})
  trivial

end ScopeOff

section ArrowIso

example :
    Arrow.mk (CGWH.realizedBoundaryInclusion.{v, u} 0) ≅
      Arrow.mk (initial.to CGWH.point.{u, v}) :=
  CGWH.realizedBoundaryInclusion_zero_arrowIso

example :
    CGWH.realizedBoundaryInclusion_zero_arrowIso.{u, v}.hom.left =
      (SSet.toCGWHOfFinite_boundary_zero_isInitial.uniqueUpToIso
        initialIsInitial).hom := rfl

example :
    CGWH.realizedBoundaryInclusion_zero_arrowIso.{u, v}.hom.right =
      SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.hom := rfl

example :
    CGWH.realizedBoundaryInclusion_zero_arrowIso.{u, v}.inv.left =
      (SSet.toCGWHOfFinite_boundary_zero_isInitial.uniqueUpToIso
        initialIsInitial).inv := rfl

example :
    CGWH.realizedBoundaryInclusion_zero_arrowIso.{u, v}.inv.right =
      SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.inv := rfl

example :
    CGWH.realizedBoundaryInclusion_zero_arrowIso.{u, v}.hom.left ≫
        initial.to CGWH.point.{u, v} =
      CGWH.realizedBoundaryInclusion.{v, u} 0 ≫
        CGWH.realizedBoundaryInclusion_zero_arrowIso.{u, v}.hom.right :=
  CGWH.realizedBoundaryInclusion_zero_arrowIso.hom.w

example :
    CGWH.realizedBoundaryInclusion_zero_arrowIso.{u, v}.inv.left ≫
        CGWH.realizedBoundaryInclusion.{v, u} 0 =
      initial.to CGWH.point.{u, v} ≫
        CGWH.realizedBoundaryInclusion_zero_arrowIso.{u, v}.inv.right :=
  CGWH.realizedBoundaryInclusion_zero_arrowIso.inv.w

example :
    CGWH.realizedBoundaryInclusion_zero_arrowIso.{0, 0}.hom.left ≫
        initial.to CGWH.point.{0, 0} =
      CGWH.realizedBoundaryInclusion.{0, 0} 0 ≫
        CGWH.realizedBoundaryInclusion_zero_arrowIso.{0, 0}.hom.right :=
  CGWH.realizedBoundaryInclusion_zero_arrowIso.hom.w

example :
    CGWH.realizedBoundaryInclusion_zero_arrowIso.{1, 1}.hom.left ≫
        initial.to CGWH.point.{1, 1} =
      CGWH.realizedBoundaryInclusion.{1, 1} 0 ≫
        CGWH.realizedBoundaryInclusion_zero_arrowIso.{1, 1}.hom.right :=
  CGWH.realizedBoundaryInclusion_zero_arrowIso.hom.w

example :
    CGWH.realizedBoundaryInclusion_zero_arrowIso.{0, 1}.hom.left ≫
        initial.to CGWH.point.{0, 1} =
      CGWH.realizedBoundaryInclusion.{1, 0} 0 ≫
        CGWH.realizedBoundaryInclusion_zero_arrowIso.{0, 1}.hom.right :=
  CGWH.realizedBoundaryInclusion_zero_arrowIso.hom.w

example :
    CGWH.realizedBoundaryInclusion_zero_arrowIso.{1, 0}.hom.left ≫
        initial.to CGWH.point.{1, 0} =
      CGWH.realizedBoundaryInclusion.{0, 1} 0 ≫
        CGWH.realizedBoundaryInclusion_zero_arrowIso.{1, 0}.hom.right :=
  CGWH.realizedBoundaryInclusion_zero_arrowIso.hom.w

end ArrowIso

section GeneratedClass

example : CGWH.realizedBoundaryInclusions.{u, v}
    (CGWH.realizedBoundaryInclusion.{v, u} 0) :=
  CGWH.boundary_mem_realizedBoundaryInclusions 0

example : CGWH.realizedBoundaryInclusions.{u, v}.rlp.llp
    (CGWH.realizedBoundaryInclusion.{v, u} 0) :=
  CGWH.realizedBoundaryInclusions.le_llp_rlp _
    (CGWH.boundary_mem_realizedBoundaryInclusions 0)

example : TopCat.realizedBoundaryInclusions.{v}.rlp.llp
    (CGWH.cgwhToTop.{u, v}.map
      (CGWH.realizedBoundaryInclusion.{v, u} 0)) := by
  have hi : CGWH.realizedBoundaryInclusions.{u, v}.rlp.llp
      (CGWH.realizedBoundaryInclusion.{v, u} 0) :=
    CGWH.realizedBoundaryInclusions.le_llp_rlp _
      (CGWH.boundary_mem_realizedBoundaryInclusions 0)
  rw [CGWH.realizedBoundaryInclusions_rlp_llp] at hi
  rw [CompactlyGenerated.realizedBoundaryInclusions_rlp_llp] at hi
  exact hi

end GeneratedClass

section Selected

open scoped CGWH.modelCategory

#synth HomotopicalAlgebra.ModelCategory CGWH.{0, 0}
#synth HomotopicalAlgebra.ModelCategory CGWH.{1, 1}
#synth HomotopicalAlgebra.ModelCategory CGWH.{0, 1}
#synth HomotopicalAlgebra.ModelCategory CGWH.{1, 0}

example : cofibrations CGWH.{u, v}
    (CGWH.realizedBoundaryInclusion.{v, u} 0) := by
  have hi : CGWH.realizedBoundaryInclusions.{u, v}.rlp.llp
      (CGWH.realizedBoundaryInclusion.{v, u} 0) :=
    CGWH.realizedBoundaryInclusions.le_llp_rlp _
      (CGWH.boundary_mem_realizedBoundaryInclusions 0)
  have hiTop : TopCat.realizedBoundaryInclusions.{v}.rlp.llp
      (CGWH.cgwhToTop.{u, v}.map
        (CGWH.realizedBoundaryInclusion.{v, u} 0)) := by
    rw [CGWH.realizedBoundaryInclusions_rlp_llp] at hi
    rw [CompactlyGenerated.realizedBoundaryInclusions_rlp_llp] at hi
    exact hi
  change CGWH.modelCofibrations.{u, v}
    (CGWH.realizedBoundaryInclusion.{v, u} 0)
  change CompactlyGenerated.modelCofibrations.{u, v}
    (CGWH.cgwhToCompactlyGenerated.{u, v}.map
      (CGWH.realizedBoundaryInclusion.{v, u} 0))
  change TopCat.realizedBoundaryInclusions.{v}.rlp.llp
    (CompactlyGenerated.compactlyGeneratedToTop.{u, v}.map
      (CGWH.cgwhToCompactlyGenerated.{u, v}.map
        (CGWH.realizedBoundaryInclusion.{v, u} 0)))
  change TopCat.realizedBoundaryInclusions.{v}.rlp.llp
    (CGWH.cgwhToTop.{u, v}.map
      (CGWH.realizedBoundaryInclusion.{v, u} 0))
  exact hiTop

example : cofibrations CGWH.{u, v}
    (initial.to CGWH.point.{u, v}) := by
  apply ((cofibrations CGWH.{u, v}).arrow_mk_iso_iff
    CGWH.realizedBoundaryInclusion_zero_arrowIso).mp
  have hi : CGWH.realizedBoundaryInclusions.{u, v}.rlp.llp
      (CGWH.realizedBoundaryInclusion.{v, u} 0) :=
    CGWH.realizedBoundaryInclusions.le_llp_rlp _
      (CGWH.boundary_mem_realizedBoundaryInclusions 0)
  have hiTop : TopCat.realizedBoundaryInclusions.{v}.rlp.llp
      (CGWH.cgwhToTop.{u, v}.map
        (CGWH.realizedBoundaryInclusion.{v, u} 0)) := by
    rw [CGWH.realizedBoundaryInclusions_rlp_llp] at hi
    rw [CompactlyGenerated.realizedBoundaryInclusions_rlp_llp] at hi
    exact hi
  change CGWH.modelCofibrations.{u, v}
    (CGWH.realizedBoundaryInclusion.{v, u} 0)
  change CompactlyGenerated.modelCofibrations.{u, v}
    (CGWH.cgwhToCompactlyGenerated.{u, v}.map
      (CGWH.realizedBoundaryInclusion.{v, u} 0))
  change TopCat.realizedBoundaryInclusions.{v}.rlp.llp
    (CompactlyGenerated.compactlyGeneratedToTop.{u, v}.map
      (CGWH.cgwhToCompactlyGenerated.{u, v}.map
        (CGWH.realizedBoundaryInclusion.{v, u} 0)))
  change TopCat.realizedBoundaryInclusions.{v}.rlp.llp
    (CGWH.cgwhToTop.{u, v}.map
      (CGWH.realizedBoundaryInclusion.{v, u} 0))
  exact hiTop

example (h : cofibrations CGWH.{u, v}
    (initial.to CGWH.point.{u, v})) :
    cofibrations CGWH.{u, v}
      (CGWH.realizedBoundaryInclusion.{v, u} 0) :=
  ((cofibrations CGWH.{u, v}).arrow_mk_iso_iff
    CGWH.realizedBoundaryInclusion_zero_arrowIso).mpr h

example : IsCofibrant CGWH.point.{u, v} := CGWH.point_isCofibrant

example : IsCofibrant CGWH.point.{0, 0} := CGWH.point_isCofibrant
example : IsCofibrant CGWH.point.{1, 1} := CGWH.point_isCofibrant
example : IsCofibrant CGWH.point.{0, 1} := CGWH.point_isCofibrant
example : IsCofibrant CGWH.point.{1, 0} := CGWH.point_isCofibrant

example : Cofibration (initial.to CGWH.point.{u, v}) := by
  rw [← isCofibrant_iff]
  exact CGWH.point_isCofibrant

example : True := by
  fail_if_success
    let _ : IsCofibrant CGWH.point.{u, v} := inferInstance
  trivial

end Selected

section ScopeTeardown

example : True := by
  fail_if_success
    have := (inferInstance : HomotopicalAlgebra.ModelCategory CGWH.{0, 0})
  trivial

#guard_msgs (error, substring := true) in
#check CGWH.point_isCofibrant_of_isTerminal

end ScopeTeardown

#print axioms CGWH.realizedBoundaryInclusion_zero_arrowIso
#print axioms CGWH.point_isCofibrant

end MathlibExtTest.CGWH.PointCofibrantTests
