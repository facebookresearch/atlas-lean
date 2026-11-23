/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealization

/-!
# Tests for simplicial-set realization and singular adjunction in CGWH
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v

namespace MathlibExtTest.SSet.CGWHRealizationTests

#check SSet.toCGWH
#check SSet.realizationToTopIso
#check SSet.sSetCGWHAdj

section LiteralRealization

variable {K L : SSet.{v}} (f : K ⟶ L)

example : CGWH.cgwhToTop.obj (SSet.toCGWH.{u, v}.obj K) =
    SSet.toTop.obj K := rfl

example : CGWH.cgwhToTop.map (SSet.toCGWH.{u, v}.map f) =
    SSet.toTop.map f := rfl

example : SSet.toCGWH.{u, v}.map (𝟙 K) = 𝟙 _ :=
  SSet.toCGWH.map_id K

example {M : SSet.{v}} (g : L ⟶ M) :
    SSet.toCGWH.{u, v}.map (f ≫ g) =
      SSet.toCGWH.map f ≫ SSet.toCGWH.map g :=
  SSet.toCGWH.map_comp f g

end LiteralRealization

section Comparison

variable {K L : SSet.{v}} (f : K ⟶ L)

example : (SSet.realizationToTopIso.{u, v}.app K).hom = 𝟙 _ := rfl

example : (SSet.realizationToTopIso.{u, v}.app K).inv = 𝟙 _ := rfl

example :
    (SSet.toCGWH.{u, v} ⋙ CGWH.cgwhToTop.{u, v}).map f ≫
        (SSet.realizationToTopIso.{u, v}.app L).hom =
      (SSet.realizationToTopIso.{u, v}.app K).hom ≫ SSet.toTop.map f :=
  SSet.realizationToTopIso.{u, v}.hom.naturality f

example :
    SSet.toTop.map f ≫ (SSet.realizationToTopIso.{u, v}.app L).inv =
      (SSet.realizationToTopIso.{u, v}.app K).inv ≫
        (SSet.toCGWH.{u, v} ⋙ CGWH.cgwhToTop.{u, v}).map f :=
  SSet.realizationToTopIso.{u, v}.inv.naturality f

end Comparison

section Adjunction

variable (K : SSet.{v}) (X : CGWH.{u, v})

example (f : SSet.toCGWH.{u, v}.obj K ⟶ X) :
    SSet.sSetCGWHAdj.{u, v}.homEquiv K X f =
      sSetTopAdj.homEquiv K (CGWH.cgwhToTop.obj X)
        ((SSet.realizationToTopIso.{u, v}.app K).inv ≫
          CGWH.cgwhToTop.{u, v}.map f) := by
  rw [SSet.sSetCGWHAdj,
    Adjunction.restrictFullyFaithful_homEquiv_apply]
  rfl

example (f : SSet.toCGWH.{u, v}.obj K ⟶ X) :
    (SSet.sSetCGWHAdj.{u, v}.homEquiv K X).symm
      (SSet.sSetCGWHAdj.{u, v}.homEquiv K X f) = f :=
  (SSet.sSetCGWHAdj.{u, v}.homEquiv K X).symm_apply_apply f

example (g : K ⟶ TopCat.toSSet.obj (CGWH.cgwhToTop.obj X)) :
    SSet.sSetCGWHAdj.{u, v}.homEquiv K X
      ((SSet.sSetCGWHAdj.{u, v}.homEquiv K X).symm g) = g :=
  (SSet.sSetCGWHAdj.{u, v}.homEquiv K X).apply_symm_apply g

example : SSet.sSetCGWHAdj.{u, v}.unit.app K =
    sSetTopAdj.unit.app K ≫
      TopCat.toSSet.map
        (SSet.realizationToTopIso.{u, v}.app K).inv := by
  simpa [SSet.sSetCGWHAdj] using
    sSetTopAdj.map_restrictFullyFaithful_unit_app
      (Functor.FullyFaithful.id SSet.{v})
      CGWH.fullyFaithfulCgwhToTop
      ((Functor.leftUnitor SSet.toTop) ≪≫
        SSet.realizationToTopIso.{u, v}.symm)
      ((Functor.rightUnitor
        (CGWH.cgwhToTop.{u, v} ⋙ TopCat.toSSet.{v})).symm) K

example : CGWH.cgwhToTop.{u, v}.map
    (SSet.sSetCGWHAdj.{u, v}.counit.app X) =
    (SSet.realizationToTopIso.{u, v}.app
        (TopCat.toSSet.obj (CGWH.cgwhToTop.obj X))).hom ≫
      sSetTopAdj.counit.app (CGWH.cgwhToTop.obj X) := by
  simpa [SSet.sSetCGWHAdj] using
    sSetTopAdj.map_restrictFullyFaithful_counit_app
      (Functor.FullyFaithful.id SSet.{v})
      CGWH.fullyFaithfulCgwhToTop
      ((Functor.leftUnitor SSet.toTop) ≪≫
        SSet.realizationToTopIso.{u, v}.symm)
      ((Functor.rightUnitor
        (CGWH.cgwhToTop.{u, v} ⋙ TopCat.toSSet.{v})).symm) X

example : SSet.toCGWH.{u, v}.map
      (SSet.sSetCGWHAdj.{u, v}.unit.app K) ≫
    SSet.sSetCGWHAdj.{u, v}.counit.app
      (SSet.toCGWH.{u, v}.obj K) = 𝟙 _ :=
  SSet.sSetCGWHAdj.{u, v}.left_triangle_components K

example : SSet.sSetCGWHAdj.{u, v}.unit.app
      ((CGWH.cgwhToTop.{u, v} ⋙ TopCat.toSSet.{v}).obj X) ≫
    (CGWH.cgwhToTop.{u, v} ⋙ TopCat.toSSet.{v}).map
      (SSet.sSetCGWHAdj.{u, v}.counit.app X) = 𝟙 _ :=
  SSet.sSetCGWHAdj.{u, v}.right_triangle_components X

end Adjunction

section UniverseMatrix

#check SSet.toCGWH.{0, 0}
#check SSet.realizationToTopIso.{0, 0}
#check SSet.sSetCGWHAdj.{0, 0}

#check SSet.toCGWH.{1, 1}
#check SSet.realizationToTopIso.{1, 1}
#check SSet.sSetCGWHAdj.{1, 1}

#check SSet.toCGWH.{0, 1}
#check SSet.realizationToTopIso.{0, 1}
#check SSet.sSetCGWHAdj.{0, 1}

#check SSet.toCGWH.{1, 0}
#check SSet.realizationToTopIso.{1, 0}
#check SSet.sSetCGWHAdj.{1, 0}

end UniverseMatrix

section Negative

variable (K : SSet.{v})

example : True := by
  fail_if_success
    let _ : UCompactlyGeneratedSpace.{u} (SSet.toTop.obj K) := inferInstance
  fail_if_success
    let _ : UWeakHausdorffSpace.{u} (SSet.toTop.obj K) := inferInstance
  fail_if_success
    let _ : CGWH.cgwhToTop.{u, v}.IsLeftAdjoint := inferInstance
  fail_if_success
    let _ : CGWH.cgwhToTop.{u, v}.IsRightAdjoint := inferInstance
  trivial

#guard_msgs (error, substring := true) in
#check SSet.pointedToCGWH

#guard_msgs (error, substring := true) in
#check SSet.toCGWH_prodComparison

#guard_msgs (error, substring := true) in
#check SSet.sSetCGWHQuillenAdj

#guard_msgs (error, substring := true) in
#check CGWH.modelCategory

#guard_msgs (error, substring := true) in
#check CGWH.classifyingBar

end Negative

#print axioms SSet.toCGWH
#print axioms SSet.realizationToTopIso
#print axioms SSet.sSetCGWHAdj

end MathlibExtTest.SSet.CGWHRealizationTests
