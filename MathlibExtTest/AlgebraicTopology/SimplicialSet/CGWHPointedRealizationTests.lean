/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHPointedRealization

/-!
# Tests for pointed simplicial-set realization in CGWH
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u v

namespace MathlibExtTest.SSet.CGWHPointedRealizationTests

section ZeroSimplexIso

example : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅
    CGWH.point.{u, v} :=
  SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}

example :
    (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).hom ≫
        (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv =
      𝟙 _ :=
  (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).hom_inv_id

example :
    (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
        (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).hom =
      𝟙 _ :=
  (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv_hom_id

end ZeroSimplexIso

section LeftFunctor

variable {A B : Under (Δ[0] : SSet.{v})} (f : A ⟶ B)

example : (SSet.pointedToCGWH.{u, v}.obj A).right =
    SSet.toCGWH.{u, v}.obj A.right := rfl

example : (SSet.pointedToCGWH.{u, v}.obj A).hom =
    (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
      SSet.toCGWH.{u, v}.map A.hom := rfl

example : (SSet.pointedToCGWH.{u, v}.map f).right =
    SSet.toCGWH.{u, v}.map f.right := rfl

example :
    (CGWH.cgwhToTop.{u, v}.map
        ((SSet.pointedToCGWH.{u, v}.obj A).hom) ≫
      (SSet.realizationToTopIso.{u, v}.app A.right).hom)
        PUnit.unit =
      SSet.realizedVertex (SSet.yonedaEquiv A.hom) :=
  SSet.pointedToCGWH_basepoint.{u, v} A

example :
    SSet.toTop.map f.right
        (SSet.realizedVertex (SSet.yonedaEquiv A.hom)) =
      SSet.realizedVertex (SSet.yonedaEquiv B.hom) := by
  rw [← SSet.realizedVertex_naturality]
  congr 1
  rw [← SSet.yonedaEquiv_comp, Under.w f]

end LeftFunctor

section RightFunctor

variable {A B : Under CGWH.point.{u, v}} (f : A ⟶ B)

example : (CGWH.pointedToSSet.{u, v}.obj A).right =
    TopCat.toSSet.{v}.obj (CGWH.cgwhToTop.{u, v}.obj A.right) := rfl

example : (CGWH.pointedToSSet.{u, v}.obj A).hom =
    SSet.sSetCGWHAdj.{u, v}.unit.app (Δ[0] : SSet.{v}) ≫
      (CGWH.cgwhToTop.{u, v} ⋙ TopCat.toSSet.{v}).map
        ((SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).hom ≫
          A.hom) := rfl

example : (CGWH.pointedToSSet.{u, v}.map f).right =
    (CGWH.cgwhToTop.{u, v} ⋙ TopCat.toSSet.{v}).map f.right := rfl

end RightFunctor

section Adjunction

variable (A : Under (Δ[0] : SSet.{v}))
  (B : Under CGWH.point.{u, v})

example (f : SSet.pointedToCGWH.{u, v}.obj A ⟶ B) :
    (SSet.pointedToCGWHAdjunction.{u, v}.homEquiv A B).symm
        (SSet.pointedToCGWHAdjunction.{u, v}.homEquiv A B f) = f :=
  (SSet.pointedToCGWHAdjunction.{u, v}.homEquiv A B).symm_apply_apply f

example (g : A ⟶ CGWH.pointedToSSet.{u, v}.obj B) :
    SSet.pointedToCGWHAdjunction.{u, v}.homEquiv A B
        ((SSet.pointedToCGWHAdjunction.{u, v}.homEquiv A B).symm g) = g :=
  (SSet.pointedToCGWHAdjunction.{u, v}.homEquiv A B).apply_symm_apply g

example {A' : Under (Δ[0] : SSet.{v})} (f : A ⟶ A') :
    f ≫ SSet.pointedToCGWHAdjunction.{u, v}.unit.app A' =
      SSet.pointedToCGWHAdjunction.{u, v}.unit.app A ≫
        CGWH.pointedToSSet.{u, v}.map
          (SSet.pointedToCGWH.{u, v}.map f) :=
  SSet.pointedToCGWHAdjunction.{u, v}.unit.naturality f

example {B' : Under CGWH.point.{u, v}} (f : B ⟶ B') :
    SSet.pointedToCGWH.{u, v}.map
        (CGWH.pointedToSSet.{u, v}.map f) ≫
      SSet.pointedToCGWHAdjunction.{u, v}.counit.app B' =
    SSet.pointedToCGWHAdjunction.{u, v}.counit.app B ≫ f :=
  SSet.pointedToCGWHAdjunction.{u, v}.counit.naturality f

example : SSet.pointedToCGWH.{u, v}.map
      (SSet.pointedToCGWHAdjunction.{u, v}.unit.app A) ≫
    SSet.pointedToCGWHAdjunction.{u, v}.counit.app
      (SSet.pointedToCGWH.{u, v}.obj A) = 𝟙 _ :=
  SSet.pointedToCGWHAdjunction.{u, v}.left_triangle_components A

example : SSet.pointedToCGWHAdjunction.{u, v}.unit.app
      (CGWH.pointedToSSet.{u, v}.obj B) ≫
    CGWH.pointedToSSet.{u, v}.map
      (SSet.pointedToCGWHAdjunction.{u, v}.counit.app B) = 𝟙 _ :=
  SSet.pointedToCGWHAdjunction.{u, v}.right_triangle_components B

end Adjunction

section UniverseMatrix

#check SSet.pointedToCGWH.{0, 0}
#check CGWH.pointedToSSet.{0, 0}
#check SSet.pointedToCGWHAdjunction.{0, 0}
#check SSet.pointedToCGWH_basepoint.{0, 0}

#check SSet.pointedToCGWH.{1, 1}
#check CGWH.pointedToSSet.{1, 1}
#check SSet.pointedToCGWHAdjunction.{1, 1}
#check SSet.pointedToCGWH_basepoint.{1, 1}

#check SSet.pointedToCGWH.{0, 1}
#check CGWH.pointedToSSet.{0, 1}
#check SSet.pointedToCGWHAdjunction.{0, 1}
#check SSet.pointedToCGWH_basepoint.{0, 1}

#check SSet.pointedToCGWH.{1, 0}
#check CGWH.pointedToSSet.{1, 0}
#check SSet.pointedToCGWHAdjunction.{1, 0}
#check SSet.pointedToCGWH_basepoint.{1, 0}

#check SSet.pointedToCGWH.{u, v}
#check CGWH.pointedToSSet.{u, v}
#check SSet.pointedToCGWHAdjunction.{u, v}
#check SSet.pointedToCGWH_basepoint.{u, v}

end UniverseMatrix

section NegativeBoundaries

#guard_msgs (error, substring := true) in
#check SSet.pointedToCGWH_costar

#guard_msgs (error, substring := true) in
#check PointedCGWH

#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalences_pointedToCGWH

#guard_msgs (error, substring := true) in
#check SSet.sSetCGWHQuillenAdj

#guard_msgs (error, substring := true) in
#check CGWH.modelCategory

#guard_msgs (error, substring := true) in
#check CGWH.classifyingBar

end NegativeBoundaries

#print axioms SSet.pointedToCGWH
#print axioms CGWH.pointedToSSet
#print axioms SSet.pointedToCGWHAdjunction
#print axioms SSet.pointedToCGWH_basepoint

end MathlibExtTest.SSet.CGWHPointedRealizationTests
