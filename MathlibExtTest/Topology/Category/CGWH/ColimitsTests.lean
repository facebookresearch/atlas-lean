/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Colimits

/-!
# Tests for colimits in CGWH

The tests cover the reflected formula, raw comparison and its characteristic
equation, coproducts, pushouts along closed embeddings, universe polymorphism,
and the absence of stronger creation or adjunction instances.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w r

open CategoryTheory CategoryTheory.Limits Topology

namespace MathlibExtTest.Topology.Category.CGWH.ColimitsTests

section Instances

example : HasColimitsOfSize.{v, v} CGWH.{u, v} := inferInstance

example : HasColimitsOfSize.{0, 0} CGWH.{0, 0} := inferInstance

example : HasColimitsOfSize.{1, 1} CGWH.{1, 1} := inferInstance

example : HasColimitsOfSize.{1, 1} CGWH.{0, 1} := inferInstance

example : HasColimitsOfSize.{0, 0} CGWH.{1, 0} := inferInstance

end Instances

section GeneralColimit

variable {J : Type v} [Category.{v} J]
  (F G : J ⥤ CGWH.{u, v}) (a : F ⟶ G) (j : J)

example : CGWH.weakHausdorffification.obj
      (Limits.colimit (F ⋙ CGWH.cgwhToCompactlyGenerated)) ≅
    Limits.colimit F :=
  CGWH.colimit F

example : Limits.colimit (F ⋙ CGWH.cgwhToTop) ⟶
    CGWH.cgwhToTop.obj (Limits.colimit F) :=
  CGWH.colimitComparisonFromTop F

example : Limits.colimit.ι (F ⋙ CGWH.cgwhToTop) j ≫
      CGWH.colimitComparisonFromTop F =
    CGWH.cgwhToTop.map (Limits.colimit.ι F j) :=
  CGWH.colimitComparisonFromTop_ι F j

example : Limits.colimMap
      (Functor.whiskerRight a CGWH.cgwhToTop) ≫
      CGWH.colimitComparisonFromTop G =
    CGWH.colimitComparisonFromTop F ≫
      CGWH.cgwhToTop.map (Limits.colimMap a) :=
  CGWH.colimitComparisonFromTop_naturality a

example : IsHomeomorph (CGWH.colimitComparisonFromTop F) ↔
    UWeakHausdorffSpace.{u} ↥(Limits.colimit (F ⋙ CGWH.cgwhToTop)) :=
  CGWH.colimitComparisonFromTop_isHomeomorph_iff F

example (h : UWeakHausdorffSpace.{u}
    ↥(Limits.colimit (F ⋙ CGWH.cgwhToTop))) :
    IsHomeomorph (CGWH.colimitComparisonFromTop F) :=
  (CGWH.colimitComparisonFromTop_isHomeomorph_iff F).2 h

example (h : IsHomeomorph (CGWH.colimitComparisonFromTop F)) :
    UWeakHausdorffSpace.{u}
      ↥(Limits.colimit (F ⋙ CGWH.cgwhToTop)) :=
  (CGWH.colimitComparisonFromTop_isHomeomorph_iff F).1 h

end GeneralColimit

section ArbitraryUniverseColimit

variable {J : Type w} [Category.{r} J]
  (F : J ⥤ CGWH.{u, v})
  [HasColimit (F ⋙ CGWH.cgwhToCompactlyGenerated)] [HasColimit F]

example (z : ↥(Limits.colimit F)) :
    ∃ (j : J) (x : ↥(F.obj j)), Limits.colimit.ι F j x = z :=
  CGWH.colimit_exists_rep F z

end ArbitraryUniverseColimit

section DiagramClients

variable
  (F₀ : Discrete PEmpty ⥤ CGWH.{u, v})
  (F₁ : Discrete PUnit ⥤ CGWH.{u, v})
  (Fpar : ULiftHom.{v} (ULift.{v} WalkingParallelPair) ⥤
    CGWH.{u, v})

example : Limits.colimit (F₀ ⋙ CGWH.cgwhToTop) ⟶
    CGWH.cgwhToTop.obj (Limits.colimit F₀) :=
  CGWH.colimitComparisonFromTop F₀

example : Limits.colimit (F₁ ⋙ CGWH.cgwhToTop) ⟶
    CGWH.cgwhToTop.obj (Limits.colimit F₁) :=
  CGWH.colimitComparisonFromTop F₁

example : Limits.colimit (Fpar ⋙ CGWH.cgwhToTop) ⟶
    CGWH.cgwhToTop.obj (Limits.colimit Fpar) :=
  CGWH.colimitComparisonFromTop Fpar

end DiagramClients

section Coproducts

variable {I : Type v} (X : I → CGWH.{u, v})

example : (∐ fun i => CGWH.cgwhToTop.obj (X i)) ≅
    CGWH.cgwhToTop.obj (∐ X) :=
  CGWH.coproductComparisonIso X

example : (CGWH.coproductComparisonIso X).hom ≫
    (CGWH.coproductComparisonIso X).inv =
      𝟙 (∐ fun i => CGWH.cgwhToTop.obj (X i)) :=
  (CGWH.coproductComparisonIso X).hom_inv_id

example : (CGWH.coproductComparisonIso X).inv ≫
    (CGWH.coproductComparisonIso X).hom =
      𝟙 (CGWH.cgwhToTop.obj (∐ X)) :=
  (CGWH.coproductComparisonIso X).inv_hom_id

end Coproducts

section ClosedPushouts

variable {W X Y : CGWH.{u, v}} (i : W ⟶ X) (f : W ⟶ Y)
  (hi : IsClosedEmbedding
    (ConcreteCategory.hom (CGWH.cgwhToTop.map i)))

example : pushout (CGWH.cgwhToTop.map i) (CGWH.cgwhToTop.map f) ≅
    CGWH.cgwhToTop.obj (pushout i f) :=
  CGWH.pushoutClosedComparisonIso i f hi

example : pushout.inl (CGWH.cgwhToTop.map i)
      (CGWH.cgwhToTop.map f) ≫
      (CGWH.pushoutClosedComparisonIso i f hi).hom =
    CGWH.cgwhToTop.map (pushout.inl i f) :=
  CGWH.pushoutClosedComparisonIso_hom_inl i f hi

example : pushout.inr (CGWH.cgwhToTop.map i)
      (CGWH.cgwhToTop.map f) ≫
      (CGWH.pushoutClosedComparisonIso i f hi).hom =
    CGWH.cgwhToTop.map (pushout.inr i f) :=
  CGWH.pushoutClosedComparisonIso_hom_inr i f hi

example : (CGWH.pushoutClosedComparisonIso i f hi).hom ≫
    (CGWH.pushoutClosedComparisonIso i f hi).inv =
      𝟙 (pushout (CGWH.cgwhToTop.map i) (CGWH.cgwhToTop.map f)) :=
  (CGWH.pushoutClosedComparisonIso i f hi).hom_inv_id

example : (CGWH.pushoutClosedComparisonIso i f hi).inv ≫
    (CGWH.pushoutClosedComparisonIso i f hi).hom =
      𝟙 (CGWH.cgwhToTop.obj (pushout i f)) :=
  (CGWH.pushoutClosedComparisonIso i f hi).inv_hom_id

end ClosedPushouts

section UniverseMatrix

#check CGWH.colimit.{0, 0}
#check CGWH.colimit_exists_rep.{0, 0, 1, 1}
#check CGWH.colimitComparisonFromTop.{0, 0}
#check CGWH.colimitComparisonFromTop_ι.{0, 0}
#check CGWH.colimitComparisonFromTop_naturality.{0, 0}
#check CGWH.colimitComparisonFromTop_isHomeomorph_iff.{0, 0}
#check CGWH.coproductComparisonIso.{0, 0}
#check CGWH.pushoutClosedComparisonIso.{0, 0}
#check CGWH.pushoutClosedComparisonIso_hom_inl.{0, 0}
#check CGWH.pushoutClosedComparisonIso_hom_inr.{0, 0}

#check CGWH.colimit.{1, 1}
#check CGWH.colimitComparisonFromTop.{1, 1}
#check CGWH.colimitComparisonFromTop_ι.{1, 1}
#check CGWH.colimitComparisonFromTop_naturality.{1, 1}
#check CGWH.colimitComparisonFromTop_isHomeomorph_iff.{1, 1}
#check CGWH.coproductComparisonIso.{1, 1}
#check CGWH.pushoutClosedComparisonIso.{1, 1}
#check CGWH.pushoutClosedComparisonIso_hom_inl.{1, 1}
#check CGWH.pushoutClosedComparisonIso_hom_inr.{1, 1}

#check CGWH.colimit.{0, 1}
#check CGWH.colimitComparisonFromTop.{0, 1}
#check CGWH.colimitComparisonFromTop_ι.{0, 1}
#check CGWH.colimitComparisonFromTop_naturality.{0, 1}
#check CGWH.colimitComparisonFromTop_isHomeomorph_iff.{0, 1}
#check CGWH.coproductComparisonIso.{0, 1}
#check CGWH.pushoutClosedComparisonIso.{0, 1}
#check CGWH.pushoutClosedComparisonIso_hom_inl.{0, 1}
#check CGWH.pushoutClosedComparisonIso_hom_inr.{0, 1}

#check CGWH.colimit.{1, 0}
#check CGWH.colimitComparisonFromTop.{1, 0}
#check CGWH.colimitComparisonFromTop_ι.{1, 0}
#check CGWH.colimitComparisonFromTop_naturality.{1, 0}
#check CGWH.colimitComparisonFromTop_isHomeomorph_iff.{1, 0}
#check CGWH.coproductComparisonIso.{1, 0}
#check CGWH.pushoutClosedComparisonIso.{1, 0}
#check CGWH.pushoutClosedComparisonIso_hom_inl.{1, 0}
#check CGWH.pushoutClosedComparisonIso_hom_inr.{1, 0}
#check CGWH.colimit.{u, v}
#check CGWH.colimit_exists_rep.{u, v, w, r}
#check CGWH.colimitComparisonFromTop.{u, v}
#check CGWH.colimitComparisonFromTop_ι.{u, v}
#check CGWH.colimitComparisonFromTop_naturality.{u, v}
#check CGWH.colimitComparisonFromTop_isHomeomorph_iff.{u, v}
#check CGWH.coproductComparisonIso.{u, v}
#check CGWH.pushoutClosedComparisonIso.{u, v}
#check CGWH.pushoutClosedComparisonIso_hom_inl.{u, v}
#check CGWH.pushoutClosedComparisonIso_hom_inr.{u, v}

end UniverseMatrix

section NegativeBoundaries

variable {J : Type v} [Category.{v} J]
  (F : J ⥤ CGWH.{u, v})

example : True := by
  fail_if_success
    let _ : IsIso (CGWH.colimitComparisonFromTop F) := inferInstance
  fail_if_success
    let _ : CreatesColimitsOfSize.{v, v} CGWH.cgwhToTop := inferInstance
  fail_if_success
    let _ : CGWH.cgwhToTop.{u, v}.IsLeftAdjoint := inferInstance
  fail_if_success
    let _ : CGWH.cgwhToTop.{u, v}.IsRightAdjoint := inferInstance
  fail_if_success
    let _ : UWeakHausdorffSpace.{u}
      ↥(Limits.colimit (F ⋙ CGWH.cgwhToTop)) := inferInstance
  trivial

end NegativeBoundaries

#print axioms CGWH.colimit
#print axioms CGWH.colimit_exists_rep
#print axioms CGWH.colimitComparisonFromTop
#print axioms CGWH.colimitComparisonFromTop_ι
#print axioms CGWH.colimitComparisonFromTop_naturality
#print axioms CGWH.colimitComparisonFromTop_isHomeomorph_iff
#print axioms CGWH.coproductComparisonIso
#print axioms CGWH.pushoutClosedComparisonIso
#print axioms CGWH.pushoutClosedComparisonIso_hom_inl
#print axioms CGWH.pushoutClosedComparisonIso_hom_inr

end MathlibExtTest.Topology.Category.CGWH.ColimitsTests
