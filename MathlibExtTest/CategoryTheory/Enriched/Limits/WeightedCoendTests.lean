/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoend

/-!
# Tests for enriched weighted coends

These tests bind every public declaration through the sole provider import.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Limits

open scoped MonoidalClosed

universe u

namespace PublicEndpointClients

variable {V : Type u} [Category.{u} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
variable {A B : Type u} [Category.{u} A] [Category.{u} B]
  [EnrichedOrdinaryCategory V A] [EnrichedOrdinaryCategory V B]
variable [HasColimitsOfSize.{u, u} V]
variable (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V)
  (U : EnrichedFunctor V Bᵒᵖ V) (G : EnrichedFunctor V B V)

example (c : A) : EnrichedFunctor V A V :=
  EnrichedFunctor.covariantRepresentable V A c

example (c : A) : EnrichedFunctor V Aᵒᵖ V :=
  EnrichedFunctor.contravariantRepresentable V A c

example : V := CategoryTheory.Enriched.weightedCoend W F

example (a : A) :
    W.obj (Opposite.op a) ⊗ F.obj a ⟶
      CategoryTheory.Enriched.weightedCoend W F :=
  CategoryTheory.Enriched.weightedCoend.ι W F a

example (a b : A) :=
  CategoryTheory.Enriched.weightedCoend.condition W F a b

example {X : V}
    (k : ∀ a, W.obj (Opposite.op a) ⊗ F.obj a ⟶ X)
    (h : ∀ a b,
      ((α_ (W.obj (Opposite.op b)) (a ⟶[V] b) (F.obj a)).inv ≫
          (MonoidalClosed.uncurry
            (W.map (Opposite.op b) (Opposite.op a)) ⊗ₘ
              𝟙 (F.obj a))) ≫ k a =
        (W.obj (Opposite.op b) ◁
          ((β_ (a ⟶[V] b) (F.obj a)).hom ≫
            MonoidalClosed.uncurry (F.map a b))) ≫ k b) :
    CategoryTheory.Enriched.weightedCoend W F ⟶ X :=
  CategoryTheory.Enriched.weightedCoend.desc W F k h

example {X : V}
    (k : ∀ a, W.obj (Opposite.op a) ⊗ F.obj a ⟶ X)
    (h : ∀ a b,
      ((α_ (W.obj (Opposite.op b)) (a ⟶[V] b) (F.obj a)).inv ≫
          (MonoidalClosed.uncurry
            (W.map (Opposite.op b) (Opposite.op a)) ⊗ₘ
              𝟙 (F.obj a))) ≫ k a =
        (W.obj (Opposite.op b) ◁
          ((β_ (a ⟶[V] b) (F.obj a)).hom ≫
            MonoidalClosed.uncurry (F.map a b))) ≫ k b)
    (a : A) :=
  CategoryTheory.Enriched.weightedCoend.ι_desc W F k h a

example {X : V}
    {f g : CategoryTheory.Enriched.weightedCoend W F ⟶ X}
    (h : ∀ a,
      CategoryTheory.Enriched.weightedCoend.ι W F a ≫ f =
        CategoryTheory.Enriched.weightedCoend.ι W F a ≫ g) :
    f = g :=
  CategoryTheory.Enriched.weightedCoend.hom_ext W F h

example (hsep : IsSeparator (𝟙_ V))
    {W' : EnrichedFunctor V Aᵒᵖ V} (t : W ⟶ W') :
    CategoryTheory.Enriched.weightedCoend W F ⟶
      CategoryTheory.Enriched.weightedCoend W' F :=
  CategoryTheory.Enriched.weightedCoend.mapWeight F t hsep

example (hsep : IsSeparator (𝟙_ V))
    {W' : EnrichedFunctor V Aᵒᵖ V} (t : W ⟶ W') (a : A) :=
  CategoryTheory.Enriched.weightedCoend.mapWeight_ι F t hsep a

example (hsep : IsSeparator (𝟙_ V))
    {F' : EnrichedFunctor V A V} (t : F ⟶ F') :
    CategoryTheory.Enriched.weightedCoend W F ⟶
      CategoryTheory.Enriched.weightedCoend W F' :=
  CategoryTheory.Enriched.weightedCoend.mapDiagram W t hsep

example (hsep : IsSeparator (𝟙_ V))
    {F' : EnrichedFunctor V A V} (t : F ⟶ F') (a : A) :=
  CategoryTheory.Enriched.weightedCoend.mapDiagram_ι W t hsep a

example (hsep : IsSeparator (𝟙_ V)) :
    CategoryTheory.Enriched.weightedCoend.mapWeight F (𝟙 W) hsep =
      𝟙 (CategoryTheory.Enriched.weightedCoend W F) :=
  CategoryTheory.Enriched.weightedCoend.mapWeight_id W F hsep

example (hsep : IsSeparator (𝟙_ V))
    {W₁ W₂ : EnrichedFunctor V Aᵒᵖ V}
    (t₀₁ : W ⟶ W₁) (t₁₂ : W₁ ⟶ W₂) :
    CategoryTheory.Enriched.weightedCoend.mapWeight F (t₀₁ ≫ t₁₂) hsep =
      CategoryTheory.Enriched.weightedCoend.mapWeight F t₀₁ hsep ≫
        CategoryTheory.Enriched.weightedCoend.mapWeight F t₁₂ hsep :=
  CategoryTheory.Enriched.weightedCoend.mapWeight_comp F t₀₁ t₁₂ hsep

example (hsep : IsSeparator (𝟙_ V)) :
    CategoryTheory.Enriched.weightedCoend.mapDiagram W (𝟙 F) hsep =
      𝟙 (CategoryTheory.Enriched.weightedCoend W F) :=
  CategoryTheory.Enriched.weightedCoend.mapDiagram_id W F hsep

example (hsep : IsSeparator (𝟙_ V))
    {F₁ F₂ : EnrichedFunctor V A V}
    (t₀₁ : F ⟶ F₁) (t₁₂ : F₁ ⟶ F₂) :
    CategoryTheory.Enriched.weightedCoend.mapDiagram W (t₀₁ ≫ t₁₂) hsep =
      CategoryTheory.Enriched.weightedCoend.mapDiagram W t₀₁ hsep ≫
        CategoryTheory.Enriched.weightedCoend.mapDiagram W t₁₂ hsep :=
  CategoryTheory.Enriched.weightedCoend.mapDiagram_comp W t₀₁ t₁₂ hsep

example (c : A) :
    CategoryTheory.Enriched.weightedCoend
        (EnrichedFunctor.contravariantRepresentable V A c) F ≅
      F.obj c :=
  CategoryTheory.Enriched.weightedCoend.coyonedaIso F c

/- The obsolete four-functor, separable-only Fubini call must not elaborate. -/
example : True := by
  fail_if_success
    have _e := CategoryTheory.Enriched.weightedCoend.fubiniIso W F U G
  trivial

/- Implementation helpers and the private Products import stay outside the
sole-import client surface. -/
example : True := by
  fail_if_success
    have _ := CategoryTheory.Enriched.coendTarget
  fail_if_success
    have _ := CategoryTheory.Enriched.weightRelation
  fail_if_success
    have _ := CategoryTheory.Enriched.gradedNatApp
  fail_if_success
    have _ := @CategoryTheory.Enriched.eHomProductIso
  trivial

end PublicEndpointClients

namespace GradedEndpointClients

universe uV vV uA vA

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
variable {A : Type uA} [Category.{vA} A] [EnrichedOrdinaryCategory V A]
variable [HasColimitsOfSize.{uA, uA} V] [HasCoequalizers V]
variable (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V)

example {W' : EnrichedFunctor V Aᵒᵖ V}
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W W') :
    CategoryTheory.Enriched.weightedCoend W F ⟶
      CategoryTheory.Enriched.weightedCoend W' F :=
  CategoryTheory.Enriched.weightedCoend.mapWeightGraded F t

example {W' : EnrichedFunctor V Aᵒᵖ V}
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W W') (a : A) :
    CategoryTheory.Enriched.weightedCoend.ι W F a ≫
        CategoryTheory.Enriched.weightedCoend.mapWeightGraded F t =
      ((eHomEquiv V).symm (t.app (Opposite.op a)) ⊗ₘ 𝟙 (F.obj a)) ≫
        CategoryTheory.Enriched.weightedCoend.ι W' F a :=
  CategoryTheory.Enriched.weightedCoend.mapWeightGraded_ι F t a

example {F' : EnrichedFunctor V A V}
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F') :
    CategoryTheory.Enriched.weightedCoend W F ⟶
      CategoryTheory.Enriched.weightedCoend W F' :=
  CategoryTheory.Enriched.weightedCoend.mapDiagramGraded W t

example {F' : EnrichedFunctor V A V}
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F') (a : A) :
    CategoryTheory.Enriched.weightedCoend.ι W F a ≫
        CategoryTheory.Enriched.weightedCoend.mapDiagramGraded W t =
      (𝟙 (W.obj (Opposite.op a)) ⊗ₘ (eHomEquiv V).symm (t.app a)) ≫
        CategoryTheory.Enriched.weightedCoend.ι W F' a :=
  CategoryTheory.Enriched.weightedCoend.mapDiagramGraded_ι W t a

example :
    CategoryTheory.Enriched.weightedCoend.mapWeightGraded F
        (GradedNatTrans.unitId W) =
      𝟙 (CategoryTheory.Enriched.weightedCoend W F) :=
  CategoryTheory.Enriched.weightedCoend.mapWeightGraded_id W F

example {W₁ W₂ : EnrichedFunctor V Aᵒᵖ V}
    (t₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W W₁)
    (t₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W₁ W₂) :
    CategoryTheory.Enriched.weightedCoend.mapWeightGraded F
        (GradedNatTrans.unitComp t₀₁ t₁₂) =
      CategoryTheory.Enriched.weightedCoend.mapWeightGraded F t₀₁ ≫
        CategoryTheory.Enriched.weightedCoend.mapWeightGraded F t₁₂ :=
  CategoryTheory.Enriched.weightedCoend.mapWeightGraded_comp F t₀₁ t₁₂

example :
    CategoryTheory.Enriched.weightedCoend.mapDiagramGraded W
        (GradedNatTrans.unitId F) =
      𝟙 (CategoryTheory.Enriched.weightedCoend W F) :=
  CategoryTheory.Enriched.weightedCoend.mapDiagramGraded_id W F

example {F₁ F₂ : EnrichedFunctor V A V}
    (t₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F₁)
    (t₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₁ F₂) :
    CategoryTheory.Enriched.weightedCoend.mapDiagramGraded W
        (GradedNatTrans.unitComp t₀₁ t₁₂) =
      CategoryTheory.Enriched.weightedCoend.mapDiagramGraded W t₀₁ ≫
        CategoryTheory.Enriched.weightedCoend.mapDiagramGraded W t₁₂ :=
  CategoryTheory.Enriched.weightedCoend.mapDiagramGraded_comp W t₀₁ t₁₂

example {W' : EnrichedFunctor V Aᵒᵖ V}
    (_t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W W') : True := by
  fail_if_success
    have _hsep : IsSeparator (𝟙_ V) := by assumption
  fail_if_success
    exact (CategoryTheory.Enriched.weightedCoend.mapWeight F _t.toEnrichedNatTrans :
      CategoryTheory.Enriched.weightedCoend W F ⟶
        CategoryTheory.Enriched.weightedCoend W' F)
  fail_if_success
    exact (CategoryTheory.Enriched.weightedCoend.mapWeightGraded F _t :
      CategoryTheory.Enriched.weightedCoend W' F ⟶
        CategoryTheory.Enriched.weightedCoend W F)
  trivial

example {F' : EnrichedFunctor V A V}
    (_t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F') : True := by
  fail_if_success
    have _hsep : IsSeparator (𝟙_ V) := by assumption
  fail_if_success
    exact (CategoryTheory.Enriched.weightedCoend.mapDiagramGraded W _t :
      CategoryTheory.Enriched.weightedCoend W F' ⟶
        CategoryTheory.Enriched.weightedCoend W F)
  trivial

example (hsep : IsSeparator (𝟙_ V))
    {W' : EnrichedFunctor V Aᵒᵖ V} (t : W ⟶ W') :
    CategoryTheory.Enriched.weightedCoend.mapWeight F t hsep =
      CategoryTheory.Enriched.weightedCoend.mapWeightGraded F (t.toGradedNatTrans hsep) :=
  rfl

example (hsep : IsSeparator (𝟙_ V))
    {F' : EnrichedFunctor V A V} (t : F ⟶ F') :
    CategoryTheory.Enriched.weightedCoend.mapDiagram W t hsep =
      CategoryTheory.Enriched.weightedCoend.mapDiagramGraded W (t.toGradedNatTrans hsep) :=
  rfl

#check @CategoryTheory.Enriched.weightedCoend.mapWeightGraded.{0, 0, 1}
#check @CategoryTheory.Enriched.weightedCoend.mapDiagramGraded.{1, 1, 0}
#check @CategoryTheory.Enriched.weightedCoend.mapWeightGraded_id
#check @CategoryTheory.Enriched.weightedCoend.mapWeightGraded_comp
#check @CategoryTheory.Enriched.weightedCoend.mapDiagramGraded_id
#check @CategoryTheory.Enriched.weightedCoend.mapDiagramGraded_comp
#check @CategoryTheory.Enriched.weightedCoend.mapWeight_id
#check @CategoryTheory.Enriched.weightedCoend.mapWeight_comp
#check @CategoryTheory.Enriched.weightedCoend.mapDiagram_id
#check @CategoryTheory.Enriched.weightedCoend.mapDiagram_comp

#print axioms CategoryTheory.Enriched.weightedCoend.mapWeightGraded
#print axioms CategoryTheory.Enriched.weightedCoend.mapWeightGraded_ι
#print axioms CategoryTheory.Enriched.weightedCoend.mapDiagramGraded
#print axioms CategoryTheory.Enriched.weightedCoend.mapDiagramGraded_ι
#print axioms CategoryTheory.Enriched.weightedCoend.mapWeightGraded_id
#print axioms CategoryTheory.Enriched.weightedCoend.mapWeightGraded_comp
#print axioms CategoryTheory.Enriched.weightedCoend.mapDiagramGraded_id
#print axioms CategoryTheory.Enriched.weightedCoend.mapDiagramGraded_comp

end GradedEndpointClients

namespace MinimalFunctorialityClients

universe uV vV uA vA

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
variable {A : Type uA} [Category.{vA} A] [EnrichedOrdinaryCategory V A]
variable [HasCoproductsOfShape A V] [HasCoproductsOfShape (A × A) V]
  [HasCoequalizers V]
variable (W₀ W₁ W₂ : EnrichedFunctor V Aᵒᵖ V)
  (F₀ F₁ F₂ : EnrichedFunctor V A V)

example :
    CategoryTheory.Enriched.weightedCoend.mapWeightGraded F₀
        (GradedNatTrans.unitId W₀) =
      𝟙 (CategoryTheory.Enriched.weightedCoend W₀ F₀) :=
  CategoryTheory.Enriched.weightedCoend.mapWeightGraded_id W₀ F₀

example
    (t₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W₀ W₁)
    (t₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W₁ W₂) :
    CategoryTheory.Enriched.weightedCoend.mapWeightGraded F₀
        (GradedNatTrans.unitComp t₀₁ t₁₂) =
      CategoryTheory.Enriched.weightedCoend.mapWeightGraded F₀ t₀₁ ≫
        CategoryTheory.Enriched.weightedCoend.mapWeightGraded F₀ t₁₂ :=
  CategoryTheory.Enriched.weightedCoend.mapWeightGraded_comp F₀ t₀₁ t₁₂

example :
    CategoryTheory.Enriched.weightedCoend.mapDiagramGraded W₀
        (GradedNatTrans.unitId F₀) =
      𝟙 (CategoryTheory.Enriched.weightedCoend W₀ F₀) :=
  CategoryTheory.Enriched.weightedCoend.mapDiagramGraded_id W₀ F₀

example
    (t₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (t₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₁ F₂) :
    CategoryTheory.Enriched.weightedCoend.mapDiagramGraded W₀
        (GradedNatTrans.unitComp t₀₁ t₁₂) =
      CategoryTheory.Enriched.weightedCoend.mapDiagramGraded W₀ t₀₁ ≫
        CategoryTheory.Enriched.weightedCoend.mapDiagramGraded W₀ t₁₂ :=
  CategoryTheory.Enriched.weightedCoend.mapDiagramGraded_comp W₀ t₀₁ t₁₂

end MinimalFunctorialityClients

namespace PlainEnrichedClients

universe uV vV uA

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
variable {A : Type uA} [EnrichedCategory V A]
variable [HasCoproductsOfShape A V] [HasCoproductsOfShape (A × A) V]
  [HasCoequalizers V]
variable (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V)

example : V := CategoryTheory.Enriched.weightedCoend W F

example (a b : A) := CategoryTheory.Enriched.weightedCoend.condition W F a b

example : CategoryTheory.Enriched.weightedCoend W F ⟶
    CategoryTheory.Enriched.weightedCoend W F :=
  CategoryTheory.Enriched.weightedCoend.desc W F
    (CategoryTheory.Enriched.weightedCoend.ι W F)
    (CategoryTheory.Enriched.weightedCoend.condition W F)

example :
    CategoryTheory.Enriched.weightedCoend.desc W F
        (CategoryTheory.Enriched.weightedCoend.ι W F)
        (CategoryTheory.Enriched.weightedCoend.condition W F) = 𝟙 _ := by
  apply CategoryTheory.Enriched.weightedCoend.hom_ext W F
  intro a
  rw [CategoryTheory.Enriched.weightedCoend.ι_desc, Category.comp_id]

example {W' : EnrichedFunctor V Aᵒᵖ V}
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W W') :
    CategoryTheory.Enriched.weightedCoend W F ⟶
      CategoryTheory.Enriched.weightedCoend W' F :=
  CategoryTheory.Enriched.weightedCoend.mapWeightGraded F t

example {F' : EnrichedFunctor V A V}
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F') :
    CategoryTheory.Enriched.weightedCoend W F ⟶
      CategoryTheory.Enriched.weightedCoend W F' :=
  CategoryTheory.Enriched.weightedCoend.mapDiagramGraded W t

example :
    CategoryTheory.Enriched.weightedCoend.mapDiagramGraded W
        (GradedNatTrans.unitId F) = 𝟙 (CategoryTheory.Enriched.weightedCoend W F) :=
  CategoryTheory.Enriched.weightedCoend.mapDiagramGraded_id W F

example {F₁ F₂ : EnrichedFunctor V A V}
    (t₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F₁)
    (t₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₁ F₂) :
    CategoryTheory.Enriched.weightedCoend.mapDiagramGraded W
        (GradedNatTrans.unitComp t₀₁ t₁₂) =
      CategoryTheory.Enriched.weightedCoend.mapDiagramGraded W t₀₁ ≫
        CategoryTheory.Enriched.weightedCoend.mapDiagramGraded W t₁₂ :=
  CategoryTheory.Enriched.weightedCoend.mapDiagramGraded_comp W t₀₁ t₁₂

example (c : A) :
    CategoryTheory.Enriched.weightedCoend
        (EnrichedFunctor.contravariantRepresentable V A c) F ≅ F.obj c :=
  CategoryTheory.Enriched.weightedCoend.coyonedaIso F c

example (c a : A) :
    CategoryTheory.Enriched.weightedCoend.ι
        (EnrichedFunctor.contravariantRepresentable V A c) F a ≫
        (CategoryTheory.Enriched.weightedCoend.coyonedaIso F c).hom =
      (β_ (a ⟶[V] c) (F.obj a)).hom ≫ MonoidalClosed.uncurry (F.map a c) :=
  CategoryTheory.Enriched.weightedCoend.coyonedaIso_ι_hom F c a

example (c : A) :
    (CategoryTheory.Enriched.weightedCoend.coyonedaIso F c).inv =
      (λ_ (F.obj c)).inv ≫ (eId V c ⊗ₘ 𝟙 (F.obj c)) ≫
        CategoryTheory.Enriched.weightedCoend.ι
          (EnrichedFunctor.contravariantRepresentable V A c) F c :=
  CategoryTheory.Enriched.weightedCoend.coyonedaIso_inv F c

example : True := by
  fail_if_success exact (inferInstance : Category A)
  fail_if_success exact (inferInstance : IsSeparator (𝟙_ V))
  trivial

#print axioms CategoryTheory.Enriched.weightedCoend.coyonedaIso
#print axioms CategoryTheory.Enriched.weightedCoend.coyonedaIso_ι_hom
#print axioms CategoryTheory.Enriched.weightedCoend.coyonedaIso_inv

end PlainEnrichedClients

namespace MinimalCoyonedaClients

universe uV vV uA

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
variable {A : Type uA} [EnrichedCategory V A]

private abbrev target (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V) :
    A → V := fun a ↦ W.obj (Opposite.op a) ⊗ F.obj a

private abbrev source (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V) :
    A × A → V := fun ab ↦
      W.obj (Opposite.op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)

private abbrev left (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V)
    [HasCoproduct (source W F)] [HasCoproduct (target W F)] :
    (∐ source W F) ⟶ ∐ target W F :=
  Sigma.desc fun ab ↦
    ((α_ (W.obj (Opposite.op ab.2)) (ab.1 ⟶[V] ab.2) (F.obj ab.1)).inv ≫
      (MonoidalClosed.uncurry (W.map (Opposite.op ab.2) (Opposite.op ab.1)) ⊗ₘ
        𝟙 (F.obj ab.1))) ≫ Sigma.ι (target W F) ab.1

private abbrev right (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V)
    [HasCoproduct (source W F)] [HasCoproduct (target W F)] :
    (∐ source W F) ⟶ ∐ target W F :=
  Sigma.desc fun ab ↦
    (W.obj (Opposite.op ab.2) ◁
      ((β_ (ab.1 ⟶[V] ab.2) (F.obj ab.1)).hom ≫
        MonoidalClosed.uncurry (F.map ab.1 ab.2))) ≫ Sigma.ι (target W F) ab.2

variable (F : EnrichedFunctor V A V) (c : A)
variable
  [HasCoproduct (source (EnrichedFunctor.contravariantRepresentable V A c) F)]
  [HasCoproduct (target (EnrichedFunctor.contravariantRepresentable V A c) F)]
  [HasCoequalizer (left (EnrichedFunctor.contravariantRepresentable V A c) F)
    (right (EnrichedFunctor.contravariantRepresentable V A c) F)]

example (a : A) :
    CategoryTheory.Enriched.weightedCoend.ι
        (EnrichedFunctor.contravariantRepresentable V A c) F a ≫
        (CategoryTheory.Enriched.weightedCoend.coyonedaIso F c).hom =
      (β_ (a ⟶[V] c) (F.obj a)).hom ≫ MonoidalClosed.uncurry (F.map a c) :=
  CategoryTheory.Enriched.weightedCoend.coyonedaIso_ι_hom F c a

example :
    (CategoryTheory.Enriched.weightedCoend.coyonedaIso F c).inv =
      (λ_ (F.obj c)).inv ≫ (eId V c ⊗ₘ 𝟙 (F.obj c)) ≫
        CategoryTheory.Enriched.weightedCoend.ι
          (EnrichedFunctor.contravariantRepresentable V A c) F c :=
  CategoryTheory.Enriched.weightedCoend.coyonedaIso_inv F c

example : True := by
  fail_if_success exact (inferInstance : Category A)
  fail_if_success exact (inferInstance : HasCoproductsOfShape A V)
  fail_if_success exact (inferInstance : HasCoequalizers V)
  trivial

#check @CategoryTheory.Enriched.weightedCoend.coyonedaIso_ι_hom.{0, 0, 1}
#check @CategoryTheory.Enriched.weightedCoend.coyonedaIso_inv.{1, 1, 0}

end MinimalCoyonedaClients

namespace CoupledFubini

variable {V X L I J : Type u} [Category.{u} V] [MonoidalCategory V]
  [HasColimitsOfSize.{u, u} V]

variable
  (outerWeight : X → L → V)
  (innerWeight : I → J → X → V)
  (i : I) (j : J)

/- This deliberately nonseparable D1-shaped client models the two Day
weights `I(x ⊗ l, k)` and `I(i ⊗ j, x)`: the abstract
`outerWeight x l` and `innerWeight i j x` share the same `x`. Deleting
either occurrence changes the inferred integrand of the public endpoint. -/
private noncomputable def d1CoupledFubiniIso := by
  let T : X × L → V := fun xl ↦
    outerWeight xl.1 xl.2 ⊗ innerWeight i j xl.1
  let BT : X × (L × L) → V := fun _ ↦ ⊥_ V
  let b₀ : ∀ p, BT p ⟶ T (p.1, p.2.1) := fun _ ↦ initial.to _
  let b₁ : ∀ p, BT p ⟶ T (p.1, p.2.2) := fun _ ↦ initial.to _
  let R : (X × X) × L → V := fun _ ↦ ⊥_ V
  let BR : (X × X) × (L × L) → V := fun _ ↦ ⊥_ V
  let r₀ : ∀ p, BR p ⟶ R (p.1, p.2.1) := fun _ ↦ initial.to _
  let r₁ : ∀ p, BR p ⟶ R (p.1, p.2.2) := fun _ ↦ initial.to _
  let a₀ : ∀ p, R p ⟶ T (p.1.1, p.2) := fun _ ↦ initial.to _
  let a₁ : ∀ p, R p ⟶ T (p.1.2, p.2) := fun _ ↦ initial.to _
  exact CategoryTheory.Enriched.weightedCoend.fubiniIso
    T BT b₀ b₁ R BR r₀ r₁ a₀ a₁
    (fun _ _ ↦ initial.hom_ext _ _)
    (fun _ _ ↦ initial.hom_ext _ _)

example :
    (d1CoupledFubiniIso outerWeight innerWeight i j).hom ≫
        (d1CoupledFubiniIso outerWeight innerWeight i j).inv =
      𝟙 _ :=
  Iso.hom_inv_id _

example :
    (d1CoupledFubiniIso outerWeight innerWeight i j).inv ≫
        (d1CoupledFubiniIso outerWeight innerWeight i j).hom =
      𝟙 _ :=
  Iso.inv_hom_id _

/- The generator laws also elaborate with this coupled integrand, using only
an ordinary target category and the specified colimits. -/
private theorem d1CoupledFubiniGenerators :
    let T : X × L → V := fun xl ↦
      outerWeight xl.1 xl.2 ⊗ innerWeight i j xl.1
    let tT : X → L → V := fun x l ↦ T (x, l)
    let sT : X → L × L → V := fun _ _ ↦ ⊥_ V
    let lT (x : X) : (∐ sT x) ⟶ ∐ tT x :=
      Sigma.desc fun ll : L × L ↦
        initial.to (T (x, ll.1)) ≫ Sigma.ι (tT x) ll.1
    let rT (x : X) : (∐ sT x) ⟶ ∐ tT x :=
      Sigma.desc fun ll : L × L ↦
        initial.to (T (x, ll.2)) ≫ Sigma.ι (tT x) ll.2
    let KT : X → V := fun x ↦ coequalizer (lT x) (rT x)
    let jT : ∀ x l, T (x, l) ⟶ KT x := fun x l ↦
      Sigma.ι (tT x) l ≫ coequalizer.π (lT x) (rT x)
    let e := d1CoupledFubiniIso outerWeight innerWeight i j
    ∀ x l,
      ((jT x l ≫ (Sigma.ι KT x ≫ coequalizer.π _ _)) ≫ e.hom =
          Sigma.ι T (x, l) ≫ coequalizer.π _ _) ∧
        ((Sigma.ι T (x, l) ≫ coequalizer.π _ _) ≫ e.inv =
          jT x l ≫ (Sigma.ι KT x ≫ coequalizer.π _ _)) := by
  let T : X × L → V := fun xl ↦
    outerWeight xl.1 xl.2 ⊗ innerWeight i j xl.1
  let BT : X × (L × L) → V := fun _ ↦ ⊥_ V
  let b₀ : ∀ p, BT p ⟶ T (p.1, p.2.1) := fun _ ↦ initial.to _
  let b₁ : ∀ p, BT p ⟶ T (p.1, p.2.2) := fun _ ↦ initial.to _
  let R : (X × X) × L → V := fun _ ↦ ⊥_ V
  let BR : (X × X) × (L × L) → V := fun _ ↦ ⊥_ V
  let r₀ : ∀ p, BR p ⟶ R (p.1, p.2.1) := fun _ ↦ initial.to _
  let r₁ : ∀ p, BR p ⟶ R (p.1, p.2.2) := fun _ ↦ initial.to _
  let a₀ : ∀ p, R p ⟶ T (p.1.1, p.2) := fun _ ↦ initial.to _
  let a₁ : ∀ p, R p ⟶ T (p.1.2, p.2) := fun _ ↦ initial.to _
  exact CategoryTheory.Enriched.weightedCoend.fubiniIso_generators
    T BT b₀ b₁ R BR r₀ r₁ a₀ a₁
    (fun _ _ ↦ initial.hom_ext _ _)
    (fun _ _ ↦ initial.hom_ext _ _)


example (x : X) (l : L) :=
  (d1CoupledFubiniGenerators outerWeight innerWeight i j x l).1

example (x : X) (l : L) :=
  (d1CoupledFubiniGenerators outerWeight innerWeight i j x l).2

#check @CategoryTheory.Enriched.weightedCoend.fubiniIso_generators.{0, 0, 1, 1}
#print axioms CategoryTheory.Enriched.weightedCoend.fubiniIso
#print axioms CategoryTheory.Enriched.weightedCoend.fubiniIso_generators

end CoupledFubini


namespace ParticularGradedVarianceClients

open CategoryTheory.Enriched Opposite

universe uV vV uA

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
variable {A : Type uA} [EnrichedCategory V A]

section Identity

variable (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V)
variable [HasCoproduct (weightedCoend.relations W F)]
  [HasCoproduct (weightedCoend.objects W F)]
  [HasCoequalizer (weightedCoend.leftMap W F) (weightedCoend.rightMap W F)]

example : weightedCoend.objects W F = fun a ↦ W.obj (op a) ⊗ F.obj a := rfl

example : weightedCoend.relations W F =
    fun (ab : A × A) ↦ W.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1) := rfl

example : weightedCoend.leftMap W F =
    Sigma.desc (fun (ab : A × A) ↦
      ((α_ (W.obj (op ab.2)) (ab.1 ⟶[V] ab.2) (F.obj ab.1)).inv ≫
          (MonoidalClosed.uncurry (W.map (op ab.2) (op ab.1)) ⊗ₘ
            𝟙 (F.obj ab.1))) ≫ Sigma.ι (weightedCoend.objects W F) ab.1) := rfl

example : weightedCoend.rightMap W F =
    Sigma.desc (fun (ab : A × A) ↦
      (W.obj (op ab.2) ◁
          ((β_ (ab.1 ⟶[V] ab.2) (F.obj ab.1)).hom ≫
            MonoidalClosed.uncurry (F.map ab.1 ab.2))) ≫
        Sigma.ι (weightedCoend.objects W F) ab.2) := rfl

/- The selected presentation is definitionally the actual coend. -/
example : weightedCoend W F =
    coequalizer (weightedCoend.leftMap W F) (weightedCoend.rightMap W F) := rfl

example : weightedCoend.mapWeightGraded F (GradedNatTrans.unitId W) =
    𝟙 (weightedCoend W F) :=
  weightedCoend.mapWeightGraded_id W F

example : weightedCoend.mapDiagramGraded W (GradedNatTrans.unitId F) =
    𝟙 (weightedCoend W F) :=
  weightedCoend.mapDiagramGraded_id W F

example : True := by
  fail_if_success exact (inferInstance : Category A)
  fail_if_success exact (inferInstance : IsSeparator (𝟙_ V))
  fail_if_success exact (inferInstance : SymmetricCategory V)
  fail_if_success exact (inferInstance : HasCoproductsOfShape A V)
  fail_if_success exact (inferInstance : HasCoproductsOfShape (A × A) V)
  fail_if_success exact (inferInstance : HasCoequalizers V)
  trivial

end Identity

section WeightComposition

variable {W₀ W₁ W₂ : EnrichedFunctor V Aᵒᵖ V} (F : EnrichedFunctor V A V)
variable [HasCoproduct (weightedCoend.relations W₀ F)]
  [HasCoproduct (weightedCoend.objects W₀ F)]
  [HasCoequalizer (weightedCoend.leftMap W₀ F) (weightedCoend.rightMap W₀ F)]
variable [HasCoproduct (weightedCoend.relations W₁ F)]
  [HasCoproduct (weightedCoend.objects W₁ F)]
  [HasCoequalizer (weightedCoend.leftMap W₁ F) (weightedCoend.rightMap W₁ F)]
variable [HasCoproduct (weightedCoend.relations W₂ F)]
  [HasCoproduct (weightedCoend.objects W₂ F)]
  [HasCoequalizer (weightedCoend.leftMap W₂ F) (weightedCoend.rightMap W₂ F)]

example
    (t₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W₀ W₁)
    (t₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W₁ W₂) :
    weightedCoend.mapWeightGraded F (GradedNatTrans.unitComp t₀₁ t₁₂) =
      weightedCoend.mapWeightGraded F t₀₁ ≫ weightedCoend.mapWeightGraded F t₁₂ :=
  weightedCoend.mapWeightGraded_comp F t₀₁ t₁₂

end WeightComposition

section DiagramComposition

variable (W : EnrichedFunctor V Aᵒᵖ V) {F₀ F₁ F₂ : EnrichedFunctor V A V}
variable [HasCoproduct (weightedCoend.relations W F₀)]
  [HasCoproduct (weightedCoend.objects W F₀)]
  [HasCoequalizer (weightedCoend.leftMap W F₀) (weightedCoend.rightMap W F₀)]
variable [HasCoproduct (weightedCoend.relations W F₁)]
  [HasCoproduct (weightedCoend.objects W F₁)]
  [HasCoequalizer (weightedCoend.leftMap W F₁) (weightedCoend.rightMap W F₁)]
variable [HasCoproduct (weightedCoend.relations W F₂)]
  [HasCoproduct (weightedCoend.objects W F₂)]
  [HasCoequalizer (weightedCoend.leftMap W F₂) (weightedCoend.rightMap W F₂)]

example
    (t₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (t₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₁ F₂) :
    weightedCoend.mapDiagramGraded W (GradedNatTrans.unitComp t₀₁ t₁₂) =
      weightedCoend.mapDiagramGraded W t₀₁ ≫ weightedCoend.mapDiagramGraded W t₁₂ :=
  weightedCoend.mapDiagramGraded_comp W t₀₁ t₁₂

end DiagramComposition

end ParticularGradedVarianceClients

namespace ParticularOrdinaryVarianceClients

open CategoryTheory.Enriched

universe uV vV uA vA

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
variable {A : Type uA} [Category.{vA} A] [EnrichedOrdinaryCategory V A]

section Identity

variable (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V)
variable [HasCoproduct (weightedCoend.relations W F)]
  [HasCoproduct (weightedCoend.objects W F)]
  [HasCoequalizer (weightedCoend.leftMap W F) (weightedCoend.rightMap W F)]

example (hsep : IsSeparator (𝟙_ V)) :
    weightedCoend.mapWeight F (𝟙 W) hsep = 𝟙 (weightedCoend W F) :=
  weightedCoend.mapWeight_id W F hsep

example (hsep : IsSeparator (𝟙_ V)) :
    weightedCoend.mapDiagram W (𝟙 F) hsep = 𝟙 (weightedCoend W F) :=
  weightedCoend.mapDiagram_id W F hsep

example : True := by
  fail_if_success exact (inferInstance : HasCoproductsOfShape A V)
  fail_if_success exact (inferInstance : HasCoproductsOfShape (A × A) V)
  fail_if_success exact (inferInstance : HasCoequalizers V)
  trivial

end Identity

section WeightComposition

variable {W₀ W₁ W₂ : EnrichedFunctor V Aᵒᵖ V} (F : EnrichedFunctor V A V)
variable [HasCoproduct (weightedCoend.relations W₀ F)]
  [HasCoproduct (weightedCoend.objects W₀ F)]
  [HasCoequalizer (weightedCoend.leftMap W₀ F) (weightedCoend.rightMap W₀ F)]
variable [HasCoproduct (weightedCoend.relations W₁ F)]
  [HasCoproduct (weightedCoend.objects W₁ F)]
  [HasCoequalizer (weightedCoend.leftMap W₁ F) (weightedCoend.rightMap W₁ F)]
variable [HasCoproduct (weightedCoend.relations W₂ F)]
  [HasCoproduct (weightedCoend.objects W₂ F)]
  [HasCoequalizer (weightedCoend.leftMap W₂ F) (weightedCoend.rightMap W₂ F)]

example (t₀₁ : W₀ ⟶ W₁) (t₁₂ : W₁ ⟶ W₂) (hsep : IsSeparator (𝟙_ V)) :
    weightedCoend.mapWeight F (t₀₁ ≫ t₁₂) hsep =
      weightedCoend.mapWeight F t₀₁ hsep ≫ weightedCoend.mapWeight F t₁₂ hsep :=
  weightedCoend.mapWeight_comp F t₀₁ t₁₂ hsep

end WeightComposition

section DiagramComposition

variable (W : EnrichedFunctor V Aᵒᵖ V) {F₀ F₁ F₂ : EnrichedFunctor V A V}
variable [HasCoproduct (weightedCoend.relations W F₀)]
  [HasCoproduct (weightedCoend.objects W F₀)]
  [HasCoequalizer (weightedCoend.leftMap W F₀) (weightedCoend.rightMap W F₀)]
variable [HasCoproduct (weightedCoend.relations W F₁)]
  [HasCoproduct (weightedCoend.objects W F₁)]
  [HasCoequalizer (weightedCoend.leftMap W F₁) (weightedCoend.rightMap W F₁)]
variable [HasCoproduct (weightedCoend.relations W F₂)]
  [HasCoproduct (weightedCoend.objects W F₂)]
  [HasCoequalizer (weightedCoend.leftMap W F₂) (weightedCoend.rightMap W F₂)]

example (t₀₁ : F₀ ⟶ F₁) (t₁₂ : F₁ ⟶ F₂) (hsep : IsSeparator (𝟙_ V)) :
    weightedCoend.mapDiagram W (t₀₁ ≫ t₁₂) hsep =
      weightedCoend.mapDiagram W t₀₁ hsep ≫ weightedCoend.mapDiagram W t₁₂ hsep :=
  weightedCoend.mapDiagram_comp W t₀₁ t₁₂ hsep

end DiagramComposition

end ParticularOrdinaryVarianceClients


namespace CoyonedaLegacyTypeGuards

universe uV vV uA

open CategoryTheory.Enriched CategoryTheory.Enriched.weightedCoend Opposite

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
variable {A : Type uA} [EnrichedCategory V A]

@[reassoc]
private theorem legacyCoyonedaHom
    (F : EnrichedFunctor V A V) (c : A) :
    let R := EnrichedFunctor.contravariantRepresentable V A c
    let t : A → V := fun a ↦ R.obj (op a) ⊗ F.obj a
    let s : A × A → V := fun ab ↦
      R.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)
    let wa : ∀ a b, s (a, b) ⟶ t a := fun a b ↦
      (α_ (R.obj (op b)) (a ⟶[V] b) (F.obj a)).inv ≫
        (MonoidalClosed.uncurry (R.map (op b) (op a)) ⊗ₘ 𝟙 (F.obj a))
    let da : ∀ a b, s (a, b) ⟶ t b := fun a b ↦
      R.obj (op b) ◁
        ((β_ (a ⟶[V] b) (F.obj a)).hom ≫ MonoidalClosed.uncurry (F.map a b))
    let l [HasCoproduct s] [HasCoproduct t] : (∐ s) ⟶ ∐ t :=
      Sigma.desc fun ab ↦ wa ab.1 ab.2 ≫ Sigma.ι t ab.1
    let r [HasCoproduct s] [HasCoproduct t] : (∐ s) ⟶ ∐ t :=
      Sigma.desc fun ab ↦ da ab.1 ab.2 ≫ Sigma.ι t ab.2
    ∀ [HasCoproduct s] [HasCoproduct t] [HasCoequalizer l r] (a : A),
      ι R F a ≫ (coyonedaIso F c).hom =
        (β_ (a ⟶[V] c) (F.obj a)).hom ≫ MonoidalClosed.uncurry (F.map a c) := by
  dsimp only
  intro _ _ _ a
  exact weightedCoend.coyonedaIso_ι_hom F c a

private theorem legacyCoyonedaInverse
    (F : EnrichedFunctor V A V) (c : A) :
    let R := EnrichedFunctor.contravariantRepresentable V A c
    let t : A → V := fun a ↦ R.obj (op a) ⊗ F.obj a
    let s : A × A → V := fun ab ↦
      R.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)
    let wa : ∀ a b, s (a, b) ⟶ t a := fun a b ↦
      (α_ (R.obj (op b)) (a ⟶[V] b) (F.obj a)).inv ≫
        (MonoidalClosed.uncurry (R.map (op b) (op a)) ⊗ₘ 𝟙 (F.obj a))
    let da : ∀ a b, s (a, b) ⟶ t b := fun a b ↦
      R.obj (op b) ◁
        ((β_ (a ⟶[V] b) (F.obj a)).hom ≫ MonoidalClosed.uncurry (F.map a b))
    let l [HasCoproduct s] [HasCoproduct t] : (∐ s) ⟶ ∐ t :=
      Sigma.desc fun ab ↦ wa ab.1 ab.2 ≫ Sigma.ι t ab.1
    let r [HasCoproduct s] [HasCoproduct t] : (∐ s) ⟶ ∐ t :=
      Sigma.desc fun ab ↦ da ab.1 ab.2 ≫ Sigma.ι t ab.2
    ∀ [HasCoproduct s] [HasCoproduct t] [HasCoequalizer l r],
      (coyonedaIso F c).inv =
        (λ_ (F.obj c)).inv ≫ (eId V c ⊗ₘ 𝟙 (F.obj c)) ≫ ι R F c := by
  dsimp only
  intro _ _ _
  exact weightedCoend.coyonedaIso_inv F c

/- The whole function types retain exactly the old presentation and binders. -/
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let pairs : Array (Name × Name) := #[
    (``CategoryTheory.Enriched.weightedCoend.coyonedaIso_ι_hom,
      ``legacyCoyonedaHom),
    (``CategoryTheory.Enriched.weightedCoend.coyonedaIso_ι_hom_assoc,
      ``legacyCoyonedaHom_assoc),
    (``CategoryTheory.Enriched.weightedCoend.coyonedaIso_inv,
      ``legacyCoyonedaInverse)]
  for (actualName, legacyName) in pairs do
    let actual ← getConstInfo actualName
    let legacy ← getConstInfo legacyName
    unless actual.levelParams.length == legacy.levelParams.length &&
        actual.levelParams.all (legacy.levelParams.contains ·) do
      throwError "{actualName} has changed universe parameters"
    unless ← isDefEq actual.type legacy.type do
      throwError "{actualName} has changed its complete public function type"
    logInfo m!"complete legacy type preserved: {actualName}"

end CoyonedaLegacyTypeGuards
