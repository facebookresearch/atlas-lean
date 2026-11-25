/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.NaturalTransformation

/-!
# Tests for unit-graded enriched natural transformations
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

universe uV vV uC vC uD vD

namespace CategoryTheory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
variable {C : Type uC} [Category.{vC} C]
  [EnrichedOrdinaryCategory V C]
variable {D : Type uD} [Category.{vD} D]
  [EnrichedOrdinaryCategory V D]
variable {F G : EnrichedFunctor V C D}

section Forward

variable (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G)

example : EnrichedNatTrans F G := a.toEnrichedNatTrans

example (X : C) :
    ForgetEnrichment.homTo V
        (a.toEnrichedNatTrans.out.app (ForgetEnrichment.of V X)) =
      a.app X :=
  rfl

example (X : C) :
    (ForgetEnrichment.equivFunctor V D).map
        (a.toEnrichedNatTrans.out.app (ForgetEnrichment.of V X)) =
      (eHomEquiv V).symm (a.app X) :=
  rfl

example (X Y : C) (f : 𝟙_ V ⟶ (X ⟶[V] Y)) :
    F.forget.map (ForgetEnrichment.homOf V f) ≫
          a.toEnrichedNatTrans.out.app (ForgetEnrichment.of V Y) =
      a.toEnrichedNatTrans.out.app (ForgetEnrichment.of V X) ≫
        G.forget.map (ForgetEnrichment.homOf V f) :=
  a.toEnrichedNatTrans.out.naturality (ForgetEnrichment.homOf V f)

end Forward

section Reverse

variable (hsep : IsSeparator (𝟙_ V)) (a : EnrichedNatTrans F G)

example : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G :=
  a.toGradedNatTrans hsep

example (X : C) :
    (a.toGradedNatTrans hsep).app X =
      ForgetEnrichment.homTo V
        (a.out.app (ForgetEnrichment.of V X)) :=
  rfl

example (X Y : C) :
    (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫
          (F.map X Y ⊗ₘ ForgetEnrichment.homTo V
            (a.out.app (ForgetEnrichment.of V Y))) ≫
        eComp V _ _ _ =
      (ForgetEnrichment.homTo V
            (a.out.app (ForgetEnrichment.of V X)) ⊗ₘ G.map X Y) ≫
        eComp V _ _ _ :=
  a.enrichedNaturality hsep X Y

example (X Y : C) :
    (a.toGradedNatTrans hsep).naturality X Y =
      a.enrichedNaturality hsep X Y :=
  rfl

example : True := by
  fail_if_success
    exact (a.toGradedNatTrans :
      GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G)
  trivial

end Reverse

section Inverses

variable (hsep : IsSeparator (𝟙_ V))

example (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G) :
    a.toEnrichedNatTrans.toGradedNatTrans hsep = a :=
  a.toEnriched_toGraded hsep

example (a : EnrichedNatTrans F G) :
    (a.toGradedNatTrans hsep).toEnrichedNatTrans = a :=
  a.toGraded_toEnriched hsep

end Inverses

section WhiskerNaturality

example {P Q R S : C} {H : V}
    (f : H ⟶ (P ⟶[V] Q)) (g : H ⟶ (R ⟶[V] S))
    (a : P ⟶ R) (b : Q ⟶ S)
    (h : (β_ (𝟙_ V) H).hom ≫
          (f ⊗ₘ eHomEquiv V b) ≫ eComp V P Q S =
        (eHomEquiv V a ⊗ₘ g) ≫ eComp V P R S) :
    f ≫ eHomWhiskerLeft V P b =
      g ≫ eHomWhiskerRight V a S :=
  unitGradedNaturality_eq_whisker f g a b h

end WhiskerNaturality

section Closed

open scoped MonoidalClosed

variable [MonoidalClosed V]
variable {A : Type uC} [EnrichedCategory V A]
variable {F' G' H' : EnrichedFunctor V A V}

section Components

variable (q : ∀ X, F'.obj X ⟶ G'.obj X)
variable (hq : ∀ X Y,
  MonoidalClosed.uncurry (F'.map X Y) ≫ q Y =
    (q X ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫ MonoidalClosed.uncurry (G'.map X Y))

example : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F' G' :=
  GradedNatTrans.unitOfComponents q hq

example (X : A) :
    (GradedNatTrans.unitOfComponents q hq).app X = eHomEquiv V (q X) :=
  GradedNatTrans.unitOfComponents_app q hq X

example (X : A) :
    (eHomEquiv V).symm ((GradedNatTrans.unitOfComponents q hq).app X) = q X :=
  GradedNatTrans.unitOfComponents_component q hq X

example (X Y : A) :
    MonoidalClosed.uncurry (F'.map X Y) ≫ q Y =
      (q X ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫ MonoidalClosed.uncurry (G'.map X Y) := by
  simpa only [GradedNatTrans.unitOfComponents_component] using
    (GradedNatTrans.unitOfComponents q hq).uncurriedNaturality X Y

example : True := by
  fail_if_success exact (inferInstance : Category A)
  fail_if_success exact (inferInstance : IsSeparator (𝟙_ V))
  fail_if_success exact (inferInstance : SymmetricCategory V)
  fail_if_success
    exact (GradedNatTrans.unitOfComponents q :
      GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F' G')
  trivial

variable (r : ∀ X, G'.obj X ⟶ H'.obj X)
variable (hr : ∀ X Y,
  MonoidalClosed.uncurry (G'.map X Y) ≫ r Y =
    (r X ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫ MonoidalClosed.uncurry (H'.map X Y))

example (X : A) :
    (eHomEquiv V).symm
        ((GradedNatTrans.unitComp
          (GradedNatTrans.unitOfComponents q hq)
          (GradedNatTrans.unitOfComponents r hr)).app X) = q X ≫ r X := by
  rw [GradedNatTrans.unitComp_component,
    GradedNatTrans.unitOfComponents_component,
    GradedNatTrans.unitOfComponents_component]

end Components

example (F' : EnrichedFunctor V A V) :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F' F' :=
  GradedNatTrans.unitId F'

example (F' : EnrichedFunctor V A V) (X : A) :
    (GradedNatTrans.unitId F').app X = eId V (F'.obj X) :=
  GradedNatTrans.unitId_app F' X

example (F' : EnrichedFunctor V A V) (X : A) :
    (eHomEquiv V).symm ((GradedNatTrans.unitId F').app X) = 𝟙 (F'.obj X) :=
  GradedNatTrans.unitId_component F' X

example (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F' G')
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G' H') :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F' H' :=
  GradedNatTrans.unitComp a b

example (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F' G')
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G' H') (X : A) :
    (GradedNatTrans.unitComp a b).app X =
      (λ_ (𝟙_ V)).inv ≫ (a.app X ⊗ₘ b.app X) ≫ eComp V _ _ _ :=
  GradedNatTrans.unitComp_app a b X

example (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F' G')
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G' H') (X : A) :
    (eHomEquiv V).symm ((GradedNatTrans.unitComp a b).app X) =
      (eHomEquiv V).symm (a.app X) ≫ (eHomEquiv V).symm (b.app X) :=
  GradedNatTrans.unitComp_component a b X

example (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F' G')
    (X Y : A) :
    MonoidalClosed.uncurry (F'.map X Y) ≫
        (eHomEquiv V).symm (a.app Y) =
      ((eHomEquiv V).symm (a.app X) ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry (G'.map X Y) :=
  a.uncurriedNaturality X Y

example (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F' G')
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G' H') (X Y : A) :
    MonoidalClosed.uncurry (F'.map X Y) ≫
        (eHomEquiv V).symm ((GradedNatTrans.unitComp a b).app Y) =
      ((eHomEquiv V).symm ((GradedNatTrans.unitComp a b).app X) ⊗ₘ
          𝟙 (X ⟶[V] Y)) ≫ MonoidalClosed.uncurry (H'.map X Y) :=
  (GradedNatTrans.unitComp a b).uncurriedNaturality X Y

example (F₁ : EnrichedFunctor V C V) (hsep : IsSeparator (𝟙_ V)) :
    (𝟙 F₁ : EnrichedNatTrans F₁ F₁).toGradedNatTrans hsep =
      GradedNatTrans.unitId F₁ :=
  EnrichedNatTrans.toGradedNatTrans_id F₁ hsep

example {F₁ F₂ F₃ : EnrichedFunctor V C V} (a : F₁ ⟶ F₂) (b : F₂ ⟶ F₃)
    (hsep : IsSeparator (𝟙_ V)) :
    (a ≫ b).toGradedNatTrans hsep =
      GradedNatTrans.unitComp (a.toGradedNatTrans hsep) (b.toGradedNatTrans hsep) :=
  EnrichedNatTrans.toGradedNatTrans_comp a b hsep

end Closed

end CategoryTheory

#print axioms CategoryTheory.unitGradedNaturality_eq_whisker
#print axioms CategoryTheory.GradedNatTrans.uncurriedNaturality
#print axioms CategoryTheory.GradedNatTrans.unitOfComponents
#print axioms CategoryTheory.GradedNatTrans.unitOfComponents_app
#print axioms CategoryTheory.GradedNatTrans.unitOfComponents_component
#print axioms CategoryTheory.GradedNatTrans.unitId
#print axioms CategoryTheory.GradedNatTrans.unitComp
#print axioms CategoryTheory.GradedNatTrans.unitId_app
#print axioms CategoryTheory.GradedNatTrans.unitId_component
#print axioms CategoryTheory.GradedNatTrans.unitComp_app
#print axioms CategoryTheory.GradedNatTrans.unitComp_component
#print axioms CategoryTheory.EnrichedNatTrans.toGradedNatTrans_id
#print axioms CategoryTheory.EnrichedNatTrans.toGradedNatTrans_comp
#print axioms CategoryTheory.GradedNatTrans.toEnrichedNatTrans
#print axioms CategoryTheory.EnrichedNatTrans.toGradedNatTrans
#print axioms CategoryTheory.EnrichedNatTrans.enrichedNaturality
#print axioms CategoryTheory.GradedNatTrans.toEnriched_toGraded
#print axioms CategoryTheory.EnrichedNatTrans.toGraded_toEnriched
