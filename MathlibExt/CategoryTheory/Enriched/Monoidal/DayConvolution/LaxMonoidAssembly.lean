/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.LaxMonoidAssociativity

/-!
# A monoid on the actual Day convolution from enriched lax monoidal data

The original enriched unit and tensorator become a stock `MonObj` on the
unchanged enriched functor category, under the monoidal structure constructed
from the actual coends.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.LaxMonoid

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

/-- The actual extended unit and descended tensorator satisfy the left monoid unit equation. -/
theorem one_mul_law :
    letI := ColimitMonoidal.monoidalCategory d
    (unit d S L ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫ multiply d S L =
      (λ_ (⟨S⟩ : EnrichedFunctorCat V I)).hom := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let F : EnrichedFunctorCat V I := ⟨S⟩
  apply (cancel_epi (λ_ F).inv).1
  have h : (λ_ F).inv ≫ (unit d S L ▷ F) ≫ multiply d S L = 𝟙 F := by
    apply EnrichedFunctorCat.hom_ext
    intro k
    rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_comp,
      EnrichedFunctorCat.component_id]
    have hi : EnrichedFunctorCat.component (λ_ F).inv k = Unitors.leftInvComponent d S k :=
      Unitors.leftUnitorInv_component d S k
    have hm : EnrichedFunctorCat.component (unit d S L ▷ F) k =
        Input.mapAt d.tensorEnrichedFunctor (unit d S L) (GradedNatTrans.unitId S) k :=
      Input.natTrans_component d.tensorEnrichedFunctor (unit d S L) (GradedNatTrans.unitId S) k
    rw [hi, hm]
    exact leftInv_unit_multiply d S L k
  exact h.trans (Iso.inv_hom_id (λ_ F)).symm

/-- The actual extended unit and descended tensorator satisfy the right monoid unit equation. -/
theorem mul_one_law :
    letI := ColimitMonoidal.monoidalCategory d
    ((⟨S⟩ : EnrichedFunctorCat V I) ◁ unit d S L) ≫ multiply d S L =
      (ρ_ (⟨S⟩ : EnrichedFunctorCat V I)).hom := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let F : EnrichedFunctorCat V I := ⟨S⟩
  apply (cancel_epi (ρ_ F).inv).1
  have h : (ρ_ F).inv ≫ (F ◁ unit d S L) ≫ multiply d S L = 𝟙 F := by
    apply EnrichedFunctorCat.hom_ext
    intro k
    rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_comp,
      EnrichedFunctorCat.component_id]
    have hi : EnrichedFunctorCat.component (ρ_ F).inv k = Unitors.rightInvComponent d S k :=
      Unitors.rightUnitorInv_component d S k
    have hm : EnrichedFunctorCat.component (F ◁ unit d S L) k =
        Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId S) (unit d S L) k :=
      Input.natTrans_component d.tensorEnrichedFunctor (GradedNatTrans.unitId S) (unit d S L) k
    rw [hi, hm]
    exact rightInv_unit_multiply d S L k
  exact h.trans (Iso.inv_hom_id (ρ_ F)).symm

/-- The actual descended tensorator satisfies associativity under the constructed Day associator. -/
theorem mul_assoc_law :
    letI := ColimitMonoidal.monoidalCategory d
    (multiply d S L ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫ multiply d S L =
      (α_ (⟨S⟩ : EnrichedFunctorCat V I) ⟨S⟩ ⟨S⟩).hom ≫
        ((⟨S⟩ : EnrichedFunctorCat V I) ◁ multiply d S L) ≫ multiply d S L := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let F : EnrichedFunctorCat V I := ⟨S⟩
  apply EnrichedFunctorCat.hom_ext
  intro k
  simp only [EnrichedFunctorCat.component_comp]
  have hl : EnrichedFunctorCat.component (multiply d S L ▷ F) k =
      Input.mapAt d.tensorEnrichedFunctor (multiply d S L) (GradedNatTrans.unitId S) k :=
    Input.natTrans_component d.tensorEnrichedFunctor (multiply d S L) (GradedNatTrans.unitId S) k
  have hr : EnrichedFunctorCat.component (F ◁ multiply d S L) k =
      Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId S) (multiply d S L) k :=
    Input.natTrans_component d.tensorEnrichedFunctor (GradedNatTrans.unitId S) (multiply d S L) k
  have ha : EnrichedFunctorCat.component (α_ F F F).hom k =
      (AssociatorConstruction.componentIso d S S S k).hom :=
    AssociatorConstruction.functorIso_hom_component d S S S k
  rw [hl, hr, ha]
  exact multiply_assoc_component d S L k

/-- The original enriched lax maps define a monoid on the actual constructed Day category. -/
@[instance_reducible]
def monObj :
    letI := ColimitMonoidal.monoidalCategory d
    MonObj (⟨S⟩ : EnrichedFunctorCat V I) := by
  letI := ColimitMonoidal.monoidalCategory d
  exact
    { one := unit d S L
      mul := multiply d S L
      one_mul := one_mul_law d S L
      mul_one := mul_one_law d S L
      mul_assoc := mul_assoc_law d S L }

/-- The monoid unit is precisely the original enriched Yoneda extension. -/
theorem monObj_one :
    letI := ColimitMonoidal.monoidalCategory d
    letI := monObj d S L
    MonObj.one (X := (⟨S⟩ : EnrichedFunctorCat V I)) = unit d S L := rfl

/-- The monoid multiplication is precisely the original full-coend tensorator descent. -/
theorem monObj_mul :
    letI := ColimitMonoidal.monoidalCategory d
    letI := monObj d S L
    MonObj.mul (X := (⟨S⟩ : EnrichedFunctorCat V I)) = multiply d S L := rfl

end CategoryTheory.EnrichedDayKernel.LaxMonoid
