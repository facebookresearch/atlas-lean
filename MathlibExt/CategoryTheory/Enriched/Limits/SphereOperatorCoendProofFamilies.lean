/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorRightTensor

/-!
# Fixed weighted-coend algorithms under full proof families

Every category, enrichment, monoidal map, coefficient functor, coproduct
diagram and parallel relation map remains fixed. Only the Prop-valued
existence proof families vary. The actual original coend and insertion
functions retain their explicit constructor arguments.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe uV vV uA vA

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace CategoryTheory.Enriched
namespace CoendProofFamilies

open CategoryTheory.Enriched.SphereOperator

attribute [local instance] MonoidalClosed.enrichedCategorySelf

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] {A : Type uA} [Category.{vA} A]
  [MonoidalCategory A] [EnrichedOrdinaryCategory V A] [MonoidalClosed V]

/-- The complete original relation-coproduct existence proof family. -/
abbrev RelationFamily (d : EnrichedMonoidalCategoryData V A) (S : EnrichedFunctor V A V) : Prop :=
  ∀ n k : A, HasCoproduct (Enriched.weightedCoend.relations (weight d n k) S)

/-- The complete original object-coproduct existence proof family. -/
abbrev ObjectFamily (d : EnrichedMonoidalCategoryData V A) (S : EnrichedFunctor V A V) : Prop :=
  ∀ n k : A, HasCoproduct (Enriched.weightedCoend.objects (weight d n k) S)

/-- The full coequalizer predicate retains both actual coproduct proof arguments. -/
abbrev CoequalizerFamily (d : EnrichedMonoidalCategoryData V A)
    (S : EnrichedFunctor V A V) (pr : RelationFamily d S) (po : ObjectFamily d S) : Prop :=
  ∀ n k : A, HasCoequalizer
    (@Enriched.weightedCoend.leftMap V _ _ _ _ A _ (weight d n k) S (pr n k) (po n k))
    (@Enriched.weightedCoend.rightMap V _ _ _ _ A _ (weight d n k) S (pr n k) (po n k))

/-- The same selected coequalizer algorithm with all existence witnesses explicit. -/
abbrev coend (d : EnrichedMonoidalCategoryData V A) (S : EnrichedFunctor V A V)
    (pr : RelationFamily d S) (po : ObjectFamily d S) (pe : CoequalizerFamily d S pr po)
    (n k : A) : V :=
  @Enriched.weightedCoend V _ _ _ _ A _ (weight d n k) S (pr n k) (po n k) (pe n k)

/-- The entire insertion function uses the original object coproduct and coequalizer. -/
def insertionFunction (d : EnrichedMonoidalCategoryData V A) (S : EnrichedFunctor V A V)
    (pr : RelationFamily d S) (po : ObjectFamily d S) (pe : CoequalizerFamily d S pr po) :
    ∀ n k a : A, Enriched.weightedCoend.objects (weight d n k) S a ⟶ coend d S pr po pe n k :=
  fun n k a =>
    @Enriched.weightedCoend.ι V _ _ _ _ A _ (weight d n k) S (pr n k) (po n k) (pe n k) a

/-- The entire proved shift uses the actual generic map with the original proof families. -/
def homFunction (d : EnrichedMonoidalCategoryData V A) (S : EnrichedFunctor V A V)
    (pr : RelationFamily d S) (po : ObjectFamily d S) (pe : CoequalizerFamily d S pr po) :
    ∀ r n k : A, coend d S pr po pe n k ⟶ coend d S pr po pe (n ⊗ r) (k ⊗ r) :=
  @GenericRightTensor.hom V _ _ _ A _ _ _ _ d S pr po pe

/-- The dependent coequalizer predicate is unchanged by its Prop-family witnesses. -/
theorem coequalizerFamily_eq (d : EnrichedMonoidalCategoryData V A)
    (S : EnrichedFunctor V A V) (pr pr' : RelationFamily d S) (po po' : ObjectFamily d S) :
    CoequalizerFamily d S pr po = CoequalizerFamily d S pr' po' := by
  cases Subsingleton.elim pr pr'
  cases Subsingleton.elim po po'
  rfl

/-- The full object function is independent only of proof families for the fixed algorithm. -/
theorem coend_object_function_eq (d : EnrichedMonoidalCategoryData V A)
    (S : EnrichedFunctor V A V) (pr pr' : RelationFamily d S) (po po' : ObjectFamily d S)
    (pe : CoequalizerFamily d S pr po) (pe' : CoequalizerFamily d S pr' po') :
    coend d S pr po pe = coend d S pr' po' pe' := by
  cases Subsingleton.elim pr pr'
  cases Subsingleton.elim po po'
  cases Subsingleton.elim pe pe'
  rfl

/-- Both complete insertion functions agree before any index or Hom input is applied. -/
theorem insertion_function_heq (d : EnrichedMonoidalCategoryData V A)
    (S : EnrichedFunctor V A V) (pr pr' : RelationFamily d S) (po po' : ObjectFamily d S)
    (pe : CoequalizerFamily d S pr po) (pe' : CoequalizerFamily d S pr' po') :
    HEq (insertionFunction d S pr po pe) (insertionFunction d S pr' po' pe') := by
  cases Subsingleton.elim pr pr'
  cases Subsingleton.elim po po'
  cases Subsingleton.elim pe pe'
  rfl

/-- Both entire shift functions agree for the same construction under its proof families. -/
theorem hom_function_heq (d : EnrichedMonoidalCategoryData V A)
    (S : EnrichedFunctor V A V) (pr pr' : RelationFamily d S) (po po' : ObjectFamily d S)
    (pe : CoequalizerFamily d S pr po) (pe' : CoequalizerFamily d S pr' po') :
    HEq (homFunction d S pr po pe) (homFunction d S pr' po' pe') := by
  cases Subsingleton.elim pr pr'
  cases Subsingleton.elim po po'
  cases Subsingleton.elim pe pe'
  rfl

/-- The original complete characteristic law holds with every constructor proof explicit. -/
theorem hom_characteristic_function (d : EnrichedMonoidalCategoryData V A)
    (S : EnrichedFunctor V A V) (pr : RelationFamily d S) (po : ObjectFamily d S)
    (pe : CoequalizerFamily d S pr po) :
    (fun r n k a : A => insertionFunction d S pr po pe n k a ≫ homFunction d S pr po pe r n k) =
      fun r n k a : A => (GenericRightTensor.weightShiftMap d r n k a ⊗ₘ 𝟙 (S.obj a)) ≫
        insertionFunction d S pr po pe (n ⊗ r) (k ⊗ r) a :=
  @GenericRightTensor.hom_ι_function V _ _ _ A _ _ _ _ d S pr po pe

/-- The full characteristic law uses the original right whisker before any native specialization. -/
theorem hom_characteristic_whisker_function (d : EnrichedMonoidalCategoryData V A)
    (S : EnrichedFunctor V A V) (pr : RelationFamily d S) (po : ObjectFamily d S)
    (pe : CoequalizerFamily d S pr po) :
    (fun r n k a : A => insertionFunction d S pr po pe n k a ≫ homFunction d S pr po pe r n k) =
      fun r n k a : A => (GenericRightTensor.weightShiftMap d r n k a ▷ S.obj a) ≫
        insertionFunction d S pr po pe (n ⊗ r) (k ⊗ r) a := by
  simpa only [tensorHom_id] using hom_characteristic_function d S pr po pe

end CoendProofFamilies
end CategoryTheory.Enriched
