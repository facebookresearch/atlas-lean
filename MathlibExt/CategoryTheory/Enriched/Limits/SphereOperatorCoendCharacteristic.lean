/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.CoendCharacteristicEquationTransport
public import MathlibExt.CategoryTheory.Enriched.Limits.SphereOperatorCoendProofFamilies

/-!
# Full reindexed characteristic of the original coend algorithm

Reindex the proved whole characteristic by arbitrary object functions while
retaining the entire original coend, both full weights and every coefficient.
The source and target object functions are the actual selected constructors.
No original-category or native Hom dictionary is substituted into the proof.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe uV vV uA vA uJ uR

open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace CategoryTheory.Enriched
namespace GenericCoendCharacteristic

attribute [local instance] MonoidalClosed.enrichedCategorySelf

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] {A : Type uA} [Category.{vA} A] [MonoidalCategory A]
  [EnrichedOrdinaryCategory V A] [MonoidalClosed V] {J : Type uJ} {R : Type uR}

variable (d : EnrichedMonoidalCategoryData V A) (S : EnrichedFunctor V A V)
  (pr : CoendProofFamilies.RelationFamily d S) (po : CoendProofFamilies.ObjectFamily d S)
  (pe : CoendProofFamilies.CoequalizerFamily d S pr po) (σ : J → A) (τ : R → A)

/-- The complete original source weight object under its literal object function. -/
abbrev sourceWeight : J → J → J → V :=
  fun n k a => ((σ a ⊗ σ n) ⟶[V] σ k)

/-- The complete original target weight, retaining the entire final tensor factor. -/
abbrev targetWeight : R → J → J → J → V :=
  fun r n k a => ((σ a ⊗ (σ n ⊗ τ r)) ⟶[V] (σ k ⊗ τ r))

/-- The same whole original coefficient object function under reindexing. -/
abbrev coefficient : J → V := fun a => S.obj (σ a)

/-- The actual complete original source coend object function. -/
abbrev sourceObject : J → J → V :=
  fun n k => CoendProofFamilies.coend d S pr po pe (σ n) (σ k)

/-- The exact target coend constructor, with its full original shift objects. -/
abbrev targetObject : R → J → J → V :=
  fun r n k => CoendProofFamilies.coend d S pr po pe (σ n ⊗ τ r) (σ k ⊗ τ r)

/-- The complete original insertion before any source coefficient is applied. -/
def sourceInsertion : CoendEquationTransport.SourceInsertion (sourceWeight (V := V) σ)
  (coefficient S σ)
    (sourceObject d S pr po pe σ) :=
  fun n k a => CoendProofFamilies.insertionFunction d S pr po pe (σ n) (σ k) (σ a)

/-- Every full original shifted insertion under both object functions. -/
def targetInsertion : CoendEquationTransport.TargetInsertion (targetWeight (V := V) σ τ)
  (coefficient S σ)
    (targetObject d S pr po pe σ τ) :=
  fun r n k a => CoendProofFamilies.insertionFunction d S pr po pe
    (σ n ⊗ τ r) (σ k ⊗ τ r) (σ a)

/-- The entire original coend Hom-map function, with all construction proofs retained. -/
def homMap : CoendEquationTransport.HomMap (sourceObject d S pr po pe σ)
    (targetObject d S pr po pe σ τ) :=
  fun r n k => CoendProofFamilies.homFunction d S pr po pe (τ r) (σ n) (σ k)

/-- The actual full weight map, before any coend or Hom argument is applied. -/
def weightMap : CoendEquationTransport.WeightMap (sourceWeight (V := V) σ) (targetWeight (V :=
  V) σ τ) :=
  fun r n k a => GenericRightTensor.weightShiftMap d (τ r) (σ n) (σ k) (σ a)

/-- The entire reindexed characteristic follows from the checked original
whole function law, with all coefficient and weight objects intact. -/
theorem condition_proof :
    CoendEquationTransport.Condition (sourceInsertion d S pr po pe σ)
      (targetInsertion d S pr po pe σ τ) (homMap d S pr po pe σ τ) (weightMap d σ τ) := by
  exact congrArg (fun Φ => fun r n k a => Φ (τ r) (σ n) (σ k) (σ a))
    (CoendProofFamilies.hom_characteristic_whisker_function d S pr po pe)

end GenericCoendCharacteristic
end CategoryTheory.Enriched
