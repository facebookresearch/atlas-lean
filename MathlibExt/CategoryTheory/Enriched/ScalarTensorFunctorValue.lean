/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.ScalarCorners
public import MathlibExt.CategoryTheory.Enriched.MappingParametrized
public import MathlibExt.CategoryTheory.Adjunction.Parametrized.WholeRecovery

/-!
# The same complete scalar tensor bifunctor in both adjunction interfaces

The scalar and weighted-end interfaces use the original tensor bifunctor.
Their comparison fixes every category, monoidal, braided, closed and
enriched argument before retaining the full functor and adjunction values.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe uV vV uI

open CategoryTheory CategoryTheory.EnrichedFunctorCat

namespace CategoryTheory.EnrichedFunctorCat.ScalarTensorFunctorValue

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]

/-- Both wrappers retain the same complete scalar bifunctor. -/
theorem scalar_weighted_tensor :
    ScalarLeibniz.tensorBifunctor (V := V) (A := I) =
      WeightedEndVariance.tensorBifunctor (V := V) (I := I) := rfl

/-- The complete flipped tensor bifunctors are also the same original values. -/
theorem scalar_weighted_tensor_flip :
    (ScalarLeibniz.tensorBifunctor (V := V) (A := I)).flip =
      (WeightedEndVariance.tensorBifunctor (V := V) (I := I)).flip :=
  congrArg Functor.flip scalar_weighted_tensor

/-- The entire scalar cotensor adjunction is transported through that exact value equality. -/
def weightedScalarAdjunction :
    WeightedEndVariance.tensorBifunctor (V := V) (I := I) ⊣₂
      ScalarLeibniz.cotensorBifunctor (V := V) (A := I) :=
  ParametrizedAdjunction.transportWhole scalar_weighted_tensor rfl
    (ScalarLeibniz.parametrizedAdjunction (V := V) (A := I))

/-- Transport retains the actual complete scalar parametrized adjunction. -/
theorem weightedScalarAdjunction_heq :
    HEq (weightedScalarAdjunction (V := V) (I := I))
      (ScalarLeibniz.parametrizedAdjunction (V := V) (A := I)) :=
  ParametrizedAdjunction.transportWhole_heq scalar_weighted_tensor rfl
    (ScalarLeibniz.parametrizedAdjunction (V := V) (A := I))

/-- With the same complete bifunctor type, transport retains the original whole value. -/
theorem weightedScalarAdjunction_eq_original :
    weightedScalarAdjunction (V := V) (I := I) =
      ScalarLeibniz.parametrizedAdjunction (V := V) (A := I) :=
  eq_of_heq weightedScalarAdjunction_heq

/-- The complete transported Hom-equivalence family is the original scalar correspondence. -/
theorem weightedScalarAdjunction_homEquiv_function :
    (fun (T : V) (X E : EnrichedFunctorCat V I) =>
      (weightedScalarAdjunction (V := V) (I := I)).homEquiv
        (X₁ := T) (X₂ := X) (X₃ := E)) =
      fun (T : V) (X E : EnrichedFunctorCat V I) => ScalarLeibniz.homEquiv T X E := by
  funext T X E
  rw [weightedScalarAdjunction_eq_original]
  change (ScalarLeibniz.adjunction T).homEquiv X E = ScalarLeibniz.homEquiv T X E
  exact ScalarLeibniz.adjunction_homEquiv T X E

/-- Each original Hom equivalence follows from that entire retained function family. -/
theorem weightedScalarAdjunction_homEquiv (T : V) (X E : EnrichedFunctorCat V I) :
    (weightedScalarAdjunction (V := V) (I := I)).homEquiv
        (X₁ := T) (X₂ := X) (X₃ := E) = ScalarLeibniz.homEquiv T X E :=
  congrFun (congrFun (congrFun weightedScalarAdjunction_homEquiv_function T) X) E

/-- Every entire fixed scalar adjunction is retained with its original functors. -/
theorem weightedScalarAdjunction_fixed_heq :
    HEq (fun T => (weightedScalarAdjunction (V := V) (I := I)).adj T)
      (fun T => (ScalarLeibniz.parametrizedAdjunction (V := V) (A := I)).adj T) := by
  rw [weightedScalarAdjunction_eq_original]

/-- The whole transported forward function family is the original scalar adjunct family. -/
theorem weightedScalarAdjunction_forward_heq :
    HEq (fun (T : V) (X E : EnrichedFunctorCat V I) =>
      ((weightedScalarAdjunction (V := V) (I := I)).homEquiv
        (X₁ := T) (X₂ := X) (X₃ := E) : _ → _))
      (fun (T : V) (X E : EnrichedFunctorCat V I) =>
        ((ScalarLeibniz.parametrizedAdjunction (V := V) (A := I)).homEquiv
          (X₁ := T) (X₂ := X) (X₃ := E) : _ → _)) := by
  rw [weightedScalarAdjunction_eq_original]

/-- The whole transported inverse function family is the original scalar unadjunct family. -/
theorem weightedScalarAdjunction_inverse_heq :
    HEq (fun (T : V) (X E : EnrichedFunctorCat V I) =>
      (((weightedScalarAdjunction (V := V) (I := I)).homEquiv
        (X₁ := T) (X₂ := X) (X₃ := E)).symm : _ → _))
      (fun (T : V) (X E : EnrichedFunctorCat V I) =>
        (((ScalarLeibniz.parametrizedAdjunction (V := V) (A := I)).homEquiv
          (X₁ := T) (X₂ := X) (X₃ := E)).symm : _ → _)) := by
  rw [weightedScalarAdjunction_eq_original]

/-- The complete original unit transformation family is retained by the typed conversion. -/
theorem weightedScalarAdjunction_unit_heq :
    HEq (fun T => ((weightedScalarAdjunction (V := V) (I := I)).adj T).unit)
      (fun T => ((ScalarLeibniz.parametrizedAdjunction (V := V) (A := I)).adj T).unit) := by
  rw [weightedScalarAdjunction_eq_original]

/-- The complete original counit transformation family is retained by the typed conversion. -/
theorem weightedScalarAdjunction_counit_heq :
    HEq (fun T => ((weightedScalarAdjunction (V := V) (I := I)).adj T).counit)
      (fun T => ((ScalarLeibniz.parametrizedAdjunction (V := V) (A := I)).adj T).counit) := by
  rw [weightedScalarAdjunction_eq_original]

end CategoryTheory.EnrichedFunctorCat.ScalarTensorFunctorValue
