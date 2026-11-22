/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalNaiveFibrations
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalSmallObject
public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-!
# The chosen auxiliary functorial factorization

The native small object construction at the regular countable cardinal in
the simplicial value universe factors every arrow through the actual auxiliary
anodyne and naive classes. The named datum retains its intermediate-object
functor and both natural factorization maps.

The two lifting identities and this datum supply the auxiliary weak
factorization system on all simplicial arrows.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe u

namespace SSet.joyalInterval

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

/-- The actual countable small object construction, with its classes identified
as the auxiliary anodyne and naive classes. -/
noncomputable def auxiliaryFunctorialFactorizationData :
    MorphismProperty.FunctorialFactorizationData auxiliaryAnodyneExtensions.{u}
      auxiliaryNaiveFibrations.{u} :=
  (SmallObject.functorialFactorizationData auxiliaryGenerators.{u}
    Cardinal.aleph0.{u}).ofLE le_rfl (by
      simpa only [auxiliaryNaiveFibrations_eq_generatorRlp] using
        (le_rfl : auxiliaryGenerators.{u}.rlp ≤ auxiliaryGenerators.{u}.rlp))

/-- The specified datum supplies functorial factorization for the exact
auxiliary classes. -/
instance auxiliaryAnodyneExtensions.hasFunctorialFactorization :
    MorphismProperty.HasFunctorialFactorization auxiliaryAnodyneExtensions.{u}
      auxiliaryNaiveFibrations.{u} where
  nonempty_functorialFactorizationData := ⟨auxiliaryFunctorialFactorizationData⟩

/-- The auxiliary classes form a weak factorization system on every arrow. -/
instance auxiliaryAnodyneExtensions.isWeakFactorizationSystem :
    MorphismProperty.IsWeakFactorizationSystem auxiliaryAnodyneExtensions.{u}
      auxiliaryNaiveFibrations.{u} where
  rlp := rfl
  llp := by
    rw [auxiliaryNaiveFibrations_eq_generatorRlp]
    rfl

end SSet.joyalInterval
