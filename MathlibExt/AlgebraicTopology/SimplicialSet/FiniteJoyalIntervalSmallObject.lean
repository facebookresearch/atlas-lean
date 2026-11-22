/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalGeneratorProperties
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# The finite-domain auxiliary small object argument

Every actual inner-horn or finite-interval endpoint-corner generator has
a finitely presentable source. The native small object conditions hold
at the regular cardinal `ℵ₀` in the simplicial value universe, so the
actual auxiliary family permits the small object argument at that size.

The ordinal iteration at this cardinal is countable. Its successor
stages may attach arbitrary small families of squares. No model structure
or local-presentability theorem is required.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace SSet.joyalInterval

/-- The source of every actual auxiliary generator is finitely presentable
relative to the simplicial value universe. -/
lemma auxiliaryGenerators.isFinitelyPresentable_source {X Y : SSet.{u}}
    {i : X ⟶ Y} (hi : auxiliaryGenerators i) : IsFinitelyPresentable.{u} X := by
  have : X.Finite := (auxiliaryGenerators.finite hi).1
  infer_instance

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

/-- The regular countable cardinal satisfies the actual source-Hom,
smallness and colimit conditions for the auxiliary family. -/
instance auxiliaryGenerators.isCardinalForSmallObjectArgument_aleph0 :
    MorphismProperty.IsCardinalForSmallObjectArgument auxiliaryGenerators.{u}
      Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A :=
      auxiliaryGenerators.isFinitelyPresentable_source hi
    infer_instance

/-- The literal auxiliary family permits the small object argument at
the same universe as its simplicial-set values. -/
instance auxiliaryGenerators.hasSmallObjectArgument :
    MorphismProperty.HasSmallObjectArgument.{u} auxiliaryGenerators.{u} where
  exists_cardinal := ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance, inferInstance⟩

end SSet.joyalInterval
