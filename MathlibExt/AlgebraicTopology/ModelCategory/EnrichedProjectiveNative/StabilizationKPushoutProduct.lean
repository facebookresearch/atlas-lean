/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationK
import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductGeneratorCriterion

/-!
# Actual original K labels in pushout-product tests

The native K family is the original level horn family together with its
actual correlated boundary and mapping-cylinder arrows. For a separately
selected tensor on the same original carrier, these tests retain every
original stabilization and boundary label. Native tensor comparison,
generator membership and stable monoidality are further proof obligations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MorphismProperty
open scoped MonoidalCategory CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
variable [MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)]
  [HasPushouts (EnrichedFunctorCat PointedCGWH.{u, v} I)]

/-- Actual extra-generator products are tested on every complete original
pair of labels, with the literal full original generator arrow. -/
theorem additionalGenerators_pushoutProductLe_iff
    (P Q : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    PushoutProductLe (additionalGenerators s) P Q ↔
      ∀ (l : L) (m : ℕ) ⦃X Y : EnrichedFunctorCat PointedCGWH.{u, v} I⦄
        (j : X ⟶ Y), P j → Q ((Arrow.mk (generatorMap s l m) □ Arrow.mk j).hom) := by
  constructor
  · intro h l m X Y j hj
    exact h _ j (generatorMap_mem s l m) hj
  · intro h A B X Y i j hi hj
    obtain ⟨⟨l, m⟩⟩ := hi
    exact h l m j hj

/-- The second tensor orientation retains the same original correlated
labels and the same full generator map. -/
theorem additionalGenerators_rightPushoutProductLe_iff
    (P Q : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    PushoutProductLe P (additionalGenerators s) Q ↔
      ∀ ⦃X Y : EnrichedFunctorCat PointedCGWH.{u, v} I⦄ (i : X ⟶ Y), P i →
        ∀ (l : L) (m : ℕ), Q ((Arrow.mk i □ Arrow.mk (generatorMap s l m)).hom) := by
  constructor
  · intro h X Y i hi l m
    exact h i _ hi (generatorMap_mem s l m)
  · intro h X Y A B i j hi hj
    obtain ⟨⟨l, m⟩⟩ := hj
    exact h i hi l m

/-- The full original K product test is exactly the level-horn test and
the complete original additional-generator test, with no family changed. -/
theorem generators_pushoutProductLe_iff
    (P Q : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    PushoutProductLe (generators s) P Q ↔
      PushoutProductLe (levelJ (I := I)) P Q ∧
        ∀ (l : L) (m : ℕ) ⦃X Y : EnrichedFunctorCat PointedCGWH.{u, v} I⦄
          (j : X ⟶ Y), P j → Q ((Arrow.mk (generatorMap s l m) □ Arrow.mk j).hom) := by
  rw [← additionalGenerators_pushoutProductLe_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro A B X Y i j hi hj
      exact h i j ((generators_iff s i).mpr (Or.inl hi)) hj
    · intro A B X Y i j hi hj
      exact h i j ((generators_iff s i).mpr (Or.inr hi)) hj
  · rintro ⟨hJ, hK⟩ A B X Y i j hi hj
    rcases (generators_iff s i).mp hi with hi | hi
    · exact hJ i j hi hj
    · exact hK i j hi hj

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
