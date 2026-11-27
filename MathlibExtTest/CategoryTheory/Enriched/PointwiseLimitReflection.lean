/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Enriched.PointwiseLimitReflection
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Equalizer lifts from evaluated enriched cones

This client constructs and characterizes lifts through an arbitrary supplied
enriched equalizer cone using only its evaluated limits. No model structure,
chosen limit object, ordinary category on the enriched index, or global limit
existence is required.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uA uV vV
open CategoryTheory Limits
open scoped MonoidalClosed

namespace EnrichedPointwiseLimitReflectionClient

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {X Y : EnrichedFunctorCat V A} (f g : X ⟶ Y) (c : Fork f g)
  (hc : ∀ a : A, IsLimit ((EnrichedFunctorCat.evaluation a).mapCone c))
  (Z : EnrichedFunctorCat V A) (k : Z ⟶ X) (hk : k ≫ f = k ≫ g)

/-- Construct the genuine enriched equalizer lift of the given equalizing arrow. -/
def evaluatedEqualizerLift : Z ⟶ c.pt :=
  (EnrichedFunctorCat.evaluationJointlyReflectsLimits c hc).lift (Fork.ofι k hk)

/-- The constructed lift factors the actual arrow through the supplied cone leg. -/
theorem evaluatedEqualizerLift_ι :
    evaluatedEqualizerLift f g c hc Z k hk ≫ c.ι = k :=
  Fork.IsLimit.lift_ι (EnrichedFunctorCat.evaluationJointlyReflectsLimits c hc)

/-- Every component is the evaluated lift of the same original equalizing arrow. -/
theorem evaluatedEqualizerLift_component (a : A) :
    EnrichedFunctorCat.component (evaluatedEqualizerLift f g c hc Z k hk) a =
      (hc a).lift ((EnrichedFunctorCat.evaluation a).mapCone (Fork.ofι k hk)) :=
  EnrichedFunctorCat.liftOfEvaluations_component c hc (Fork.ofι k hk) a

/-- Any genuine enriched factorization of that arrow is the constructed lift. -/
theorem evaluatedEqualizerLift_unique (m : Z ⟶ c.pt) (hm : m ≫ c.ι = k) :
    m = evaluatedEqualizerLift f g c hc Z k hk := by
  apply Fork.IsLimit.hom_ext (EnrichedFunctorCat.evaluationJointlyReflectsLimits c hc)
  exact hm.trans (evaluatedEqualizerLift_ι f g c hc Z k hk).symm

end EnrichedPointwiseLimitReflectionClient
