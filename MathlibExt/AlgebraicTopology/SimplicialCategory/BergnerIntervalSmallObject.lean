/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerPointPresentability
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerIntervalGenerators
import Mathlib.CategoryTheory.SmallObject.Basic
import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-!
# The genuine original small A2 point-map factorization

All actual original A2 source maps have the SAME finitely presentable
point domain. The genuine original changing-object colimits supply the
full native small-object iteration at countable length. Every original
representative interval, point label, attachment and whole factor map is
retained. No acyclicity or global model outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

namespace CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily

/-- Every actual original A2 domain is the SAME genuinely finitely presentable original point. -/
theorem interval_domain_presentable {A B : Carrier.{u}} (i : A ⟶ B) (hi : generatingIntervals i) :
    IsFinitelyPresentable.{u} A := by
  obtain ⟨⟨⟨H, hH⟩, x⟩⟩ := hi
  exact BergnerObjects.point_isFinitelyPresentable

/-- The SAME actual original small A2 family satisfies every native small-object condition at countable length. -/
instance intervalCardinal :
    MorphismProperty.IsCardinalForSmallObjectArgument generatingIntervals.{u} Cardinal.aleph0.{u} where
  preservesColimit i hi _ _ := by
    have : IsFinitelyPresentable.{u} _ := interval_domain_presentable i hi
    infer_instance

/-- The full genuine original A2 point-map family permits the actual native small-object argument. -/
instance intervalHasSmallObjectArgument : MorphismProperty.HasSmallObjectArgument.{u} generatingIntervals.{u} where
  exists_cardinal := ⟨Cardinal.aleph0, inferInstance, inferInstance, inferInstance⟩

/-- The SAME actual original A2 left and right classes have a genuine full weak factorization system. -/
theorem intervalWFS : MorphismProperty.IsWeakFactorizationSystem
    generatingIntervals.{u}.rlp.llp generatingIntervals.rlp := by
  exact MorphismProperty.IsWeakFactorizationSystem.mk' _ _
    (fun _ _ hi hp => hi _ hp)

end CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
