/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Pointwise closure properties of native intersections

An intersection of actual two-out-of-three morphism classes has the same
property, and intersections of retract-stable classes remain retract
stable. The proofs retain each original component test. These named
closure dictionaries add no global instance or model assumption.
-/

universe w v u
open CategoryTheory

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] {I : Type w} (W : I → MorphismProperty C)

/-- Every original component two-out-of-three test is retained by their actual intersection. -/
theorem hasTwoOutOfThreeProperty_iInf [∀ i, (W i).HasTwoOutOfThreeProperty] :
    (iInf W).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg := by
    apply (iInf_iff W f).mpr
    intro i
    exact (W i).of_postcomp f g ((iInf_iff W g).mp hg i) ((iInf_iff W (f ≫ g)).mp hfg i)
  of_precomp f g hf hfg := by
    apply (iInf_iff W g).mpr
    intro i
    exact (W i).of_precomp f g ((iInf_iff W f).mp hf i) ((iInf_iff W (f ≫ g)).mp hfg i)

/-- The actual intersection preserves each original arrow-retract test. -/
theorem isStableUnderRetracts_iInf [∀ i, (W i).IsStableUnderRetracts] :
    (iInf W).IsStableUnderRetracts where
  of_retract h hg := by
    apply (iInf_iff W _).mpr
    intro i
    exact of_retract (P := W i) h ((iInf_iff W _).mp hg i)

end CategoryTheory.MorphismProperty
