/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryMatchingLift
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure

/-!
# Trivial Kan–Quillen fibrations from actual matching surjectivity

Surjectivity of every actual relative matching map supplies every
original boundary lift. The established boundary generators then give
a genuine trivial fibration in the original Kan–Quillen model.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet.modelCategoryQuillen

/-- Surjectivity of all actual relative matching maps proves a genuine Kan–Quillen trivial
fibration. -/
theorem trivialFibration_of_relativeMatching_surjective {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : ∀ n : ℕ, Function.Surjective (SimplicialObject.relativeMatchingMap f n)) :
    trivialFibrations SSet.{u} f := by
  rw [← cofibrations_rlp, cofibrations_eq, SSet.rlp_monomorphisms]
  intro A B i hi
  obtain ⟨n⟩ := hi
  exact BoundaryMatching.hasLiftingProperty_boundary_of_relativeMatching_surjective f n (hf n)

/-- Epimorphic actual Type-valued relative matching maps supply the same genuine trivial
fibration. -/
theorem trivialFibration_of_relativeMatching_epimorphisms {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : ∀ n : ℕ, MorphismProperty.epimorphisms (Type u)
      (SimplicialObject.relativeMatchingMap f n)) : trivialFibrations SSet.{u} f :=
  trivialFibration_of_relativeMatching_surjective f
    (fun n => (CategoryTheory.epi_iff_surjective _).mp (hf n))

end SSet.modelCategoryQuillen
