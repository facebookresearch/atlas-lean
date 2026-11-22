/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalGeneratorProperties

/-!
# Public clients for countable finite auxiliary generators

Consumers recover countable indexing by the actual arrows, finite total
nondegenerate source and target sets, and monomorphism cancellation from
membership alone.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory
open SSet.joyalInterval

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalGeneratorProperties

/-- Membership gives finiteness of all nondegenerate simplices at once,
not just finiteness in each fixed degree. -/
theorem member_finite_nonDegenerate {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : auxiliaryGenerators f) : _root_.Finite X.N ∧ _root_.Finite Y.N := by
  obtain ⟨hX, hY⟩ := auxiliaryGenerators.finite hf
  have := hX
  have := hY
  exact ⟨inferInstance, inferInstance⟩

/-- No separate monomorphism assumption is needed to cancel a family member. -/
theorem member_cancel {X Y Z : SSet.{u}} {f : X ⟶ Y}
    (hf : auxiliaryGenerators f) (a b : Z ⟶ X) (h : a ≫ f = b ≫ f) : a = b := by
  have : Mono f := auxiliaryGenerators_le_monomorphisms f hf
  exact (cancel_mono f).mp h

/-- An arbitrary chosen countable presentation supports literal arrow
membership and finite total nondegenerate sources and targets. -/
theorem exists_countable_actual_arrows :
    ∃ (ι : Type u) (_ : Countable ι) (F : ι → Arrow SSet.{u}),
      (∀ {X Y : SSet.{u}} (f : X ⟶ Y),
        auxiliaryGenerators f ↔ ∃ i, Arrow.mk f = F i) ∧
      ∀ i, _root_.Finite (F i).left.N ∧ _root_.Finite (F i).right.N := by
  obtain ⟨ι, hι, F, hF, hprops⟩ := auxiliaryGenerators.exists_countable_finite_generators.{u}
  refine ⟨ι, hι, F, ?_, ?_⟩
  · intro X Y f
    rw [hF]
    simpa only [Arrow.mk_eq] using
      (MorphismProperty.ofHoms_iff (fun i ↦ (F i).hom) f)
  · intro i
    have := (hprops i).2.1
    have := (hprops i).2.2
    exact ⟨inferInstance, inferInstance⟩

end MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalGeneratorProperties
