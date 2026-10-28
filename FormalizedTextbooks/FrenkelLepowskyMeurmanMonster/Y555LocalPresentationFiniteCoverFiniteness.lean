/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual quotient finiteness from finite original-presentation transversal certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationFiniteCover

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Inverse representatives surject onto the actual left-coset quotient of any finite cover. -/
theorem y322Presentation_quotient_surjective_of_cover {size : ℕ}
    (K : Subgroup Y322Presentation) (representative : Fin size → Y322Presentation)
    (cover : ∀ g : Y322Presentation, ∃ h ∈ K, ∃ i : Fin size, g = h * representative i) :
    Function.Surjective
      (fun i : Fin size => (QuotientGroup.mk (representative i)⁻¹ : Y322Presentation ⧸ K)) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨h, hh, i, hi⟩ := cover g⁻¹
  refine ⟨i, QuotientGroup.eq.mpr ?_⟩
  have hg : g = (representative i)⁻¹ * h⁻¹ := by
    simpa only [mul_inv_rev, inv_inv] using congrArg (fun x => x⁻¹) hi
  rw [inv_inv, hg, ← mul_assoc, mul_inv_cancel, one_mul]
  exact K.inv_mem hh

/-- A finite actual transversal cover establishes quotient finiteness directly. -/
theorem y322Presentation_quotient_finite_of_cover {size : ℕ}
    (K : Subgroup Y322Presentation) (representative : Fin size → Y322Presentation)
    (cover : ∀ g : Y322Presentation, ∃ h ∈ K, ∃ i : Fin size, g = h * representative i) :
    Finite (Y322Presentation ⧸ K) := by
  exact Finite.of_surjective _
    (y322Presentation_quotient_surjective_of_cover K representative cover)

/-- Finite actual transversal certificates establish finite index, beyond a natural-card bound. -/
theorem y322Presentation_finiteIndex_of_cover {size : ℕ}
    (K : Subgroup Y322Presentation) (representative : Fin size → Y322Presentation)
    (cover : ∀ g : Y322Presentation, ∃ h ∈ K, ∃ i : Fin size, g = h * representative i) :
    K.FiniteIndex := by
  let := y322Presentation_quotient_finite_of_cover K representative cover
  exact Subgroup.finiteIndex_of_finite_quotient

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
