/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.GroupCohomology.Invariance

open CategoryTheory groupCohomology Rep

/-- Smoke test: cohomology is invariant under the identity group isomorphism. -/
example {G : Type} [Group G] (A : Rep ℚ G) (n : ℕ) :
    Nonempty (groupCohomology A n ≃ₗ[ℚ] groupCohomology A n) := by
  obtain ⟨ψ, -⟩ := groupCohomology.nonempty_linearEquiv_of_iso_res_mulEquiv
    (MulEquiv.refl G) A A (Iso.refl _) n
  exact ⟨ψ⟩
