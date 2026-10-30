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

universe u

/-- The full invariance API is available throughout its supported universe. -/
example {k G H : Type u} [CommRing k] [Group G] [Group H]
    (e : G ≃* H) (A : Rep k G) (B : Rep k H)
    (φ : A ≅ Rep.res e.toMonoidHom B) (n : ℕ) :
    Nonempty (groupCohomology A n ≃ₗ[k] groupCohomology B n) := by
  obtain ⟨ψ, -⟩ := groupCohomology.nonempty_linearEquiv_of_iso_res_mulEquiv e A B φ n
  exact ⟨ψ⟩

/-- The identity-isomorphism smoke test works in every supported universe. -/
example {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (n : ℕ) :
    Nonempty (groupCohomology A n ≃ₗ[k] groupCohomology A n) := by
  obtain ⟨ψ, -⟩ := groupCohomology.nonempty_linearEquiv_of_iso_res_mulEquiv
    (MulEquiv.refl G) A A (Iso.refl _) n
  exact ⟨ψ⟩

/-- The invariance theorem applies to genuine higher-universe representations. -/
example
    (A : Rep.{1, 1, 1} (ULift.{1} ℚ) (ULift.{1} (Multiplicative ℤ))) (n : ℕ) :
    Nonempty (groupCohomology A n ≃ₗ[ULift.{1} ℚ] groupCohomology A n) := by
  obtain ⟨ψ, -⟩ := groupCohomology.nonempty_linearEquiv_of_iso_res_mulEquiv
    (MulEquiv.refl (ULift.{1} (Multiplicative ℤ))) A A (Iso.refl _) n
  exact ⟨ψ⟩
