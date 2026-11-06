/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCo1GeometryPoints

/-! The actual Conway geometry point vectors span the entire binary Leech module. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual point span is invariant under the genuine Conway action. -/
theorem generatedCo1GeometryPointSpan_action (g : Co1) (v : Fin 24 → ZMod 2)
    (hv : v ∈ generatedCo1GeometryPointSpan) :
    co1BinaryAction g v ∈ generatedCo1GeometryPointSpan := by
  have hle : generatedCo1GeometryPointSpan ≤
      generatedCo1GeometryPointSpan.comap (co1BinaryAction g).toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx
    exact Submodule.subset_span (generatedCo1GeometryPoints_action g x hx)
  exact hle hv

/-- Actual frame-class points span the whole 24-dimensional binary Conway module. -/
theorem generatedCo1GeometryPointSpan_eq_top : generatedCo1GeometryPointSpan = ⊤ := by
  rcases co1BinaryAction_invariant_subspace_dichotomy generatedCo1GeometryPointSpan
    generatedCo1GeometryPointSpan_action with hzero | htop
  · have hz : ∀ x : generatedCo1GeometryPoints, x.val = 0 := by
      intro x
      have hx : x.val ∈ generatedCo1GeometryPointSpan := Submodule.subset_span x.property
      rw [hzero] at hx
      exact hx
    have : Subsingleton generatedCo1GeometryPoints := ⟨fun x y =>
      Subtype.ext ((hz x).trans (hz y).symm)⟩
    have hcard := Nat.card_le_card_of_injective
      (f := fun _ : generatedCo1GeometryPoints => ())
      (fun _ _ _ => Subsingleton.elim _ _)
    norm_num only [Nat.card_unique] at hcard
    rw [generatedCo1GeometryPoints_card] at hcard
    omega
  · exact htop

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
