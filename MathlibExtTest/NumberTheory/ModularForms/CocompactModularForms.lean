/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.CocompactModularForms

@[expose] public section

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

-- Consumer with the original binders.
example (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    [DiscreteTopology ↥Γ]
    (hcpt : ∃ K : Set ℍ, IsCompact K ∧ ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K) :
    (∀ f : ModularForm Γ 0, ∃ c : ℂ, (f : ℍ → ℂ) = fun _ => c) ∧
    (∀ k : ℤ, k < 0 → ∀ f : ModularForm Γ k, (f : ℍ → ℂ) = 0) :=
  ModularCurve.modularForm_eq_const_and_eq_zero_of_isCompact Γ hcpt

-- The zero form is the constant zero form in weight zero, and it
-- vanishes in negative weight, as the theorem requires.
example (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    [DiscreteTopology ↥Γ]
    (hcpt : ∃ K : Set ℍ, IsCompact K ∧ ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K) :
    (∃ c : ℂ, ((0 : ModularForm Γ 0) : ℍ → ℂ) = fun _ => c) ∧
    (∀ k : ℤ, k < 0 → ((0 : ModularForm Γ k) : ℍ → ℂ) = 0) := by
  obtain ⟨h0, hneg⟩ :=
    ModularCurve.modularForm_eq_const_and_eq_zero_of_isCompact Γ hcpt
  exact ⟨h0 0, fun k hk => hneg k hk 0⟩
