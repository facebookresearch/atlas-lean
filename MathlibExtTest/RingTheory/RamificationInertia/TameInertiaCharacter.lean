/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.RamificationInertia.TameInertiaCharacter

@[expose] public section

open Ideal

universe u v

/-- Exact-source consumer: the original binders and conclusion. -/
theorem exactSource {B : Type u} [CommRing B] {G : Type v} [Group G]
    [MulSemiringAction G B] (𝔓 : Ideal B) [𝔓.IsMaximal] [Finite (B ⧸ 𝔓)]
    {ϖ : B} (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) :
    ∃ θ : 𝔓.inertia G →* (B ⧸ 𝔓)ˣ,
      (∀ (σ : 𝔓.inertia G) (t : B),
        ((θ σ : (B ⧸ 𝔓)ˣ) : B ⧸ 𝔓) = Ideal.Quotient.mk 𝔓 t ↔
          (σ : G) • ϖ - ϖ * t ∈ 𝔓 ^ 2) ∧
      (∀ σ : 𝔓.inertia G, θ σ = 1 ↔ ∀ x : B, (σ : G) • x - x ∈ 𝔓 ^ 2) ∧
        IsCyclic θ.range :=
  Ideal.exists_monoidHom_inertia_residueFieldUnits_ker_iff_of_uniformizer
    𝔓 hϖP hgen hreg

/-- Higher-universe consumer: the ring and the acting group may live in
universes above the ones used by the source statement. -/
theorem exactSourceHigherUniverse {B : Type (u + 2)} [CommRing B]
    {G : Type (v + 1)} [Group G] [MulSemiringAction G B] (𝔓 : Ideal B)
    [𝔓.IsMaximal] [Finite (B ⧸ 𝔓)] {ϖ : B} (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) :
    ∃ θ : 𝔓.inertia G →* (B ⧸ 𝔓)ˣ,
      (∀ (σ : 𝔓.inertia G) (t : B),
        ((θ σ : (B ⧸ 𝔓)ˣ) : B ⧸ 𝔓) = Ideal.Quotient.mk 𝔓 t ↔
          (σ : G) • ϖ - ϖ * t ∈ 𝔓 ^ 2) ∧
      (∀ σ : 𝔓.inertia G, θ σ = 1 ↔ ∀ x : B, (σ : G) • x - x ∈ 𝔓 ^ 2) ∧
        IsCyclic θ.range :=
  Ideal.exists_monoidHom_inertia_residueFieldUnits_ker_iff_of_uniformizer
    𝔓 hϖP hgen hreg

/-- Boundary check: the regularity hypothesis cannot be dropped. With
`ϖ = 0`, every element of `𝔓` trivially differs from a multiple of `ϖ`
only when `𝔓 ⊆ 𝔓 ^ 2`, and `c * ϖ ∈ 𝔓 ^ 2` holds for every `c`, so
regularity would force every coefficient into `𝔓`; in particular the
coefficient chosen for `σ • ϖ` need not be a unit modulo `𝔓`. -/
example : ¬ (∀ c : ℤ, c * (0 : ℤ) ∈ Ideal.span {(2 : ℤ)} ^ 2 →
    c ∈ Ideal.span {(2 : ℤ)}) := by
  intro h
  have h1 := h 1 (by simp)
  have h2 : (2 : ℤ) ∣ 1 := Ideal.mem_span_singleton.mp h1
  norm_num at h2
