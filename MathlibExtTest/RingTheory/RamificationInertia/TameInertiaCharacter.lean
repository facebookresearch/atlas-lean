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
private theorem exactSource {B : Type u} [CommRing B] {G : Type v} [Group G]
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
private theorem exactSourceHigherUniverse {B : Type (u + 2)} [CommRing B]
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

/-!
### Boundary check: `hreg` cannot be dropped

The model is `B = ZMod 2`, `𝔓 = ⊥` and `ϖ = 0`, acted on by `RingAut (ZMod 2)`.
Every hypothesis of the theorem except `hreg` holds there, and `hreg` fails. So
does the conclusion: as `ϖ = 0`, its coefficient characterization would make the
unit `θ 1 = 1` equal to the residue class of every `t`, including `t = 0`.
-/

/-- `𝔓 = ⊥` is a maximal ideal of `ZMod 2`. -/
private theorem boundary_isMaximal : (⊥ : Ideal (ZMod 2)).IsMaximal :=
  Ideal.bot_isMaximal

/-- The residue field `ZMod 2 ⧸ ⊥` is finite. -/
private theorem boundary_finite : Finite (ZMod 2 ⧸ (⊥ : Ideal (ZMod 2))) :=
  Finite.of_surjective _ Ideal.Quotient.mk_surjective

/-- `ϖ = 0` lies in `𝔓 = ⊥`. -/
private theorem boundary_mem : (0 : ZMod 2) ∈ (⊥ : Ideal (ZMod 2)) :=
  Ideal.zero_mem _

/-- `ϖ = 0` generates `𝔓 = ⊥` modulo `𝔓 ^ 2`, since `0` is the only element of `⊥`. -/
private theorem boundary_gen :
    ∀ x ∈ (⊥ : Ideal (ZMod 2)), ∃ y : ZMod 2, x - 0 * y ∈ (⊥ : Ideal (ZMod 2)) ^ 2 := by
  intro x hx
  refine ⟨0, ?_⟩
  rw [Ideal.mem_bot.mp hx, zero_mul, sub_zero]
  exact Ideal.zero_mem _

/-- `hreg` fails: `1 * 0 ∈ ⊥ ^ 2`, but `1 ∉ ⊥`. -/
private theorem boundary_not_reg :
    ¬ ∀ c : ZMod 2, c * 0 ∈ (⊥ : Ideal (ZMod 2)) ^ 2 → c ∈ (⊥ : Ideal (ZMod 2)) := fun h =>
  one_ne_zero (Ideal.mem_bot.mp (h 1 (by rw [mul_zero]; exact Ideal.zero_mem _)))

/-- Without `hreg` the theorem is false: the model above satisfies every other
hypothesis, and the conclusion fails there. -/
example : ¬ ∀ (B : Type) [CommRing B] (G : Type) [Group G] [MulSemiringAction G B]
    (𝔓 : Ideal B) [𝔓.IsMaximal] [Finite (B ⧸ 𝔓)] (ϖ : B), ϖ ∈ 𝔓 →
    (∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) →
    ∃ θ : 𝔓.inertia G →* (B ⧸ 𝔓)ˣ,
      (∀ (σ : 𝔓.inertia G) (t : B),
        ((θ σ : (B ⧸ 𝔓)ˣ) : B ⧸ 𝔓) = Ideal.Quotient.mk 𝔓 t ↔
          (σ : G) • ϖ - ϖ * t ∈ 𝔓 ^ 2) ∧
      (∀ σ : 𝔓.inertia G, θ σ = 1 ↔ ∀ x : B, (σ : G) • x - x ∈ 𝔓 ^ 2) ∧
        IsCyclic θ.range := by
  intro h
  obtain ⟨θ, hθ, -, -⟩ := @h (ZMod 2) _ (RingAut (ZMod 2)) _ _ ⊥ boundary_isMaximal
    boundary_finite 0 boundary_mem boundary_gen
  have h1 := (hθ 1 0).mpr (by rw [smul_zero, mul_zero, sub_zero]; exact Ideal.zero_mem _)
  rw [map_one, Units.val_one, ← map_one (Ideal.Quotient.mk ⊥), Ideal.Quotient.eq,
    sub_zero] at h1
  exact one_ne_zero (Ideal.mem_bot.mp h1)
