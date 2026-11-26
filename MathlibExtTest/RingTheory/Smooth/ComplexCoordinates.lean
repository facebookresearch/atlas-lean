/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The examples restate the theorem type from
`Theorems/Thm_Algebra_exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2, without its `Algebra.FiniteType` hypothesis.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.RingTheory.Smooth.ComplexCoordinates

@[expose] public section

open Topology

example (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S]
    (hsm : Algebra.Smooth ℂ S)
    {n : ℕ} (hrank : Module.rank S (KaehlerDifferential ℂ S) = n)
    (σ₀ : S →ₐ[ℂ] ℂ) (t : Fin n → S)
    (hdt : (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule S (KaehlerDifferential ℂ S)) ⊔
        Submodule.span S (Set.range fun i : Fin n => KaehlerDifferential.D ℂ S (t i)) = ⊤) :
    ∃ (r : ℝ) (𝒰 : Set (S →ₐ[ℂ] ℂ)), 0 < r ∧ σ₀ ∈ 𝒰 ∧
      Set.BijOn (fun σ : S →ₐ[ℂ] ℂ => fun i : Fin n => σ (t i)) 𝒰
        (Metric.ball (fun i : Fin n => σ₀ (t i)) r) ∧
      (∀ s : S, ∃ F : (Fin n → ℂ) → ℂ,
        DifferentiableOn ℂ F (Metric.ball (fun i : Fin n => σ₀ (t i)) r) ∧
        ∀ σ ∈ 𝒰, σ s = F (fun i : Fin n => σ (t i))) ∧
      (∀ σ ∈ 𝒰, ∃ (fs : Finset S) (ε : ℝ), 0 < ε ∧
        ∀ σ' : S →ₐ[ℂ] ℂ, (∀ s ∈ fs, ‖σ' s - σ s‖ < ε) → σ' ∈ 𝒰) :=
  Algebra.exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential
    S hsm hrank σ₀ t hdt

universe u

example (S : Type u) [CommRing S] [IsDomain S] [Algebra ℂ S]
    (hsm : Algebra.Smooth ℂ S)
    {n : ℕ} (hrank : Module.rank S (KaehlerDifferential ℂ S) = n)
    (σ₀ : S →ₐ[ℂ] ℂ) (t : Fin n → S)
    (hdt : (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule S (KaehlerDifferential ℂ S)) ⊔
        Submodule.span S (Set.range fun i : Fin n => KaehlerDifferential.D ℂ S (t i)) = ⊤) :
    ∃ (r : ℝ) (𝒰 : Set (S →ₐ[ℂ] ℂ)), 0 < r ∧ σ₀ ∈ 𝒰 ∧
      Set.BijOn (fun σ : S →ₐ[ℂ] ℂ => fun i : Fin n => σ (t i)) 𝒰
        (Metric.ball (fun i : Fin n => σ₀ (t i)) r) := by
    obtain ⟨r, 𝒰, hr, hσ, hbij, -, -⟩ :=
      Algebra.exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential
        S hsm hrank σ₀ t hdt
    exact ⟨r, 𝒰, hr, hσ, hbij⟩

/-- Smoothness known only through an algebra equivalence suffices: there is no
`Algebra.FiniteType ℂ S` instance in scope, and none is needed. -/
example (S T : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [CommRing T] [Algebra ℂ T]
    [Algebra.Smooth ℂ T] (e : T ≃ₐ[ℂ] S)
    {n : ℕ} (hrank : Module.rank S (KaehlerDifferential ℂ S) = n)
    (σ₀ : S →ₐ[ℂ] ℂ) (t : Fin n → S)
    (hdt : (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule S (KaehlerDifferential ℂ S)) ⊔
        Submodule.span S (Set.range fun i : Fin n => KaehlerDifferential.D ℂ S (t i)) = ⊤) :
    ∃ (r : ℝ) (𝒰 : Set (S →ₐ[ℂ] ℂ)), 0 < r ∧ σ₀ ∈ 𝒰 ∧
      Set.BijOn (fun σ : S →ₐ[ℂ] ℂ => fun i : Fin n => σ (t i)) 𝒰
        (Metric.ball (fun i : Fin n => σ₀ (t i)) r) := by
  obtain ⟨r, 𝒰, hr, hσ, hbij, -, -⟩ :=
    Algebra.exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential
      S (Algebra.Smooth.of_equiv e) hrank σ₀ t hdt
  exact ⟨r, 𝒰, hr, hσ, hbij⟩
