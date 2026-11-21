/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Smooth.ComplexCoordinates

@[expose] public section

open Topology

example (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S]
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

example (S : Type u) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S]
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
