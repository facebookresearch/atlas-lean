/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.Perfectoid.DeRhamPeriodRingInvariants

/-! Tests for the de Rham period ring of `ℂ_p`: `B_dR^+` is a discrete valuation ring with
uniformizers `ξ` and `[ε] - 1`, `B_dR` is its fraction field, Fontaine's map `θ` on `B_dR^+` is a
surjective `ℚ_[p]`-algebra map with kernel `(ξ)`, the Galois action fixes `ℚ_[p]` and commutes with
`θ` and with `ℚ̄_p ⊆ B_dR^+`, and `B_dR ^ Gal(ℚ̄_p/K) = K`. -/

open Ideal WittVector MathlibExt.AlgebraicGeometry.HodgeTateComparison PadicComplexInt

variable (p : ℕ) [Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p
local notation "𝔹" => BDeRham 𝓞_ℂ_[p] p

example : IsDiscreteValuationRing 𝔹⁺ := inferInstance

example : IsFractionRing 𝔹⁺ 𝔹 := inferInstance

-- `B_dR` is a field, so nonzero elements are invertible.
example (x : 𝔹) (hx : x ≠ 0) : x * x⁻¹ = 1 := mul_inv_cancel₀ hx

example : IsLocalRing.maximalIdeal 𝔹⁺ = span {algebraMap 𝔸 𝔹⁺ (xi p)} :=
  maximalIdeal_bDeRhamPlus p

example : Irreducible (algebraMap 𝔸 𝔹⁺ (xi p)) := irreducible_algebraMap_xi p

example : Irreducible (algebraMap 𝔸 𝔹⁺ (teichmuller p (epsilon p) - 1)) :=
  irreducible_algebraMap_teichmuller_epsilon_sub_one p

-- `θ` is a surjective `ℚ_[p]`-algebra map with kernel `(ξ)`; it extends `θ` on `W(𝓞_ℂ_[p]♭)`.
example : Function.Surjective (fontaineThetaBDeRhamPlus p) :=
  fontaineThetaBDeRhamPlus_surjective p

example (c : ℚ_[p]) :
    fontaineThetaBDeRhamPlus p (algebraMap ℚ_[p] 𝔹⁺ c) = algebraMap ℚ_[p] ℂ_[p] c :=
  (fontaineThetaBDeRhamPlus p).commutes c

example : fontaineThetaBDeRhamPlus p (algebraMap 𝔸 𝔹⁺ (xi p)) = 0 := by
  rw [fontaineThetaBDeRhamPlus_algebraMap_wittVector, fontaineTheta_xi]
  rfl

example : RingHom.ker (fontaineThetaBDeRhamPlus p) = span {algebraMap 𝔸 𝔹⁺ (xi p)} :=
  ker_fontaineThetaBDeRhamPlus p

-- The Galois action on `B_dR` is the map induced by the action on `𝓞_ℂ_[p]`, fixes `ℚ_[p]`, and
-- extends the action on `B_dR^+`; `θ` is equivariant.
example (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    (galoisBDeRham p σ : 𝔹 →+* 𝔹) = BDeRham.mapOfRingEquiv p (integralGalois p σ) :=
  rfl

example (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (c : ℚ_[p]) :
    galoisBDeRham p σ (algebraMap ℚ_[p] 𝔹 c) = algebraMap ℚ_[p] 𝔹 c :=
  (galoisBDeRham p σ).commutes c

example (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : 𝓞_ℂ_[p]) :
    ((integralGalois p σ x : 𝓞_ℂ_[p]) : ℂ_[p]) = completionGalois p σ x :=
  coe_integralGalois p σ x

example (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : 𝔹⁺) :
    fontaineThetaBDeRhamPlus p (galoisBDeRhamPlus p σ x) =
      completionGalois p σ (fontaineThetaBDeRhamPlus p x) :=
  fontaineThetaBDeRhamPlus_galoisBDeRhamPlus p σ x

-- `ℚ̄_p ⊆ B_dR^+`: `θ` restricts to the inclusion `ℚ̄_p ⊆ ℂ_[p]`, and the embedding is equivariant.
example (x : PadicAlgCl p) :
    fontaineThetaBDeRhamPlus p (padicAlgClToBDeRhamPlus p x) = (x : ℂ_[p]) :=
  fontaineThetaBDeRhamPlus_padicAlgClToBDeRhamPlus p x

example (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p) :
    galoisBDeRham p σ (algebraMap 𝔹⁺ 𝔹 (padicAlgClToBDeRhamPlus p x)) =
      algebraMap 𝔹⁺ 𝔹 (padicAlgClToBDeRhamPlus p (σ x)) := by
  rw [galoisBDeRham_algebraMap, galoisBDeRhamPlus_padicAlgClToBDeRhamPlus]

-- The Galois action on `[ε] - 1` is multiplication by a lift of the cyclotomic character.
example (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    ∃ w : 𝔹⁺, galoisBDeRhamPlus p σ (algebraMap 𝔸 𝔹⁺ (teichmuller p (epsilon p) - 1)) =
        algebraMap 𝔸 𝔹⁺ (teichmuller p (epsilon p) - 1) * w ∧
      fontaineThetaBDeRhamPlus p w = algebraMap ℚ_[p] ℂ_[p] (cyclotomicScalar p σ) :=
  exists_galoisBDeRhamPlus_algebraMap_teichmuller_epsilon_sub_one p σ

-- `B_dR ^ Gal(ℚ̄_p/K) = K`, and `B_dR ^ Gal(ℚ̄_p/ℚ_p) = ℚ_p`.
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    {x : 𝔹 | ∀ σ ∈ K.fixingSubgroup, galoisBDeRham p σ x = x} =
      Set.range fun y : K => algebraMap 𝔹⁺ 𝔹 (padicAlgClToBDeRhamPlus p y) :=
  fixedPoints_bDeRham_eq_range p K

example (x : 𝔹) (hx : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, galoisBDeRham p σ x = x) :
    ∃ c : ℚ_[p], x = algebraMap ℚ_[p] 𝔹 c :=
  exists_eq_algebraMap_of_forall_galoisBDeRham_eq_self p hx

-- The elements of `ℚ̄_p` fixed by `Gal(ℚ̄_p/K)` lie in `K`, so their images in `B_dR` are
-- invariants.
example (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (y : K)
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hσ : σ ∈ K.fixingSubgroup) :
    galoisBDeRham p σ (algebraMap 𝔹⁺ 𝔹 (padicAlgClToBDeRhamPlus p y)) =
      algebraMap 𝔹⁺ 𝔹 (padicAlgClToBDeRhamPlus p y) := by
  have h : (algebraMap 𝔹⁺ 𝔹 (padicAlgClToBDeRhamPlus p y)) ∈
      {x : 𝔹 | ∀ σ ∈ K.fixingSubgroup, galoisBDeRham p σ x = x} := by
    rw [fixedPoints_bDeRham_eq_range]
    exact ⟨y, rfl⟩
  exact h σ hσ

-- Lifting embeddings through a henselian residue map, in the generic form.
example {K R Ω L : Type*} [Field K] [CommRing R] [Algebra K R] [Field Ω] [Algebra K Ω] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsDomain R]
    (θ : R →ₐ[K] Ω) (hsurj : Function.Surjective θ) [HenselianRing R (RingHom.ker θ)]
    (hunit : ∀ y, θ y ≠ 0 → IsUnit y) (ι : L →ₐ[K] Ω) :
    ∃! ι₀ : L →ₐ[K] R, θ.comp ι₀ = ι := by
  obtain ⟨ι₀, h⟩ := AlgHom.exists_comp_eq_of_henselianRing θ hsurj hunit ι
  exact ⟨ι₀, h, fun f hf => AlgHom.ext_of_comp_eq θ (hf.trans h.symm)⟩
