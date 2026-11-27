/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_GaloisRep_Residual.lean`,
`Definitions/Def_GaloisRep_DeformationRingData.lean`,
`Definitions/Def_CuspForm_HeckeGaloisRepDatum.lean`,
`Theorems/Thm_GaloisRepAdic_charpoly_baseChangeAlong.lean`,
`P2M/Sol/S_GaloisRepAdic_charpoly_baseChangeAlong.lean`,
`Theorems/Thm_GaloisRepAdic_charpoly_eq_of_isEquiv.lean`,
`P2M/Sol/S_GaloisRepAdic_charpoly_eq_of_isEquiv.lean`,
`Theorems/Thm_CuspForm_HeckeGaloisRepDatum_surjective_of_isEquiv_baseChangeAlong.lean`,
`P2M/Sol/S_CuspForm_HeckeGaloisRepDatum_surjective_of_isEquiv_baseChangeAlong.lean`,
`Theorems/Thm_GaloisRep_DeformationRingData_exists_surjective_algHom_of_heckeGaloisRepDatum.lean`,
and
`P2M/Sol/S_GaloisRep_DeformationRingData_exists_surjective_algHom_of_heckeGaloisRepDatum.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import MathlibExt.FieldTheory.Galois.GaloisRepAdic
public import MathlibExt.NumberTheory.ModularForms.HeckeAlgebra
public import MathlibExt.RingTheory.Valuation.FrobeniusExists

/-!
# From a deformation ring onto a local Hecke algebra

A universal deformation ring `R` of an absolutely irreducible residual Galois
representation `ρbar` (`GaloisRep.DeformationRingData`) and a finite free local
`𝒪`-algebra `T` carrying the Hecke operators together with a Galois representation
whose Frobenius characteristic polynomials are `X² - T_ℓ X + ℓ`
(`CuspForm.HeckeGaloisRepDatum`) are related as follows: when the Hecke
representation is a deformation of `ρbar` of the given type and `T` sees no
operator `U_q`, the universal map `R → T`, a local `𝒪`-algebra map, is surjective.

## Main declarations

* `GaloisRepAdic.charpoly_baseChangeAlong`, `GaloisRepAdic.charpoly_eq_of_isEquiv`.
* `GaloisRep.DeformationRingData`, `CuspForm.HeckeGaloisRepDatum`.
* `GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum`.
-/

@[expose] public section

noncomputable section

universe u v

open Polynomial

namespace GaloisRepAdic

/-- For a local homomorphism `φ : A → B` of local rings, the characteristic polynomial of a
Galois element on the base change along `φ` is the image under `φ` of its characteristic
polynomial on the original representation. -/
theorem charpoly_baseChangeAlong {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v}
    [CommRing B] [IsLocalRing B] (φ : A →+* B) (hφ : IsLocalHom φ)
    (ρ : GaloisRepAdic.{u, v} A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.charpoly ((ρ.baseChangeAlong φ hφ).ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).map φ := by
  let : Algebra A B := φ.toAlgebra
  exact LinearMap.charpoly_baseChange (ρ.ρ σ) B

/-- Equivalent adic Galois representations over a local ring have the same characteristic
polynomial at every Galois element. -/
theorem charpoly_eq_of_isEquiv {A : Type u} [CommRing A] [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic.{u, v} A} (h : ρ₁.IsEquiv ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.charpoly (ρ₁.ρ σ) = LinearMap.charpoly (ρ₂.ρ σ) := by
  obtain ⟨e⟩ := h
  have hconj : ρ₂.ρ σ = (e.toLinearEquiv : ρ₁.V →ₗ[A] ρ₂.V) ∘ₗ ρ₁.ρ σ ∘ₗ
      (e.toLinearEquiv.symm : ρ₂.V →ₗ[A] ρ₁.V) := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply]
    exact (e.toIntertwiningMap.isIntertwining _ _ σ x).symm
  rw [hconj]
  exact (LinearEquiv.charpoly_conj e.toLinearEquiv (ρ₁.ρ σ)).symm

end GaloisRepAdic

namespace GaloisRep

/-- A universal deformation ring for deformations of type `𝒟` of an absolutely irreducible
residual representation `ρbar` over a complete discrete valuation ring `𝒪`: a complete local
noetherian `𝒪`-algebra `R`, whose structure map is local and induces a surjection on residue
fields, with a deformation `ρ` of `ρbar` of type `𝒟` over `R`, such that for every complete
local noetherian `𝒪`-algebra `A` whose structure map is local and induces a surjection on
residue fields, every representation of type `𝒟` over `A` whose residual representation is
equivalent to the base change of `ρbar` is equivalent to the base change of `ρ` along a unique
local `𝒪`-algebra map `R → A`. -/
structure DeformationRingData (𝒪 : Type u) [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (ρbar : ResidualGaloisRep.{u, u} (IsLocalRing.ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type u⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A],
      GaloisRepAdic.{u, u} A → Prop) :
    Type (u + 1) where
  /-- The deformation ring. -/
  R : Type u
  [instCommRing : CommRing R]
  [instIsLocalRing : IsLocalRing R]
  [instIsNoetherianRing : IsNoetherianRing R]
  [instIsAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [instAlgebra : Algebra 𝒪 R]
  [instIsLocalHom : IsLocalHom (algebraMap 𝒪 R)]
  /-- The residue field of `R` is that of `𝒪`. -/
  residue_surjective : Function.Surjective (IsLocalRing.residue R ∘ algebraMap 𝒪 R)
  /-- The residual representation is absolutely irreducible. -/
  absIrr : ρbar.IsAbsolutelyIrreducible
  /-- The universal deformation. -/
  ρ : GaloisRepAdic.{u, u} R
  /-- The universal deformation has type `𝒟`. -/
  isOfType : 𝒟 ρ
  /-- The universal deformation lifts `ρbar`. -/
  residual_isEquiv : ρ.residual.IsEquiv
    (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 R)))
  /-- Universality: over every complete local noetherian `𝒪`-algebra `A` whose structure map
  is local and induces a surjection on residue fields, every representation of type `𝒟` whose
  residual representation is equivalent to the base change of `ρbar` is equivalent to the base
  change of `ρ` along a unique local `𝒪`-algebra map `R → A`. -/
  universal : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Algebra 𝒪 A]
      [IsLocalHom (algebraMap 𝒪 A)],
      Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A) →
      ∀ ρA : GaloisRepAdic.{u, u} A, 𝒟 ρA →
        ρA.residual.IsEquiv
          (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 A))) →
        ∃! φ : R →ₐ[𝒪] A, ∃ hφ : IsLocalHom (φ : R →+* A),
          (ρ.baseChangeAlong (φ : R →+* A) hφ).IsEquiv ρA

attribute [instance] DeformationRingData.instCommRing DeformationRingData.instIsLocalRing
  DeformationRingData.instIsNoetherianRing DeformationRingData.instIsAdicComplete
  DeformationRingData.instAlgebra DeformationRingData.instIsLocalHom

end GaloisRep

namespace CuspForm

/-- Integral Hecke–Galois data at a residual Hecke character `θ`, a ring homomorphism from
the weight-two Hecke algebra `heckeAlgebra N 2 S` to the residue field of `𝒪`. It consists of
a complete local noetherian `𝒪`-algebra `T`, finite and free over `𝒪`, whose structure map is
local and induces a surjection on residue fields; of a ring homomorphism `π` from the Hecke
algebra to `T` that reduces to `θ` and whose image generates `T` as an `𝒪`-algebra, such that
every `𝒪`-valued character of the Hecke algebra reducing to `θ` factors through `π` by an
`𝒪`-algebra map `T → 𝒪`; and of a Galois representation over `T` whose residual
representation is absolutely irreducible and whose Frobenius at every prime `ℓ ∤ N`, `ℓ ∉ S`,
has characteristic polynomial `X² - T_ℓ X + ℓ`. -/
structure HeckeGaloisRepDatum (N : ℕ) [NeZero N] (S : Set ℕ)
    (𝒪 : Type u) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (θ : heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪)
    (T : Type u) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)]
    [Module.Finite 𝒪 T] [Module.Free 𝒪 T] : Type (u + 1) where
  /-- The map from the Hecke algebra. -/
  π : heckeAlgebra N 2 S →+* T
  /-- `π` lifts `θ`. -/
  residue_π : ∀ t : heckeAlgebra N 2 S,
    IsLocalRing.residue T (π t) = IsLocalRing.ResidueField.map (algebraMap 𝒪 T) (θ t)
  /-- `T` is generated over `𝒪` by the Hecke operators. -/
  adjoin_range_π : Algebra.adjoin 𝒪 (Set.range π) = ⊤
  /-- Every `𝒪`-valued lift of `θ` factors through `T`. -/
  exists_point : ∀ χ : heckeAlgebra N 2 S →+* 𝒪,
    (∀ t : heckeAlgebra N 2 S, IsLocalRing.residue 𝒪 (χ t) = θ t) →
      ∃ ψ : T →ₐ[𝒪] 𝒪, ∀ t : heckeAlgebra N 2 S, ψ (π t) = χ t
  /-- The residue field of `T` is that of `𝒪`. -/
  residue_surjective : Function.Surjective (IsLocalRing.residue T ∘ algebraMap 𝒪 T)
  /-- The Galois representation. -/
  ρ : GaloisRepAdic.{u, u} T
  /-- Frobenius characteristic polynomials. -/
  charpoly_frob : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
        LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C (π (heckeAlgebra.T hℓ hℓN hℓS)) * X + C ((ℓ : T))
  /-- The residual representation is absolutely irreducible. -/
  residual_absIrr : ρ.residual.IsAbsolutelyIrreducible

variable {N : ℕ} [NeZero N] {S : Set ℕ} {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪]
  [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {θ : heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪} {T : Type u} [CommRing T]
  [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
  [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]

/-- If `S` contains every prime dividing `N`, then every local `𝒪`-algebra map `R → T` from
a local `𝒪`-algebra `R`, along which some representation over `R` base changes to a
representation equivalent to the Hecke representation, is surjective: the Frobenius traces
`T_ℓ` generate `T` and lie in the image. -/
theorem HeckeGaloisRepDatum.surjective_of_isEquiv_baseChangeAlong
    (H : HeckeGaloisRepDatum N S 𝒪 θ T) (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    {R : Type u} [CommRing R] [IsLocalRing R] [Algebra 𝒪 R] (ρR : GaloisRepAdic.{u, u} R)
    (φ : R →ₐ[𝒪] T) (hφ : IsLocalHom (φ : R →+* T))
    (he : (ρR.baseChangeAlong (φ : R →+* T) hφ).IsEquiv H.ρ) : Function.Surjective φ := by
  have hgen : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      H.π (heckeAlgebra.T hℓ hℓN hℓS) ∈ φ.range := by
    intro ℓ hℓ hℓN hℓS
    obtain ⟨A, hA, σ, hσ⟩ := ValuationSubring.exists_isFrobeniusAt_rat ℓ hℓ
    have h1 := H.charpoly_frob ℓ hℓ hℓN hℓS A hA σ hσ
    have h2 := GaloisRepAdic.charpoly_eq_of_isEquiv he σ
    have h3 := GaloisRepAdic.charpoly_baseChangeAlong (φ : R →+* T) hφ ρR σ
    have h4 := congrArg (fun p : T[X] => p.coeff 1) (h1.symm.trans (h2.symm.trans h3))
    simp only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X_one, coeff_C, coeff_map,
      mul_one, ite_eq_right (show (1 : ℕ) ≠ 2 by decide),
      ite_eq_right (show (1 : ℕ) ≠ 0 by decide),
      zero_sub, add_zero, RingHom.coe_coe] at h4
    exact ⟨-(LinearMap.charpoly (ρR.ρ σ)).coeff 1, by
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [map_neg, ← h4, neg_neg]⟩
  have hπ : ∀ t : heckeAlgebra N 2 S, H.π t ∈ φ.range := by
    rintro ⟨t, ht⟩
    induction ht using Algebra.adjoin_induction with
    | mem x hx =>
        rcases hx with ⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩
        · exact hgen ℓ hℓ hℓN hℓS
        · exact absurd (hS q hq hqN) hqS
    | algebraMap r =>
        have h : H.π ⟨algebraMap ℤ _ r, Subalgebra.algebraMap_mem _ r⟩ = (r : T) :=
          eq_intCast (H.π.comp (algebraMap ℤ (heckeAlgebra N 2 S))) r
        rw [h]
        exact intCast_mem φ.range r
    | add x y hx hy ihx ihy =>
        have h : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : heckeAlgebra N 2 S) =
            ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
        rw [h, H.π.map_add]
        exact add_mem ihx ihy
    | mul x y hx hy ihx ihy =>
        have h : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : heckeAlgebra N 2 S) =
            ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
        rw [h, H.π.map_mul]
        exact mul_mem ihx ihy
  have hle : Algebra.adjoin 𝒪 (Set.range H.π) ≤ φ.range :=
    Algebra.adjoin_le (by rintro _ ⟨t, rfl⟩; exact hπ t)
  rw [H.adjoin_range_π, top_le_iff] at hle
  exact (AlgHom.range_eq_top φ).mp hle

end CuspForm

namespace GaloisRep.DeformationRingData

/-- If the Hecke representation has type `𝒟` and its residual representation is equivalent to
the base change of `ρbar`, and `S` contains every prime dividing `N`, then there is a surjective
local `𝒪`-algebra map from the deformation ring to `T`, the one universality gives, along which
the universal deformation base changes to a representation equivalent to the Hecke
representation. -/
theorem exists_surjective_algHom_of_heckeGaloisRepDatum {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep.{u, u} (IsLocalRing.ResidueField 𝒪)}
    {𝒟 : ∀ ⦃A : Type u⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A],
      GaloisRepAdic.{u, u} A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟) {N : ℕ} [NeZero N] {S : Set ℕ}
    {θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪} {T : Type u} [CommRing T]
    [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (H : CuspForm.HeckeGaloisRepDatum N S 𝒪 θ T) (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (h𝒟 : 𝒟 H.ρ)
    (hres : H.ρ.residual.IsEquiv
      (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 T)))) :
    ∃ φ : D.R →ₐ[𝒪] T, Function.Surjective φ ∧ ∃ hφ : IsLocalHom (φ : D.R →+* T),
      (D.ρ.baseChangeAlong (φ : D.R →+* T) hφ).IsEquiv H.ρ := by
  obtain ⟨φ, ⟨hφ, he⟩, -⟩ := D.universal T H.residue_surjective H.ρ h𝒟 hres
  exact ⟨φ, H.surjective_of_isEquiv_baseChangeAlong hS D.ρ φ hφ he, hφ, he⟩

end GaloisRep.DeformationRingData

end
