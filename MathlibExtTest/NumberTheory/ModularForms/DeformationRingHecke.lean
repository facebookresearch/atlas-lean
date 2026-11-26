/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.DeformationRingHecke

@[expose] public section

open Polynomial

/-- exactSource consumer: the original binders apply verbatim. -/
example {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟) {N : ℕ} [NeZero N] {S : Set ℕ}
    {θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪} {T : Type} [CommRing T]
    [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (H : CuspForm.HeckeGaloisRepDatum N S 𝒪 θ T) (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (h𝒟 : 𝒟 H.ρ)
    (hres : H.ρ.residual.IsEquiv
      (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 T)))) :
    ∃ φ : D.R →ₐ[𝒪] T, Function.Surjective φ ∧ ∃ hφ : IsLocalHom (φ : D.R →+* T),
      (D.ρ.baseChangeAlong (φ : D.R →+* T) hφ).IsEquiv H.ρ :=
  D.exists_surjective_algHom_of_heckeGaloisRepDatum H hS h𝒟 hres

/-- Higher-universe consumer: the coefficient rings may live in any universe. -/
example {𝒪 : Type 1} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep.{1, 1} (IsLocalRing.ResidueField 𝒪)}
    {𝒟 : ∀ ⦃A : Type 1⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A],
      GaloisRepAdic.{1, 1} A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟) {N : ℕ} [NeZero N] {S : Set ℕ}
    {θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪} {T : Type 1} [CommRing T]
    [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (H : CuspForm.HeckeGaloisRepDatum N S 𝒪 θ T) (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (h𝒟 : 𝒟 H.ρ)
    (hres : H.ρ.residual.IsEquiv
      (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 T)))) :
    ∃ φ : D.R →ₐ[𝒪] T, Function.Surjective φ ∧ ∃ hφ : IsLocalHom (φ : D.R →+* T),
      (D.ρ.baseChangeAlong (φ : D.R →+* T) hφ).IsEquiv H.ρ :=
  D.exists_surjective_algHom_of_heckeGaloisRepDatum H hS h𝒟 hres

/-- exactSource consumer: the original binders apply verbatim (with the representation
space in `Type`, as in the source). -/
example {A : Type} [CommRing A] [IsLocalRing A] {B : Type} [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic.{0, 0} A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.charpoly ((ρ.baseChangeAlong φ hφ).ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).map φ :=
  GaloisRepAdic.charpoly_baseChangeAlong φ hφ ρ σ

/-- exactSource consumer: the original binders apply verbatim (with the representation
space in `Type`, as in the source). -/
example {A : Type} [CommRing A] [IsLocalRing A] {ρ₁ ρ₂ : GaloisRepAdic.{0, 0} A}
    (h : ρ₁.IsEquiv ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.charpoly (ρ₁.ρ σ) = LinearMap.charpoly (ρ₂.ρ σ) :=
  GaloisRepAdic.charpoly_eq_of_isEquiv h σ

/-- Boundary: with no `U_q` excluded, the hypothesis on `S` is what rules out the operators
`U_q` for `q ∣ N`; at level one it holds vacuously. -/
private theorem prime_dvd_one_mem (S : Set ℕ) : ∀ q : ℕ, q.Prime → q ∣ 1 → q ∈ S :=
  fun _ hq h1 => absurd (Nat.dvd_one.mp h1) hq.ne_one

/-- Level one: the surjectivity theorem applies for every `S`, the hypothesis on `S` being
discharged by `prime_dvd_one_mem`. -/
example {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] {S : Set ℕ}
    {θ : CuspForm.heckeAlgebra 1 2 S →+* IsLocalRing.ResidueField 𝒪} {T : Type} [CommRing T]
    [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (H : CuspForm.HeckeGaloisRepDatum 1 S 𝒪 θ T) {R : Type} [CommRing R] [IsLocalRing R]
    [Algebra 𝒪 R] (ρR : GaloisRepAdic.{0, 0} R) (φ : R →ₐ[𝒪] T) (hφ : IsLocalHom (φ : R →+* T))
    (he : (ρR.baseChangeAlong (φ : R →+* T) hφ).IsEquiv H.ρ) : Function.Surjective φ :=
  H.surjective_of_isEquiv_baseChangeAlong (prime_dvd_one_mem S) ρR φ hφ he

/-- Level one: the universal map from the deformation ring is surjective for every `S`. -/
example {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟) {S : Set ℕ}
    {θ : CuspForm.heckeAlgebra 1 2 S →+* IsLocalRing.ResidueField 𝒪} {T : Type} [CommRing T]
    [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (H : CuspForm.HeckeGaloisRepDatum 1 S 𝒪 θ T) (h𝒟 : 𝒟 H.ρ)
    (hres : H.ρ.residual.IsEquiv
      (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 T)))) :
    ∃ φ : D.R →ₐ[𝒪] T, Function.Surjective φ ∧ ∃ hφ : IsLocalHom (φ : D.R →+* T),
      (D.ρ.baseChangeAlong (φ : D.R →+* T) hφ).IsEquiv H.ρ :=
  D.exists_surjective_algHom_of_heckeGaloisRepDatum H (prime_dvd_one_mem S) h𝒟 hres
