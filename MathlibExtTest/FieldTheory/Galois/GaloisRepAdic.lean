/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Galois.GaloisRepAdic

@[expose] public section

universe u

/-- Consumer with the original binders. -/
example {A : Type} [CommRing A] [IsLocalRing A] [Finite A] (p : ℕ) [Fact p.Prime]
    (ρ : GaloisRepAdic A) (hρ : ρ.IsFlatAt p) :
    ∃ (H : Type) (cH : CommRing H) (hH : HopfAlgebra ℤ_[p] H),
      letI : CommRing H := cH
      letI : HopfAlgebra ℤ_[p] H := hH
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρ.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
          (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = σ (f h)) → e g = ρ.ρ (localGaloisToGlobal p σ) (e f) :=
  GaloisRepAdic.exists_finiteFlat_padicInt_model_of_isFlatAt p ρ hρ

/-- Higher-universe consumer. -/
example {A : Type (u + 1)} [CommRing A] [IsLocalRing A] [Finite A] (p : ℕ)
    [Fact p.Prime] (ρ : GaloisRepAdic A) (hρ : ρ.IsFlatAt p) :
    ∃ (H : Type (u + 1)) (cH : CommRing H) (hH : HopfAlgebra ℤ_[p] H),
      letI : CommRing H := cH
      letI : HopfAlgebra ℤ_[p] H := hH
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρ.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
          (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = σ (f h)) → e g = ρ.ρ (localGaloisToGlobal p σ) (e f) :=
  GaloisRepAdic.exists_finiteFlat_padicInt_model_of_isFlatAt p ρ hρ

/-- Boundary: the primality hypothesis excludes `p = 1`, for which the
localization and the `p`-adic integers used in the statement degenerate. -/
example : ¬ Nat.Prime 1 := by decide
