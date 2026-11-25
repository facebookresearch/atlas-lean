/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Galois.GaloisRepAdic

@[expose] public section

universe u v

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

/-- Consumer with the original binders: the residual representation of an
adic representation, its determinant, trace, and unramifiedness predicate. -/
example {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (q : ℕ) :
    True := by
  let _ := ρ.residual
  let _ := ρ.det σ
  let _ := ρ.trace σ
  let _ : Prop := ρ.IsUnramifiedAt q
  trivial

/-- Higher-universe consumer. -/
example {A : Type (u + 1)} [CommRing A] [IsLocalRing A]
    (ρ : GaloisRepAdic A) (q : ℕ) : Prop :=
  ρ.IsUnramifiedAt q

/-- An adic representation over a field gives a residual representation,
and a residual representation lifts to an adic one over the same field. -/
example {k : Type} [Field k] (ρ : GaloisRepAdic k)
    (τ : ResidualGaloisRep k) : True := by
  let _ := ρ.toResidualGaloisRep
  let _ := GaloisRepAdic.ofResidualGaloisRep τ
  trivial

/-- Equivalences of adic representations are equivalences of the underlying
representations: they use the standard `refl`, `symm` and `trans`, and induce
equivalences of residual representations. -/
example {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) :
    True := by
  let e : GaloisRepAdic.Equiv ρ ρ := Representation.Equiv.refl ρ.ρ
  let _ : GaloisRepAdic.Equiv ρ ρ := e.symm.trans e
  let _ := e.residual
  let _ : GaloisRepAdic.IsEquiv ρ ρ := ⟨e⟩
  trivial

/-- Boundary: unramifiedness at `q` is a statement about inertia over `q`;
for a representation that is unramified at `q`, the predicate is exactly
the quantified triviality statement in its definition. -/
example {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (q : ℕ) :
    ρ.IsUnramifiedAt q ↔
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ = 1 :=
  Iff.rfl
