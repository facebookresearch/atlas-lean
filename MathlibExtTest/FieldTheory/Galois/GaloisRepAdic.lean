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

/-- Equivalences of adic representations are reflexive, and induce
equivalences of residual representations. -/
example {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) :
    True := by
  let e := GaloisRepAdic.Equiv.refl ρ
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
