/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_GaloisRep_LocalConditions.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers
of the Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a
proof-extraction framework; the statements are reused here with that
machinery removed and the names restated in Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import MathlibExt.FieldTheory.Galois.GaloisRepAdic
public import MathlibExt.RingTheory.Valuation.InertiaRootsOfUnity
public import MathlibExt.RingTheory.Valuation.LiesOverPrime

@[expose] public section

universe u v

namespace GaloisRepAdic

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The determinant is cyclotomic at `p`: `p` lies in the maximal
ideal, and the determinant of `σ` agrees with the cyclotomic exponent
`a` modulo `p ^ n` whenever `σ` acts on `p ^ n`-th roots of unity by
raising to the `a`-th power. -/
public def DetIsCyclotomic (ρ : GaloisRepAdic A) (p : ℕ) : Prop :=
  (p : A) ∈ IsLocalRing.maximalIdeal A ∧
    ∀ (n : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (a : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a) →
        LinearMap.det (ρ.ρ σ) - (a : A) ∈
          Ideal.span {((p ^ n : ℕ) : A)}

/-- The representation is ordinary at `p`: at every valuation
subring lying over `p` there is a Galois-stable line, spanned by a
basis vector, such that inertia acts trivially modulo that line. -/
public def IsOrdinaryAt (ρ : GaloisRepAdic A) (p : ℕ) : Prop :=
  ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
    ∃ L : Submodule A ρ.V,
      (∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L)

/-- The representation is unipotent on inertia at `q`: every
inertia element has characteristic polynomial `(X - 1) ^ 2`. -/
public def IsUnipotentOnInertiaAt (ρ : GaloisRepAdic A) (q : ℕ) :
    Prop :=
  ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
    ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      LinearMap.charpoly (ρ.ρ σ) = (Polynomial.X - 1) ^ 2

end GaloisRepAdic

namespace GaloisRep

/-- The ordinary local condition over `𝒪` at `p` with exceptional
set `S`: cyclotomic determinant, ordinary at `p`, and unramified at
every prime outside `S`. -/
public def ordinaryCondition (𝒪 : Type u) [CommRing 𝒪] (p : ℕ)
    (S : Finset ℕ) :
    ∀ ⦃A : Type v⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A],
      GaloisRepAdic A → Prop :=
  fun _A _ _ _ ρ => ρ.DetIsCyclotomic p ∧ ρ.IsOrdinaryAt p ∧
    ∀ q : ℕ, q.Prime → q ∉ S → ρ.IsUnramifiedAt q

/-- The ordinary condition unfolds to its three clauses. -/
theorem ordinaryCondition_def (𝒪 : Type u) [CommRing 𝒪] (p : ℕ)
    (S : Finset ℕ) {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra 𝒪 A] (ρ : GaloisRepAdic A) :
    ordinaryCondition 𝒪 p S ρ ↔
      ρ.DetIsCyclotomic p ∧ ρ.IsOrdinaryAt p ∧
        ∀ q : ℕ, q.Prime → q ∉ S → ρ.IsUnramifiedAt q :=
  Iff.rfl

/-- The minimal ordinary local condition: the ordinary condition,
together with unipotent inertia at every prime of `S` other
than `p`. -/
public def minimalOrdinaryCondition (𝒪 : Type u) [CommRing 𝒪]
    (p : ℕ) (S : Finset ℕ) :
    ∀ ⦃A : Type v⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A],
      GaloisRepAdic A → Prop :=
  fun _A _ _ _ ρ => ordinaryCondition 𝒪 p S ρ ∧
    ∀ q ∈ S, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q

/-- The minimal ordinary condition unfolds to its two clauses. -/
theorem minimalOrdinaryCondition_def (𝒪 : Type u) [CommRing 𝒪]
    (p : ℕ) (S : Finset ℕ) {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra 𝒪 A] (ρ : GaloisRepAdic A) :
    minimalOrdinaryCondition 𝒪 p S ρ ↔
      ordinaryCondition 𝒪 p S ρ ∧
        ∀ q ∈ S, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q :=
  Iff.rfl

end GaloisRep
