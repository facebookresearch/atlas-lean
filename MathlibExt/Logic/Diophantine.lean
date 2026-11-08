/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Diophantine sets over a commutative ring

A subset `S ⊆ Rᵏ` is Diophantine with coefficients from `A` (mapped into `R` by `φ : A →+* R`) when
it is the projection of the common zero set of finitely many polynomials over `A`. In a field this
is existential definability in the language of rings with constants for the image of `A` (negations
and disjunctions of equations are again positive-existential). Mathlib's `Dioph` covers the special
case of subsets of `ℕ^α` cut out by integer polynomials.
-/

@[expose] public section

namespace MetaMathlibExt

open MvPolynomial

variable {A R : Type*} [CommRing A] [CommRing R]

/-- `S ⊆ Rᵏ` is Diophantine over `R` with coefficients from `A` (through `φ : A →+* R`): for some
`n` and finitely many polynomials `P` over `A` in the variables `x₁, …, x_k, y₁, …, yₙ`,
`x ∈ S ↔ ∃ y, ∀ p ∈ P, p(x, y) = 0`. -/
def IsDiophantine (φ : A →+* R) {k : ℕ} (S : Set (Fin k → R)) : Prop :=
  ∃ (n : ℕ) (P : Finset (MvPolynomial (Fin k ⊕ Fin n) A)), ∀ x : Fin k → R,
    x ∈ S ↔ ∃ y : Fin n → R, ∀ p ∈ P, eval₂ φ (Sum.elim x y) p = 0

/-- A subset `S ⊆ R` is Diophantine with coefficients from `A`. -/
def IsDiophantineSet (φ : A →+* R) (S : Set R) : Prop :=
  IsDiophantine φ {x : Fin 1 → R | x 0 ∈ S}

theorem isDiophantineSet_iff (φ : A →+* R) (S : Set R) :
    IsDiophantineSet φ S ↔ IsDiophantine φ {x : Fin 1 → R | x 0 ∈ S} :=
  Iff.rfl

/-- The whole space is Diophantine (no polynomials, no auxiliary variables). -/
theorem isDiophantine_univ (φ : A →+* R) (k : ℕ) :
    IsDiophantine φ (Set.univ : Set (Fin k → R)) :=
  ⟨0, ∅, fun x => by simp⟩

/-- The empty set is Diophantine (cut out by the constant polynomial `1`). -/
theorem isDiophantine_empty [Nontrivial R] (φ : A →+* R) (k : ℕ) :
    IsDiophantine φ (∅ : Set (Fin k → R)) :=
  ⟨0, {1}, fun x => by simp⟩

end MetaMathlibExt
