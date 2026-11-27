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

/-- **Diophantine sets.** Let $\varphi : A \to R$ be a ring homomorphism of commutative rings and
let $k \in \mathbb{N}$. Polynomials with coefficients in $A$ are evaluated at points with
coordinates in $R$ by first mapping their coefficients into $R$ by $\varphi$. A subset
$S \subseteq R^k$ is Diophantine over $R$ with coefficients from $A$ through $\varphi$ when there
are $n \in \mathbb{N}$ and a finite set $P$ of polynomials with coefficients in $A$ in the
variables $x_1, \dots, x_k, y_1, \dots, y_n$ such that for every $x \in R^k$, $x \in S$ if and
only if there is $y \in R^n$ with $p(x, y) = 0$ for all $p \in P$. -/
def IsDiophantine (φ : A →+* R) {k : ℕ} (S : Set (Fin k → R)) : Prop :=
  ∃ (n : ℕ) (P : Finset (MvPolynomial (Fin k ⊕ Fin n) A)), ∀ x : Fin k → R,
    x ∈ S ↔ ∃ y : Fin n → R, ∀ p ∈ P, eval₂ φ (Sum.elim x y) p = 0

/-- **Diophantine subsets of a ring.** Let $\varphi : A \to R$ be a ring homomorphism of commutative
rings. A subset $S \subseteq R$ is Diophantine over $R$ with coefficients from $A$ through $\varphi$
when the set $\{(s) : s \in S\} \subseteq R^1$ of one-coordinate points with coordinate in $S$ is a
Diophantine subset of $R^1$ over $R$ with coefficients from $A$ through $\varphi$. -/
def IsDiophantineSet (φ : A →+* R) (S : Set R) : Prop :=
  IsDiophantine φ {x : Fin 1 → R | x 0 ∈ S}

theorem isDiophantineSet_iff (φ : A →+* R) (S : Set R) :
    IsDiophantineSet φ S ↔ IsDiophantine φ {x : Fin 1 → R | x 0 ∈ S} :=
  Iff.rfl

/-- **The whole space is Diophantine.** Let $\varphi : A \to R$ be a ring homomorphism of
commutative rings. For every $k \in \mathbb{N}$, the whole space $R^k$ is Diophantine over $R$ with
coefficients from $A$ through $\varphi$.

It is cut out by the empty set of polynomials, with no auxiliary variables. -/
theorem isDiophantine_univ (φ : A →+* R) (k : ℕ) :
    IsDiophantine φ (Set.univ : Set (Fin k → R)) :=
  ⟨0, ∅, fun x => by simp⟩

/-- **The empty set is Diophantine.** Let $\varphi : A \to R$ be a ring homomorphism of commutative
rings, with $R$ nontrivial. For every $k \in \mathbb{N}$, the empty subset of $R^k$ is Diophantine
over $R$ with coefficients from $A$ through $\varphi$.

It is cut out by the constant polynomial $1$. -/
theorem isDiophantine_empty [Nontrivial R] (φ : A →+* R) (k : ℕ) :
    IsDiophantine φ (∅ : Set (Fin k → R)) :=
  ⟨0, {1}, fun x => by simp⟩

end MetaMathlibExt
