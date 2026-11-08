/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.Ideal.Span

/-!
# Locally integer polynomial functions

Statements from Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41 (arXiv `2401.17955`, TeX source read).

For `U ⊆ ℤ`, a function `f : U → ℤ` is *locally integer polynomial* (LIP) when its restriction
to every finite subset of `U` is given by a polynomial with integer coefficients. These functions
form the ring `LIP(U)`, here `lipSubring U`; `LIP(ℤ) = Lℤ[x]` is `lipSubring Set.univ`. A function
`g : ℤ → ℤ` is LIP on `U` when `U.domRestrict g ∈ lipSubring U`. The paper's interpolation polynomial
`f_X ∈ ℚ[x]` (the unique polynomial of degree `< |X|` agreeing with `f` on the finite set `X`) is
`interpolationPoly X f`, built from Mathlib's `Lagrange.interpolate`; "`f_X ∈ ℤ[x]`" is
`interpolationPoly X f ∈ Polynomial.lifts (Int.castRingHom ℚ)`. The paper's `ℕ` is the positive
integers.
-/

open Polynomial Filter Topology

namespace MetaMathlibExt

@[expose] public section

/-- The ring `LIP(U)` of locally integer polynomial functions on `U ⊆ ℤ`: the functions
`f : U → ℤ` whose restriction to every finite subset of `U` is given by a polynomial with
integer coefficients.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Definitions 1 and 2. -/
public def lipSubring (U : Set ℤ) : Subring (U → ℤ) where
  carrier := {f | ∀ X : Finset U, ∃ p : ℤ[X], ∀ x ∈ X, p.eval (x : ℤ) = f x}
  mul_mem' := by
    intro f g hf hg X
    obtain ⟨p, hp⟩ := hf X
    obtain ⟨q, hq⟩ := hg X
    exact ⟨p * q, fun x hx => by simp [hp x hx, hq x hx]⟩
  one_mem' := fun _ => ⟨1, by simp⟩
  add_mem' := by
    intro f g hf hg X
    obtain ⟨p, hp⟩ := hf X
    obtain ⟨q, hq⟩ := hg X
    exact ⟨p + q, fun x hx => by simp [hp x hx, hq x hx]⟩
  zero_mem' := fun _ => ⟨0, by simp⟩
  neg_mem' := by
    intro f hf X
    obtain ⟨p, hp⟩ := hf X
    exact ⟨-p, fun x hx => by simp [hp x hx]⟩

/-- Membership in `LIP(U)` unfolds to the defining condition on finite subsets.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Definition 1. -/
public theorem mem_lipSubring_iff {U : Set ℤ} {f : U → ℤ} :
    f ∈ lipSubring U ↔ ∀ X : Finset U, ∃ p : ℤ[X], ∀ x ∈ X, p.eval (x : ℤ) = f x :=
  Iff.rfl

/-- The function `x ↦ x(x+1)/2` is not LIP on `ℤ`: no integer polynomial takes the values
`0, 0, 1` at `-1, 0, 1`, since `1 - (-1)` must divide `p(1) - p(-1)`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Section 1 and Example 2. -/
public theorem triangular_not_mem_lipSubring_univ :
    (fun x : (Set.univ : Set ℤ) => (x : ℤ) * ((x : ℤ) + 1) / 2) ∉ lipSubring Set.univ := by
  intro h
  obtain ⟨p, hp⟩ := h {⟨-1, trivial⟩, ⟨1, trivial⟩}
  have h1 := hp ⟨1, trivial⟩ (by simp)
  have h2 := hp ⟨-1, trivial⟩ (by simp)
  have hd := Polynomial.sub_dvd_eval_sub (1 : ℤ) (-1) p
  simp only at h1 h2
  rw [h1, h2] at hd
  norm_num at hd

/-- Evaluation of integer polynomials, as a ring homomorphism `ℤ[x] → LIP(U)`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 1. -/
public noncomputable def polynomialToLIP (U : Set ℤ) : ℤ[X] →+* lipSubring U :=
  (RingHom.pi fun u : U => Polynomial.evalRingHom (u : ℤ)).codRestrict (lipSubring U)
    fun p _ => ⟨p, fun _ _ => rfl⟩

/-- `polynomialToLIP U p` is the function `u ↦ p(u)`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 1. -/
@[simp] public theorem polynomialToLIP_apply (U : Set ℤ) (p : ℤ[X]) (u : U) :
    (polynomialToLIP U p : U → ℤ) u = p.eval (u : ℤ) :=
  rfl

/-- The interpolation polynomial `f_X ∈ ℚ[x]` of `f : ℤ → ℤ` on a finite set `X ⊆ ℤ`: the
unique rational polynomial of degree `< |X|` agreeing with `f` on `X`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Section 1 and Definition 3. -/
public noncomputable def interpolationPoly (X : Finset ℤ) (f : ℤ → ℤ) : ℚ[X] :=
  Lagrange.interpolate X (fun z : ℤ => (z : ℚ)) fun z => (f z : ℚ)

/-- `f_X` agrees with `f` on `X`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Section 1. -/
public theorem eval_interpolationPoly {X : Finset ℤ} (f : ℤ → ℤ) {x : ℤ} (hx : x ∈ X) :
    (interpolationPoly X f).eval (x : ℚ) = f x :=
  Lagrange.eval_interpolate_at_node _ (fun _ _ _ _ h => Int.cast_injective h) hx

/-- `f_X` has degree `< |X|`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Section 1. -/
public theorem degree_interpolationPoly_lt (X : Finset ℤ) (f : ℤ → ℤ) :
    (interpolationPoly X f).degree < X.card :=
  Lagrange.degree_interpolate_lt _ fun _ _ _ _ h => Int.cast_injective h

/-- **Lemma 1** (polynomial part). For infinite `U ⊆ ℤ`, `LIP(U)` contains `ℤ[x]`: evaluation
`ℤ[x] → LIP(U)` is injective. The subring part of Lemma 1 is the construction of `lipSubring`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 1 (`integers-2025-A41-lem-1`). -/
public theorem_wanted polynomialToLIP_injective {U : Set ℤ} (hU : U.Infinite) :
    Function.Injective (polynomialToLIP U)

/-- **Lemma 2.** If `q ∈ ℚ[x]` has degree `< |X|` and agrees on the finite set `X ⊆ ℤ` with
some integer polynomial `p`, then `q ∈ ℤ[x]`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 2 (`integers-2025-A41-lem-2`). -/
public theorem_wanted mem_lifts_of_degree_lt_of_eval_eq (X : Finset ℤ) (q : ℚ[X])
    (hq : q.degree < X.card) (p : ℤ[X]) (h : ∀ x ∈ X, q.eval (x : ℚ) = ((p.eval x : ℤ) : ℚ)) :
    q ∈ Polynomial.lifts (Int.castRingHom ℚ)

/-- **Lemma 3.** A LIP function vanishing at infinitely many points of `U` is zero.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 3 (`integers-2025-A41-lem-3`). -/
public theorem_wanted lip_eq_zero_of_infinite_zeros {U : Set ℤ} {f : U → ℤ}
    (hf : f ∈ lipSubring U) (h : {x : U | f x = 0}.Infinite) : f = 0

/-- **Corollary 1.** For infinite `U ⊆ V ⊆ ℤ`, restriction `LIP(V) → LIP(U)` is injective
(with `V = ℤ`: `LIP(ℤ)` embeds in every `LIP(U)`).

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Corollary 1 (`integers-2025-A41-cor-1`). -/
public theorem_wanted lip_restrict_injective {U V : Set ℤ} (hU : U.Infinite) (hUV : U ⊆ V)
    {f g : V → ℤ} (hf : f ∈ lipSubring V) (hg : g ∈ lipSubring V)
    (h : f ∘ Set.inclusion hUV = g ∘ Set.inclusion hUV) : f = g

/-- **Lemma 4** (domain). For infinite `U ⊆ ℤ`, `LIP(U)` is a domain.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 4 (`integers-2025-A41-lem-4`). -/
public theorem_wanted lipSubring_isDomain {U : Set ℤ} (hU : U.Infinite) :
    IsDomain (lipSubring U)

/-- **Lemma 4** (units). For infinite `U ⊆ ℤ`, the only units of `LIP(U)` are `1` and `-1`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 4 (`integers-2025-A41-lem-4`). -/
public theorem_wanted lipSubring_units_eq {U : Set ℤ} (hU : U.Infinite)
    (u : (lipSubring U)ˣ) : u = 1 ∨ u = -1

/-- **Lemma 5.** An integer polynomial of degree `d` satisfies `|f(x)| ≥ d!/2^d` for some
`x ∈ {0, 1, …, d}`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 5 (`integers-2025-A41-lem-5`). -/
public theorem_wanted exists_factorial_div_two_pow_le_abs_eval (f : ℤ[X]) (d : ℕ)
    (hf : f.degree = d) :
    ∃ x ∈ Finset.range (d + 1), (d.factorial : ℚ) / 2 ^ d ≤ |((f.eval (x : ℤ) : ℤ) : ℚ)|

/-- **Lemma 6** (Exchange Formula). For a finite `X ⊆ ℤ` and `a, b ∉ X`,
`f_{X ⊔ {a}} = f_{X ⊔ {b}} + c (a - b) ∏_{z ∈ X} (x - z)`, where `c` is the coefficient of
`x^{|X|+1}` in `f_{X ⊔ {a,b}}`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 6 (`integers-2025-A41-lem-6`). -/
public theorem_wanted interpolationPoly_exchange (X : Finset ℤ) {a b : ℤ} (ha : a ∉ X)
    (hb : b ∉ X) (f : ℤ → ℤ) :
    interpolationPoly (insert a X) f = interpolationPoly (insert b X) f +
      C ((interpolationPoly (insert a (insert b X)) f).coeff (X.card + 1) * ((a : ℚ) - b)) *
        ∏ z ∈ X, (Polynomial.X - C (z : ℚ))

/-- **Lemma 7.** Let `X` be a circuit for `f`: `f_X ∉ ℤ[x]` but `f_{X \ {a}} ∈ ℤ[x]` for every
`a ∈ X`. Then the coefficient `c` of `x^{|X|-1}` in `f_X` is not an integer, and all elements
of `X` are congruent modulo the reduced denominator of `c`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 7 (`integers-2025-A41-lem-7`), with the circuit definition preceding it. -/
public theorem_wanted circuit_coeff_den (f : ℤ → ℤ) (X : Finset ℤ)
    (hX : interpolationPoly X f ∉ Polynomial.lifts (Int.castRingHom ℚ))
    (hmin : ∀ a ∈ X, interpolationPoly (X.erase a) f ∈ Polynomial.lifts (Int.castRingHom ℚ)) :
    ((interpolationPoly X f).coeff (X.card - 1)).den ≠ 1 ∧
      ∀ a ∈ X, ∀ b ∈ X, (((interpolationPoly X f).coeff (X.card - 1)).den : ℤ) ∣ a - b

/-- **Lemma 8.** For `d₁, d₂ > 0`, the progressions `a₁ + d₁ℤ_{≥0}` and `a₂ + d₂ℤ_{≥0}` in `ℕ`
intersect iff `gcd(d₁, d₂) ∣ a₁ - a₂`, and a nonempty intersection is `a₃ + lcm(d₁, d₂)ℤ_{≥0}`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 8 (`integers-2025-A41-lem-8`). -/
public theorem_wanted natProgression_inter (a₁ a₂ d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    (({x | ∃ n : ℕ, x = a₁ + d₁ * n} ∩ {x | ∃ n : ℕ, x = a₂ + d₂ * n} : Set ℕ).Nonempty ↔
      ((Nat.gcd d₁ d₂ : ℕ) : ℤ) ∣ (a₁ : ℤ) - a₂) ∧
    (({x | ∃ n : ℕ, x = a₁ + d₁ * n} ∩ {x | ∃ n : ℕ, x = a₂ + d₂ * n} : Set ℕ).Nonempty →
      ∃ a₃ : ℕ, ({x | ∃ n : ℕ, x = a₁ + d₁ * n} ∩ {x | ∃ n : ℕ, x = a₂ + d₂ * n} : Set ℕ) =
        {x | ∃ n : ℕ, x = a₃ + Nat.lcm d₁ d₂ * n})

/-- **Lemma 9.** If `a ∈ a₁ + d₁ℤ_{≥0}` and `b ∈ a₂ + d₂ℤ_{≥0}` (`d₁, d₂ > 0`), the two
progressions intersect, and `a ≠ b`, then their intersection meets the progression
`min(a,b) + |b - a| ℤ_{≥0}` generated by `a` and `b` in infinitely many points.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 9 (`integers-2025-A41-lem-9`). -/
public theorem_wanted natProgression_inter_infinite (a₁ a₂ d₁ d₂ a b : ℕ) (hd₁ : 0 < d₁)
    (hd₂ : 0 < d₂) (ha : ∃ n : ℕ, a = a₁ + d₁ * n) (hb : ∃ n : ℕ, b = a₂ + d₂ * n)
    (hne : ({x | ∃ n : ℕ, x = a₁ + d₁ * n} ∩ {x | ∃ n : ℕ, x = a₂ + d₂ * n} : Set ℕ).Nonempty)
    (hab : a ≠ b) :
    ({x | ∃ n : ℕ, x = a₁ + d₁ * n} ∩ {x | ∃ n : ℕ, x = a₂ + d₂ * n} ∩
      {x | ∃ n : ℕ, x = min a b + (max a b - min a b) * n} : Set ℕ).Infinite

/-- **Theorem 1.** For a bijection `σ : ℕ ≃ U`, every integer sequence `a` gives the LIP
function `f(x) = ∑_k a_k ∏_{i<k} (x - σ(i))` (for `x = σ(m)` only the terms `k ≤ m` are
nonzero, so the formal series is the displayed finite sum), and every `f ∈ LIP(U)` arises from
a unique `a`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Theorem 1 (`integers-2025-A41-thm-1`), reindexed from `σ(1), σ(2), …`. -/
public theorem_wanted lipSubring_newton_series {U : Set ℤ} (σ : ℕ ≃ U) :
    (∀ a : ℕ → ℤ, (fun u : U => ∑ k ∈ Finset.range (σ.symm u + 1),
        a k * ∏ i ∈ Finset.range k, ((u : ℤ) - σ i)) ∈ lipSubring U) ∧
    ∀ f ∈ lipSubring U, ∃! a : ℕ → ℤ, (fun u : U => ∑ k ∈ Finset.range (σ.symm u + 1),
        a k * ∏ i ∈ Finset.range k, ((u : ℤ) - σ i)) = f

/-- **Theorem 2.** If `f ∈ LIP(U)` and `|f(x)|` is prime for infinitely many `x ∈ U`, then `f`
is irreducible in `LIP(U)`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Theorem 2 (`integers-2025-A41-thm-2`). -/
public theorem_wanted irreducible_of_infinite_prime_values {U : Set ℤ} (f : lipSubring U)
    (h : {x : U | ((f : U → ℤ) x).natAbs.Prime}.Infinite) : Irreducible f

/-- **Theorem 3.** If `f ∈ LIP(U)` and `|f(x)| ≤ C|x|^d` for infinitely many `x ∈ U`, then `f`
is an integer polynomial.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Theorem 3 (`integers-2025-A41-thm-3`). -/
public theorem_wanted mem_range_polynomialToLIP_of_bound {U : Set ℤ} (C : ℝ) (d : ℕ)
    (f : lipSubring U)
    (h : {x : U | |(((f : U → ℤ) x : ℤ) : ℝ)| ≤ C * |((x : ℤ) : ℝ)| ^ d}.Infinite) :
    f ∈ (polynomialToLIP U).range

/-- **Corollary 2.** For infinite `U`, a prime element of `ℤ[x]` (a prime of `ℤ`, or an
irreducible integer polynomial of content `1`) stays prime in `LIP(U)`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Corollary 2 (`integers-2025-A41-cor-2`). -/
public theorem_wanted prime_polynomialToLIP {U : Set ℤ} (hU : U.Infinite) {p : ℤ[X]}
    (hp : Prime p) : Prime (polynomialToLIP U p)

/-- **Corollary 3.** For infinite `U`, `ℤ[x]` is algebraically closed in `LIP(U)`: a LIP
function that is a root of a nonzero polynomial over `ℤ[x]` lies in `ℤ[x]`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Corollary 3 (`integers-2025-A41-cor-3`). -/
public theorem_wanted mem_range_polynomialToLIP_of_isAlgebraic {U : Set ℤ} (hU : U.Infinite)
    (f : lipSubring U) (q : Polynomial ℤ[X]) (hq : q ≠ 0)
    (hf : q.eval₂ (polynomialToLIP U) f = 0) : f ∈ (polynomialToLIP U).range

/-- **Theorem 4.** For infinite `U`, `LIP(U)` has an infinite strictly increasing chain of
principal ideals (so it is not Noetherian).

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Theorem 4 (`integers-2025-A41-thm-4`). -/
public theorem_wanted exists_strictMono_principal_ideals {U : Set ℤ} (hU : U.Infinite) :
    ∃ g : ℕ → lipSubring U, StrictMono fun n => Ideal.span ({g n} : Set (lipSubring U))

/-- **Theorem 5 (1).** `Lℤ[x]` is closed under composition.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Theorem 5 (`integers-2025-A41-thm-5`). -/
public theorem_wanted lip_univ_comp {f g : ↥(Set.univ : Set ℤ) → ℤ}
    (hf : f ∈ lipSubring Set.univ) (hg : g ∈ lipSubring Set.univ) :
    (fun x => f ⟨g x, Set.mem_univ _⟩) ∈ lipSubring Set.univ

/-- **Theorem 5 (2).** `Lℤ[x]` is closed under the left discrete derivative
`f(x) ↦ f(x) - f(x - 1)`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Theorem 5 (`integers-2025-A41-thm-5`). -/
public theorem_wanted lip_univ_sub_shift {f : ↥(Set.univ : Set ℤ) → ℤ}
    (hf : f ∈ lipSubring Set.univ) :
    (fun x => f x - f ⟨(x : ℤ) - 1, Set.mem_univ _⟩) ∈ lipSubring Set.univ

/-- **Theorem 6.** For every `τ : ℕ → ℝ` with `τ(n) → +∞` there is a non-polynomial
`f ∈ Lℤ[x]` with `|f(x)| < |x|^{τ(|x|)}` on some infinite `X ⊆ ℤ`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Theorem 6 (`integers-2025-A41-thm-6`). -/
public theorem_wanted exists_lip_univ_not_polynomial_lt_rpow (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop atTop) :
    ∃ f : lipSubring (Set.univ : Set ℤ), f ∉ (polynomialToLIP Set.univ).range ∧
      ∃ X : Set ℤ, X.Infinite ∧ ∀ x ∈ X,
        |(((f : ↥(Set.univ : Set ℤ) → ℤ) ⟨x, Set.mem_univ x⟩ : ℤ) : ℝ)| <
          |(x : ℝ)| ^ τ x.natAbs

/-- **Theorem 7.** If `f ∈ Lℤ[x]` and `|f(x)| < (2|x| - 1)!/2^{2|x|-1}` for all but finitely
many `x ∈ ℤ`, then `f` is an integer polynomial.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Theorem 7 (`integers-2025-A41-thm-7`). -/
public theorem_wanted mem_range_polynomialToLIP_of_factorial_bound
    (f : lipSubring (Set.univ : Set ℤ))
    (h : ∀ᶠ x : ℤ in cofinite,
      |((((f : ↥(Set.univ : Set ℤ) → ℤ) ⟨x, Set.mem_univ x⟩ : ℤ)) : ℚ)| <
        ((2 * x.natAbs - 1).factorial : ℚ) / 2 ^ (2 * x.natAbs - 1)) :
    f ∈ (polynomialToLIP Set.univ).range

/-- **Theorem 8** (in the reading of its proof). Let `X ⊆ ℤ` be finite and `f : ℤ → ℤ` with
`f_{X ⊔ {a,b}} ∉ ℤ[x]` but `f_{X ⊔ {a}}, f_{X ⊔ {b}} ∈ ℤ[x]` (this forces `a ≠ b` and
`a, b ∉ X`). Then `|a - b| ≥ 2`, and with `V = {x : gcd(x - a, a - b) = 1}` and `U = X ∪ V`
there is `g` agreeing with `f` on `X ∪ {a, b}` that is LIP on `U ∪ {a}` and on `U ∪ {b}`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Theorem 8 (`integers-2025-A41-thm-8`). -/
public theorem_wanted lip_continuation_two_points (X : Finset ℤ) (a b : ℤ) (f : ℤ → ℤ)
    (hab : interpolationPoly (insert a (insert b X)) f ∉ Polynomial.lifts (Int.castRingHom ℚ))
    (ha : interpolationPoly (insert a X) f ∈ Polynomial.lifts (Int.castRingHom ℚ))
    (hb : interpolationPoly (insert b X) f ∈ Polynomial.lifts (Int.castRingHom ℚ)) :
    2 ≤ |a - b| ∧ ∃ g : ℤ → ℤ, (∀ x ∈ insert a (insert b X), g x = f x) ∧
      (insert a ((X : Set ℤ) ∪ {x | Int.gcd (x - a) (a - b) = 1})).domRestrict g ∈
        lipSubring (insert a ((X : Set ℤ) ∪ {x | Int.gcd (x - a) (a - b) = 1})) ∧
      (insert b ((X : Set ℤ) ∪ {x | Int.gcd (x - a) (a - b) = 1})).domRestrict g ∈
        lipSubring (insert b ((X : Set ℤ) ∪ {x | Int.gcd (x - a) (a - b) = 1}))

/-- **Theorem 9.** Let `U = ⋃_α U_α ⊆ ℤ` be such that for all `α₁, α₂` and distinct
`a₁ ∈ U_{α₁}`, `a₂ ∈ U_{α₂}`, the set `U_{α₁} ∩ U_{α₂}` contains infinitely many terms of
`a₁ + (a₂ - a₁)ℤ`. Then `f` is LIP on `U` iff it is LIP on every `U_α`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Theorem 9 (`integers-2025-A41-thm-9`). -/
public theorem_wanted lip_iUnion_iff {ι : Type*} (V : ι → Set ℤ) (f : ℤ → ℤ)
    (hV : ∀ i j, ∀ a₁ ∈ V i, ∀ a₂ ∈ V j, a₁ ≠ a₂ →
      (V i ∩ V j ∩ {x | ∃ n : ℤ, x = a₁ + (a₂ - a₁) * n}).Infinite) :
    (⋃ i, V i).domRestrict f ∈ lipSubring (⋃ i, V i) ↔
      ∀ i, (V i).domRestrict f ∈ lipSubring (V i)

/-- **Corollary 4** (cofinite topology on `ℕ`). On the positive integers with the cofinite
topology, every locally LIP function on a nonempty open `U` is LIP on `U`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Corollary 4 (`integers-2025-A41-cor-4`). -/
public theorem_wanted lip_sheaf_cofinite_nat (U : Set ℤ) (hUS : U ⊆ {n | 0 < n})
    (hU : ({n : ℤ | 0 < n} \ U).Finite) (f : ℤ → ℤ) :
    (∀ a ∈ U, ∃ W ⊆ U, a ∈ W ∧ ({n : ℤ | 0 < n} \ W).Finite ∧
      W.domRestrict f ∈ lipSubring W) ↔ U.domRestrict f ∈ lipSubring U

/-- **Corollary 4** (cofinite topology on `ℤ`). On `ℤ` with the cofinite topology, every
locally LIP function on a nonempty open `U` is LIP on `U`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Corollary 4 (`integers-2025-A41-cor-4`). -/
public theorem_wanted lip_sheaf_cofinite_int (U : Set ℤ) (hU : Uᶜ.Finite) (f : ℤ → ℤ) :
    (∀ a ∈ U, ∃ W ⊆ U, a ∈ W ∧ Wᶜ.Finite ∧ W.domRestrict f ∈ lipSubring W) ↔
      U.domRestrict f ∈ lipSubring U

/-- **Corollary 4** (density one topology on `ℕ`). On the positive integers, whose nonempty open
sets are the sets of natural density one, every locally LIP function on a nonempty open `U` is
LIP on `U`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Corollary 4 (`integers-2025-A41-cor-4`). -/
public theorem_wanted lip_sheaf_densityOne_nat (U : Set ℤ) (hUS : U ⊆ {n | 0 < n})
    (hU : Tendsto (fun x : ℕ => ((U ∩ Set.Icc 1 (x : ℤ)).ncard : ℝ) / x) atTop (𝓝 1))
    (f : ℤ → ℤ) :
    (∀ a ∈ U, ∃ W ⊆ U, a ∈ W ∧
      Tendsto (fun x : ℕ => ((W ∩ Set.Icc 1 (x : ℤ)).ncard : ℝ) / x) atTop (𝓝 1) ∧
      W.domRestrict f ∈ lipSubring W) ↔ U.domRestrict f ∈ lipSubring U

/-- **Corollary 4** (density one topology on `ℤ`). On `ℤ`, whose nonempty open sets are the sets
`U` with `|{n ∈ U : |n| ≤ x}| / (2x + 1) → 1`, every locally LIP function on a nonempty open
`U` is LIP on `U`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Corollary 4 (`integers-2025-A41-cor-4`). -/
public theorem_wanted lip_sheaf_densityOne_int (U : Set ℤ)
    (hU : Tendsto (fun x : ℕ => ((U ∩ Set.Icc (-(x : ℤ)) x).ncard : ℝ) / (2 * x + 1)) atTop
      (𝓝 1))
    (f : ℤ → ℤ) :
    (∀ a ∈ U, ∃ W ⊆ U, a ∈ W ∧
      Tendsto (fun x : ℕ => ((W ∩ Set.Icc (-(x : ℤ)) x).ncard : ℝ) / (2 * x + 1)) atTop
        (𝓝 1) ∧
      W.domRestrict f ∈ lipSubring W) ↔ U.domRestrict f ∈ lipSubring U

/-- **Corollary 5.** On the set of primes with the cofinite topology, every locally LIP function
on a nonempty open `U` is LIP on `U`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Corollary 5 (`integers-2025-A41-cor-5`). -/
public theorem_wanted lip_sheaf_cofinite_primes (U : Set ℤ) (hUS : U ⊆ {p | Prime p ∧ 0 < p})
    (hU : ({p : ℤ | Prime p ∧ 0 < p} \ U).Finite) (f : ℤ → ℤ) :
    (∀ a ∈ U, ∃ W ⊆ U, a ∈ W ∧ ({p : ℤ | Prime p ∧ 0 < p} \ W).Finite ∧
      W.domRestrict f ∈ lipSubring W) ↔ U.domRestrict f ∈ lipSubring U

/-- **Corollary 6.** Let `U₁ = a₁ + d₁ℤ_{≥0}` and `U₂ = a₂ + d₂ℤ_{≥0}` (`d₁, d₂ > 0`) be
intersecting progressions in `ℕ`. If `f` is LIP on `U₁` and on `U₂`, it is LIP on `U₁ ∪ U₂`.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Corollary 6 (`integers-2025-A41-cor-6`). -/
public theorem_wanted lip_union_natProgression (a₁ a₂ d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (f : ℤ → ℤ)
    (hne : ({x | ∃ n : ℕ, x = a₁ + d₁ * n} ∩ {x | ∃ n : ℕ, x = a₂ + d₂ * n} : Set ℤ).Nonempty)
    (h₁ : ({x | ∃ n : ℕ, x = a₁ + d₁ * n} : Set ℤ).domRestrict f ∈
      lipSubring {x | ∃ n : ℕ, x = a₁ + d₁ * n})
    (h₂ : ({x | ∃ n : ℕ, x = a₂ + d₂ * n} : Set ℤ).domRestrict f ∈
      lipSubring {x | ∃ n : ℕ, x = a₂ + d₂ * n}) :
    ({x | ∃ n : ℕ, x = a₁ + d₁ * n} ∪ {x | ∃ n : ℕ, x = a₂ + d₂ * n} : Set ℤ).domRestrict f ∈
      lipSubring ({x | ∃ n : ℕ, x = a₁ + d₁ * n} ∪ {x | ∃ n : ℕ, x = a₂ + d₂ * n})

end

end MetaMathlibExt
