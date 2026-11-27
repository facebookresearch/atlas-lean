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
public import Mathlib.RingTheory.Ideal.Span
public import MathlibExt.Algebra.Polynomial.FactorialEvalBound
public import MathlibExt.Algebra.Polynomial.InterpolationPolyExchange
public import MathlibExt.Algebra.Polynomial.LocallyIntegerPolynomial
public import MathlibExt.Algebra.Polynomial.LocallyIntegerPolynomialComp
public import MathlibExt.Algebra.Polynomial.LowDegreeInterpolant
public import MathlibExt.Data.Nat.ProgressionIntersection

/-!
# Locally integer polynomial functions

Statements from Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41 (arXiv `2401.17955`, TeX source read).

For `U ⊆ ℤ`, a function `f : U → ℤ` is *locally integer polynomial* (LIP) when its restriction
to every finite subset of `U` is given by a polynomial with integer coefficients. These functions
form the ring `LIP(U)`, here `lipSubring U`; `LIP(ℤ) = Lℤ[x]` is `lipSubring Set.univ`. A function
`g : ℤ → ℤ` is LIP on `U` when `U.domRestrict g ∈ lipSubring U`. The paper's interpolation
polynomial
`f_X ∈ ℚ[x]` (the unique polynomial of degree `< |X|` agreeing with `f` on the finite set `X`) is
`interpolationPoly X f`, built from Mathlib's `Lagrange.interpolate`; "`f_X ∈ ℤ[x]`" is
`interpolationPoly X f ∈ Polynomial.lifts (Int.castRingHom ℚ)`. The paper's `ℕ` is the positive
integers.
-/

open Polynomial Filter Topology

namespace MetaMathlibExt

@[expose] public section

/-- **Integer polynomials embed in LIP(U).** For every infinite set $U \subseteq \mathbb{Z}$, the
evaluation map $\mathbb{Z}[x] \to \mathrm{LIP}(U)$, sending $p$ to the function $u \mapsto p(u)$,
is injective: distinct integer polynomials give distinct functions on $U$.

The other part of Lemma 1, that $\mathrm{LIP}(U)$ is a subring of the ring of all functions
$U \to \mathbb{Z}$, holds by construction.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 1 (`integers-2025-A41-lem-1`). -/
public theorem_wanted polynomialToLIP_injective {U : Set ℤ} (hU : U.Infinite) :
    Function.Injective (polynomialToLIP U)

/-- **Locally integer polynomial functions agreeing on an infinite subset are equal.** Let
$U \subseteq V \subseteq \mathbb{Z}$ with $U$ infinite, and let $f, g : V \to \mathbb{Z}$ lie in
the ring $\mathrm{LIP}(V)$ of locally integer polynomial functions on $V$. If $f(x) = g(x)$ for
every $x \in U$, then $f = g$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Corollary 1 (`integers-2025-A41-cor-1`). -/
public theorem_wanted lip_restrict_injective {U V : Set ℤ} (hU : U.Infinite) (hUV : U ⊆ V)
    {f g : V → ℤ} (hf : f ∈ lipSubring V) (hg : g ∈ lipSubring V)
    (h : f ∘ Set.inclusion hUV = g ∘ Set.inclusion hUV) : f = g

/-- **Denominator of the top coefficient on a circuit.** Let $f : \mathbb{Z} \to \mathbb{Z}$, and
for a finite set $Y \subseteq \mathbb{Z}$ write $f_Y \in \mathbb{Q}[x]$ for the interpolation
polynomial of $f$ on $Y$. Let $X \subseteq \mathbb{Z}$ be a finite circuit for $f$: $f_X$ does not
have integer coefficients, but $f_{X \setminus \{a\}}$ has integer coefficients for every
$a \in X$. Let $c$ be the coefficient of $x^{|X|-1}$ in $f_X$ and let $q \ge 1$ be the denominator
of $c$ in lowest terms. Then $q \ne 1$, so $c$ is not an integer, and $q$ divides $a - b$ for all
$a, b \in X$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 7 (`integers-2025-A41-lem-7`), with the circuit definition preceding it. -/
public theorem_wanted circuit_coeff_den (f : ℤ → ℤ) (X : Finset ℤ)
    (hX : interpolationPoly X f ∉ Polynomial.lifts (Int.castRingHom ℚ))
    (hmin : ∀ a ∈ X, interpolationPoly (X.erase a) f ∈ Polynomial.lifts (Int.castRingHom ℚ)) :
    ((interpolationPoly X f).coeff (X.card - 1)).den ≠ 1 ∧
      ∀ a ∈ X, ∀ b ∈ X, (((interpolationPoly X f).coeff (X.card - 1)).den : ℤ) ∣ a - b

/-- **Intersection of two arithmetic progressions of natural numbers.** Let $a_1, a_2, d_1, d_2$
be natural numbers with $d_1, d_2 > 0$, where $\mathbb{N} = \{0, 1, 2, \dots\}$, and let
$P_i = \{a_i + d_i n : n \in \mathbb{N}\}$ for $i = 1, 2$. Then $P_1 \cap P_2$ is nonempty if
and only if $\gcd(d_1, d_2)$ divides the integer $a_1 - a_2$, and if $P_1 \cap P_2$ is nonempty,
then $P_1 \cap P_2 = \{a_3 + \operatorname{lcm}(d_1, d_2)\, n : n \in \mathbb{N}\}$ for some
$a_3 \in \mathbb{N}$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 8 (`integers-2025-A41-lem-8`). -/
public theorem_wanted natProgression_inter (a₁ a₂ d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    (({x | ∃ n : ℕ, x = a₁ + d₁ * n} ∩ {x | ∃ n : ℕ, x = a₂ + d₂ * n} : Set ℕ).Nonempty ↔
      ((Nat.gcd d₁ d₂ : ℕ) : ℤ) ∣ (a₁ : ℤ) - a₂) ∧
    (({x | ∃ n : ℕ, x = a₁ + d₁ * n} ∩ {x | ∃ n : ℕ, x = a₂ + d₂ * n} : Set ℕ).Nonempty →
      ∃ a₃ : ℕ, ({x | ∃ n : ℕ, x = a₁ + d₁ * n} ∩ {x | ∃ n : ℕ, x = a₂ + d₂ * n} : Set ℕ) =
        {x | ∃ n : ℕ, x = a₃ + Nat.lcm d₁ d₂ * n})

/-- **Newton series of locally integer polynomial functions.** Let $U \subseteq \mathbb{Z}$, let
$\mathbb{N} = \{0, 1, 2, \dots\}$, and let $\sigma : \mathbb{N} \to U$ be a bijection. For a
sequence of integers $a = (a_k)_{k \in \mathbb{N}}$ define $f_a : U \to \mathbb{Z}$ by
$$f_a(u) = \sum_{k=0}^{\sigma^{-1}(u)} a_k \prod_{i=0}^{k-1} (u - \sigma(i)).$$
Then $f_a$ lies in the ring $\mathrm{LIP}(U)$ of locally integer polynomial functions on $U$ for
every sequence $a$, and every $f \in \mathrm{LIP}(U)$ equals $f_a$ for exactly one sequence $a$.

For $u = \sigma(m)$ every product with $k > m$ contains the factor $u - \sigma(m) = 0$, so $f_a$
is the formal series $\sum_{k \ge 0} a_k \prod_{i < k} (x - \sigma(i))$ evaluated at $x = u$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Theorem 1 (`integers-2025-A41-thm-1`), reindexed from `σ(1), σ(2), …`. -/
public theorem_wanted lipSubring_newton_series {U : Set ℤ} (σ : ℕ ≃ U) :
    (∀ a : ℕ → ℤ, (fun u : U => ∑ k ∈ Finset.range (σ.symm u + 1),
        a k * ∏ i ∈ Finset.range k, ((u : ℤ) - σ i)) ∈ lipSubring U) ∧
    ∀ f ∈ lipSubring U, ∃! a : ℕ → ℤ, (fun u : U => ∑ k ∈ Finset.range (σ.symm u + 1),
        a k * ∏ i ∈ Finset.range k, ((u : ℤ) - σ i)) = f

/-- **A LIP function bounded by $C|x|^d$ infinitely often is a polynomial.** Let
$U \subseteq \mathbb{Z}$, let $C$ be a real number and $d \ge 0$ an integer, and let
$f \in \mathrm{LIP}(U)$. If $|f(x)| \le C|x|^d$ for infinitely many $x \in U$, then there is a
polynomial $p \in \mathbb{Z}[x]$ with $f(x) = p(x)$ for all $x \in U$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Theorem 3 (`integers-2025-A41-thm-3`). -/
public theorem_wanted mem_range_polynomialToLIP_of_bound {U : Set ℤ} (C : ℝ) (d : ℕ)
    (f : lipSubring U)
    (h : {x : U | |(((f : U → ℤ) x : ℤ) : ℝ)| ≤ C * |((x : ℤ) : ℝ)| ^ d}.Infinite) :
    f ∈ (polynomialToLIP U).range

/-- **Prime integer polynomials stay prime in LIP(U).** Let $U \subseteq \mathbb{Z}$ be infinite
and let $p$ be a prime element of $\mathbb{Z}[x]$ (a prime of $\mathbb{Z}$, or an irreducible
integer polynomial of content $1$). Then the function $u \mapsto p(u)$, the image of $p$ under
the evaluation map $\mathbb{Z}[x] \to \mathrm{LIP}(U)$, is a prime element of $\mathrm{LIP}(U)$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Corollary 2 (`integers-2025-A41-cor-2`). -/
public theorem_wanted prime_polynomialToLIP {U : Set ℤ} (hU : U.Infinite) {p : ℤ[X]}
    (hp : Prime p) : Prime (polynomialToLIP U p)

/-- **$\mathbb{Z}[x]$ is algebraically closed in $\mathrm{LIP}(U)$.** Let $U \subseteq \mathbb{Z}$
be infinite, and map each $p \in \mathbb{Z}[x]$ to the function $u \mapsto p(u)$ in
$\mathrm{LIP}(U)$. Let $f \in \mathrm{LIP}(U)$ and let $Q$ be a nonzero polynomial with
coefficients in $\mathbb{Z}[x]$ such that $Q(f) = 0$ in $\mathrm{LIP}(U)$, where the
coefficients of $Q$ are mapped into $\mathrm{LIP}(U)$ in this way. Then there is
$p \in \mathbb{Z}[x]$ with $f(u) = p(u)$ for all $u \in U$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Corollary 3 (`integers-2025-A41-cor-3`). -/
public theorem_wanted mem_range_polynomialToLIP_of_isAlgebraic {U : Set ℤ} (hU : U.Infinite)
    (f : lipSubring U) (q : Polynomial ℤ[X]) (hq : q ≠ 0)
    (hf : q.eval₂ (polynomialToLIP U) f = 0) : f ∈ (polynomialToLIP U).range

/-- **Infinite ascending chains of principal ideals in LIP rings.** Let $U \subseteq \mathbb{Z}$ be
infinite, and write $\mathrm{LIP}(U)$ for the ring of locally integer polynomial functions on $U$:
the functions $U \to \mathbb{Z}$ whose restriction to every finite subset of $U$ agrees with a
polynomial with integer coefficients. Then there are $g_0, g_1, g_2, \ldots \in \mathrm{LIP}(U)$
such that the principal ideals of $\mathrm{LIP}(U)$ they generate form a strictly increasing chain
$(g_0) \subsetneq (g_1) \subsetneq (g_2) \subsetneq \cdots$.

In particular $\mathrm{LIP}(U)$ is not Noetherian.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Theorem 4 (`integers-2025-A41-thm-4`). -/
public theorem_wanted exists_strictMono_principal_ideals {U : Set ℤ} (hU : U.Infinite) :
    ∃ g : ℕ → lipSubring U, StrictMono fun n => Ideal.span ({g n} : Set (lipSubring U))

/-- **Non-polynomial LIP functions on the integers that are small on an infinite set.** Let
$\tau : \mathbb{N} \to \mathbb{R}$ with $\tau(n) \to +\infty$ as $n \to \infty$. Write
$\mathrm{LIP}(\mathbb{Z})$ for the ring of locally integer polynomial functions on $\mathbb{Z}$:
the functions $\mathbb{Z} \to \mathbb{Z}$ whose restriction to every finite subset of $\mathbb{Z}$
agrees with a polynomial with integer coefficients. Then there is $f \in \mathrm{LIP}(\mathbb{Z})$
that is not of the form $x \mapsto p(x)$ for any $p \in \mathbb{Z}[x]$, together with an infinite
set $X \subseteq \mathbb{Z}$ such that $|f(x)| < |x|^{\tau(|x|)}$ for every $x \in X$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Theorem 6 (`integers-2025-A41-thm-6`). -/
public theorem_wanted exists_lip_univ_not_polynomial_lt_rpow (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop atTop) :
    ∃ f : lipSubring (Set.univ : Set ℤ), f ∉ (polynomialToLIP Set.univ).range ∧
      ∃ X : Set ℤ, X.Infinite ∧ ∀ x ∈ X,
        |(((f : ↥(Set.univ : Set ℤ) → ℤ) ⟨x, Set.mem_univ x⟩ : ℤ) : ℝ)| <
          |(x : ℝ)| ^ τ x.natAbs

/-- **LIP functions on $\mathbb{Z}$ below the factorial bound are polynomials.** Let $f$ lie in
$\mathrm{LIP}(\mathbb{Z})$, the ring of locally integer polynomial functions
$\mathbb{Z} \to \mathbb{Z}$. If $|f(x)| < (2|x| - 1)!/2^{2|x| - 1}$ for all but finitely many
$x \in \mathbb{Z}$, then there is a polynomial $p \in \mathbb{Z}[x]$ with $f(x) = p(x)$ for all
$x \in \mathbb{Z}$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Theorem 7 (`integers-2025-A41-thm-7`). -/
public theorem_wanted mem_range_polynomialToLIP_of_factorial_bound
    (f : lipSubring (Set.univ : Set ℤ))
    (h : ∀ᶠ x : ℤ in cofinite,
      |((((f : ↥(Set.univ : Set ℤ) → ℤ) ⟨x, Set.mem_univ x⟩ : ℤ)) : ℚ)| <
        ((2 * x.natAbs - 1).factorial : ℚ) / 2 ^ (2 * x.natAbs - 1)) :
    f ∈ (polynomialToLIP Set.univ).range

/-- **LIP continuation at two points.** Let $f : \mathbb{Z} \to \mathbb{Z}$, and for a finite set
$Y \subseteq \mathbb{Z}$ write $f_Y \in \mathbb{Q}[x]$ for the interpolation polynomial of $f$ on
$Y$. For $S \subseteq \mathbb{Z}$ write $\mathrm{LIP}(S)$ for the ring of locally integer
polynomial functions on $S$: the functions $S \to \mathbb{Z}$ whose restriction to every finite
subset of $S$ agrees with a polynomial with integer coefficients. Let $X \subseteq \mathbb{Z}$ be
finite and $a, b \in \mathbb{Z}$ such that $f_{X \cup \{a, b\}}$ does not have integer
coefficients, while $f_{X \cup \{a\}}$ and $f_{X \cup \{b\}}$ both do (this forces $a \ne b$ and
$a, b \notin X$). Put $V = \{x \in \mathbb{Z} : \gcd(x - a, a - b) = 1\}$. Then $|a - b| \ge 2$,
and there is a function $g : \mathbb{Z} \to \mathbb{Z}$ with $g(x) = f(x)$ for all
$x \in X \cup \{a, b\}$ whose restriction to $X \cup V \cup \{a\}$ lies in
$\mathrm{LIP}(X \cup V \cup \{a\})$ and whose restriction to $X \cup V \cup \{b\}$ lies in
$\mathrm{LIP}(X \cup V \cup \{b\})$.

This is the form of Theorem 8 established in its proof in the source.

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

/-- **Locally integer polynomial functions on a union of sets.** For $S \subseteq \mathbb{Z}$, write
$\mathrm{LIP}(S)$ for the ring of locally integer polynomial functions $S \to \mathbb{Z}$. Let
$(V_i)_{i \in I}$ be a family of subsets of $\mathbb{Z}$ with union $U = \bigcup_{i \in I} V_i$.
Suppose that for all $i, j \in I$, not necessarily distinct, and all $a_1 \in V_i$ and
$a_2 \in V_j$ with $a_1 \ne a_2$, the set $V_i \cap V_j$ contains infinitely many elements of
$\{a_1 + (a_2 - a_1) n : n \in \mathbb{Z}\}$. Then for every $f : \mathbb{Z} \to \mathbb{Z}$, the
restriction of $f$ to $U$ lies in $\mathrm{LIP}(U)$ if and only if, for every $i \in I$, the
restriction of $f$ to $V_i$ lies in $\mathrm{LIP}(V_i)$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Theorem 9 (`integers-2025-A41-thm-9`). -/
public theorem_wanted lip_iUnion_iff {ι : Type*} (V : ι → Set ℤ) (f : ℤ → ℤ)
    (hV : ∀ i j, ∀ a₁ ∈ V i, ∀ a₂ ∈ V j, a₁ ≠ a₂ →
      (V i ∩ V j ∩ {x | ∃ n : ℤ, x = a₁ + (a₂ - a₁) * n}).Infinite) :
    (⋃ i, V i).domRestrict f ∈ lipSubring (⋃ i, V i) ↔
      ∀ i, (V i).domRestrict f ∈ lipSubring (V i)

/-- **Locally integer polynomial functions on cofinite sets of positive integers.** Let
$\mathbb{N}^+ = \{n \in \mathbb{Z} : n > 0\}$, let $U \subseteq \mathbb{N}^+$ with
$\mathbb{N}^+ \setminus U$ finite, let $f : \mathbb{Z} \to \mathbb{Z}$, and for
$S \subseteq \mathbb{Z}$ write $\mathrm{LIP}(S)$ for the ring of locally integer polynomial (LIP)
functions $S \to \mathbb{Z}$. Then the restriction of $f$ to $U$ lies in $\mathrm{LIP}(U)$ if and
only if every $a \in U$ lies in some $W \subseteq U$ with $\mathbb{N}^+ \setminus W$ finite such
that the restriction of $f$ to $W$ lies in $\mathrm{LIP}(W)$.

In the cofinite topology on $\mathbb{N}^+$ the nonempty open sets are the subsets with finite
complement, so this says that a function which is LIP on an open neighbourhood of each point of
a nonempty open set $U$ is LIP on $U$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Corollary 4 (`integers-2025-A41-cor-4`). -/
public theorem_wanted lip_sheaf_cofinite_nat (U : Set ℤ) (hUS : U ⊆ {n | 0 < n})
    (hU : ({n : ℤ | 0 < n} \ U).Finite) (f : ℤ → ℤ) :
    (∀ a ∈ U, ∃ W ⊆ U, a ∈ W ∧ ({n : ℤ | 0 < n} \ W).Finite ∧
      W.domRestrict f ∈ lipSubring W) ↔ U.domRestrict f ∈ lipSubring U

/-- **Locally integer polynomial functions on cofinite subsets of the integers.** Let
$U \subseteq \mathbb{Z}$ have finite complement, let $f : \mathbb{Z} \to \mathbb{Z}$, and for
$S \subseteq \mathbb{Z}$ write $\mathrm{LIP}(S)$ for the ring of locally integer polynomial (LIP)
functions $S \to \mathbb{Z}$. Then the restriction of $f$ to $U$ lies in $\mathrm{LIP}(U)$ if and
only if every $a \in U$ lies in some $W \subseteq U$ with finite complement in $\mathbb{Z}$ such
that the restriction of $f$ to $W$ lies in $\mathrm{LIP}(W)$.

In the cofinite topology on $\mathbb{Z}$ the nonempty open sets are the sets with finite
complement, so this says that a function which is LIP on an open neighbourhood of each point of
a nonempty open set $U$ is LIP on $U$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Corollary 4 (`integers-2025-A41-cor-4`). -/
public theorem_wanted lip_sheaf_cofinite_int (U : Set ℤ) (hU : Uᶜ.Finite) (f : ℤ → ℤ) :
    (∀ a ∈ U, ∃ W ⊆ U, a ∈ W ∧ Wᶜ.Finite ∧ W.domRestrict f ∈ lipSubring W) ↔
      U.domRestrict f ∈ lipSubring U

/-- **Locally integer polynomial functions on density one sets of positive integers.** Say that
a set $S$ of positive integers has natural density one if $\#(S \cap [1, x]) / x \to 1$ as the
natural number $x$ tends to infinity, and write $\mathrm{LIP}(S)$ for the ring of locally
integer polynomial (LIP) functions $S \to \mathbb{Z}$. Let $U$ be a set of positive integers of
natural density one and let $f : \mathbb{Z} \to \mathbb{Z}$. Then the restriction of $f$ to $U$
lies in $\mathrm{LIP}(U)$ if and only if every $a \in U$ lies in some $W \subseteq U$ of natural
density one such that the restriction of $f$ to $W$ lies in $\mathrm{LIP}(W)$.

In the density one topology on the positive integers the nonempty open sets are the sets of
natural density one, so this says that a function which is LIP on an open neighbourhood of each
point of a nonempty open set $U$ is LIP on $U$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Corollary 4 (`integers-2025-A41-cor-4`). -/
public theorem_wanted lip_sheaf_densityOne_nat (U : Set ℤ) (hUS : U ⊆ {n | 0 < n})
    (hU : Tendsto (fun x : ℕ => ((U ∩ Set.Icc 1 (x : ℤ)).ncard : ℝ) / x) atTop (𝓝 1))
    (f : ℤ → ℤ) :
    (∀ a ∈ U, ∃ W ⊆ U, a ∈ W ∧
      Tendsto (fun x : ℕ => ((W ∩ Set.Icc 1 (x : ℤ)).ncard : ℝ) / x) atTop (𝓝 1) ∧
      W.domRestrict f ∈ lipSubring W) ↔ U.domRestrict f ∈ lipSubring U

/-- **Locally integer polynomial functions on density one subsets of the integers.** Say that
$S \subseteq \mathbb{Z}$ has density one if $\#(S \cap [-x, x]) / (2x + 1) \to 1$ as the natural
number $x$ tends to infinity, and write $\mathrm{LIP}(S)$ for the ring of locally integer
polynomial (LIP) functions $S \to \mathbb{Z}$. Let $U \subseteq \mathbb{Z}$ have density one and
let $f : \mathbb{Z} \to \mathbb{Z}$. Then the restriction of $f$ to $U$ lies in $\mathrm{LIP}(U)$
if and only if every $a \in U$ lies in some $W \subseteq U$ of density one such that the
restriction of $f$ to $W$ lies in $\mathrm{LIP}(W)$.

In the density one topology on $\mathbb{Z}$ the nonempty open sets are the sets of density one,
so this says that a function which is LIP on an open neighbourhood of each point of a nonempty
open set $U$ is LIP on $U$.

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

/-- **Locally integer polynomial functions on cofinite sets of primes.** Let $P$ be the set of
positive prime numbers in $\mathbb{Z}$, let $U \subseteq P$ with $P \setminus U$ finite, let
$f : \mathbb{Z} \to \mathbb{Z}$, and for $S \subseteq \mathbb{Z}$ write $\mathrm{LIP}(S)$ for the
ring of locally integer polynomial (LIP) functions $S \to \mathbb{Z}$. Then the restriction of
$f$ to $U$ lies in $\mathrm{LIP}(U)$ if and only if every $a \in U$ lies in some $W \subseteq U$
with $P \setminus W$ finite such that the restriction of $f$ to $W$ lies in $\mathrm{LIP}(W)$.

In the cofinite topology on $P$ the nonempty open sets are the subsets with finite complement,
so this says that a function which is LIP on an open neighbourhood of each point of a nonempty
open set $U$ is LIP on $U$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Corollary 5 (`integers-2025-A41-cor-5`). -/
public theorem_wanted lip_sheaf_cofinite_primes (U : Set ℤ) (hUS : U ⊆ {p | Prime p ∧ 0 < p})
    (hU : ({p : ℤ | Prime p ∧ 0 < p} \ U).Finite) (f : ℤ → ℤ) :
    (∀ a ∈ U, ∃ W ⊆ U, a ∈ W ∧ ({p : ℤ | Prime p ∧ 0 < p} \ W).Finite ∧
      W.domRestrict f ∈ lipSubring W) ↔ U.domRestrict f ∈ lipSubring U

/-- **Gluing LIP functions on two intersecting progressions.** Let $a_1, a_2 \ge 0$ and
$d_1, d_2 \ge 1$ be integers, let $U_i = \{a_i + d_i n : n \in \mathbb{Z}, n \ge 0\}$ for
$i = 1, 2$, and suppose $U_1 \cap U_2$ is nonempty. If $f : \mathbb{Z} \to \mathbb{Z}$ restricts
to an element of $\mathrm{LIP}(U_1)$ on $U_1$ and to an element of $\mathrm{LIP}(U_2)$ on $U_2$,
then the restriction of $f$ to $U_1 \cup U_2$ lies in $\mathrm{LIP}(U_1 \cup U_2)$.

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
