/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import MathlibExt.Combinatorics.AccessibleSets

/-!
# Accessible and large sets (statements)

Statement-only targets from Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25
(2025), Article A64. Colorings are maps `ℕ+ → Fin r` (the paper's `ℕ` is the positive integers),
`D`-diffsequences are integer sequences with consecutive differences in `D`, and minimal systems
are compact metric spaces with a homeomorphism admitting no proper nonempty closed invariant set.
The colorings here are of `ℕ+`, unlike `MathlibExt.Combinatorics.PrimeTwoAccessibilityWanted`,
whose `IsRAccessible` colors all of `ℕ`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Growth bound for the degree of accessibility.** Let $r \ge 2$, let $d_0 < d_1 < d_2 < \cdots$
be a strictly increasing sequence of natural numbers with $d_0 > 0$, and let
$D = \{d_n : n \ge 0\}$. If there are a real number $\delta > 0$ and an integer $N \ge 1$ such that
$d_{n+1} \ge \left(2 + \frac{1}{r-1} + \delta\right) d_n$ for every $n \ge N - 1$, then $D$ is not
$r$-accessible.

In the paper's terms, the degree of accessibility of $D$ is at most $r - 1$; the enumeration here
starts at index $0$, so $d_n$ is the paper's $d_{n+1}$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 1. -/
public theorem_wanted accessibility_degree_growth_bound (r : ℕ) (D : Set ℕ)
    (d : ℕ → ℕ) (hr : 2 ≤ r) (hmono : StrictMono d)
    (hD : D = Set.range d) (hd0 : 0 < d 0) (δ : ℝ) (hδ : 0 < δ)
    (N : ℕ) (hN : 0 < N)
    (hgrowth : ∀ n : ℕ, N ≤ n + 1 →
      (d (n + 1) : ℝ) ≥
        (2 + (((r - 1 : ℕ) : ℝ)⁻¹) + δ) * (d n : ℝ)) :
    ¬ IsRAccessible r D

/-- **Fast eventual growth rules out 2-accessibility.** Let $d_0 < d_1 < d_2 < \cdots$ be a
strictly increasing sequence of natural numbers with $d_0 > 0$, and let
$D = \{d_n : n \in \mathbb{N}\}$. Suppose there are a real number $\delta > 0$ and a natural
number $N \ge 1$ such that $d_{n+1} \ge (3 + \delta) d_n$ for every $n \in \mathbb{N}$ with
$n + 1 \ge N$. Then $D$ is not $2$-accessible.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Corollary 1. -/
public theorem_wanted not_two_accessible_of_growth (D : Set ℕ) (d : ℕ → ℕ)
    (hmono : StrictMono d) (hD : D = Set.range d) (hd0 : 0 < d 0)
    (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 0 < N)
    (hgrowth : ∀ n : ℕ, N ≤ n + 1 →
      (d (n + 1) : ℝ) ≥ (3 + δ) * (d n : ℝ)) :
    ¬ IsRAccessible 2 D

/-- **2-large sets contain multiples of every positive integer.** Every $2$-large set $D$ of
positive integers contains a multiple of each positive integer $m$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 2. -/
public theorem_wanted two_large_contains_multiples (D : Set ℕ) (h : IsRLarge 2 D) :
    ∀ m : ℕ, 0 < m → ∃ d ∈ D, m ∣ d

/-- **Finite removal preserves $r$-largeness.** Let $r$ be a natural number. If a set
$D \subseteq \mathbb{N}$ is $r$-large and $F \subseteq \mathbb{N}$ is finite, then $D \setminus F$
is $r$-large.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 3. -/
public theorem_wanted rLarge_sdiff_finite (r : ℕ) (D F : Set ℕ)
    (hD : IsRLarge r D) (hF : F.Finite) :
    IsRLarge r (D \ F)

/-- **Sets growing by a factor of three are not 2-large.** Let $d_0 < d_1 < d_2 < \cdots$ be a
strictly increasing sequence of natural numbers with $d_0 > 0$ and $d_{n+1} \ge 3 d_n$ for every
$n \in \mathbb{N}$, and let $D = \{d_n : n \in \mathbb{N}\}$. Then $D$ is not $2$-large.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 5. -/
public theorem_wanted not_two_large_of_triple_growth (D : Set ℕ) (d : ℕ → ℕ)
    (hmono : StrictMono d) (hD : D = Set.range d) (hd0 : 0 < d 0)
    (hgrowth : ∀ n : ℕ, d (n + 1) ≥ 3 * d n) :
    ¬ IsRLarge 2 D

/-- **Dilates of a finite union of lacunary sets stay away from the integers.** Let $\ell \ge 1$
and let $S_0, \dots, S_{\ell-1} \subseteq \mathbb{N}$ be lacunary sets with union
$S = \bigcup_i S_i$. Then there are real numbers $\alpha$ and $\varepsilon > 0$ such that the
infimum over $s \in S$ of the distance $|\alpha s - \operatorname{round}(\alpha s)|$ from
$\alpha s$ to its nearest integer $\operatorname{round}(\alpha s)$ equals $\varepsilon$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 6. -/
public theorem_wanted lacunary_union_avoids_integers (ℓ : ℕ) (hℓ : 0 < ℓ)
    (S : Fin ℓ → Set ℕ) (hS : ∀ i, IsLacunarySet (S i)) :
    ∃ α ε : ℝ, 0 < ε ∧
      sInf ((fun s : ℕ => |α * (s : ℝ) - round (α * (s : ℝ))|) '' (⋃ i, S i)) = ε

/-- **Two-colorings avoiding long $D$-progressions.** Let $D$ be a set of positive integers,
let $\alpha$ be a real number and let $\varepsilon > 0$ be such that
$\lVert \alpha d \rVert \ge \varepsilon$ for every $d \in D$, where $\lVert t \rVert$ denotes the
distance from $t$ to the nearest integer. Then there is a $2$-coloring of the positive integers
with no monochromatic $D$-arithmetic progression of length $\lceil 1/(2\varepsilon) \rceil + 1$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 7. -/
public theorem_wanted two_coloring_avoids_long_DAP (D : Set ℕ)
    (hD : D ⊆ Set.Ioi 0) (α ε : ℝ) (hε : 0 < ε)
    (hsep : ∀ d ∈ D, ε ≤ |α * (d : ℝ) - round (α * (d : ℝ))|) :
    ∃ c : ℕ+ → Fin 2,
      ¬ ∃ x : Fin (Nat.ceil ((2 * ε)⁻¹) + 1) → ℕ+,
        IsMonochromatic c x ∧ IsDAP D (Nat.ceil ((2 * ε)⁻¹) + 1) x

/-- **Finite unions of lacunary sets are not 2-large.** For every $n \ge 1$ and all lacunary sets
$D_1, \dots, D_n$, the union $D_1 \cup \dots \cup D_n$ is not 2-large.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 8. -/
public theorem_wanted finite_union_lacunary_not_two_large (n : ℕ) (hn : 0 < n)
    (D : Fin n → Set ℕ) (hD : ∀ i, IsLacunarySet (D i)) :
    ¬ IsRLarge 2 (⋃ i, D i)

/-- **Positive values of a polynomial vanishing at zero form a large set.** Let $p$ be a
polynomial with integer coefficients, positive leading coefficient and $p(0) = 0$. Then the set
of positive integers $d$ such that $p(n) = d$ for some positive integer $n$ is large.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 9. -/
public theorem_wanted polynomial_range_large (p : Polynomial ℤ)
    (hlead : 0 < p.leadingCoeff) (hzero : p.eval 0 = 0) :
    IsLarge {d : ℕ | 0 < d ∧ ∃ n : ℕ+, p.eval (n : ℤ) = (d : ℤ)}

/-- **A coloring criterion for accessibility of a shifted set.** Let $r \ge 2$ and $c$ be natural
numbers, let $D$ be a set of positive integers, and write $D + c = \{d + c : d \in D\}$. Suppose
that for every coloring of $D$ with $r - 1$ colors and every $k \ge 1$ there are
$x_0, \dots, x_{k-1} \in D$, all of the same color, that form a $(D + c)$-diffsequence, that is,
$x_{i+1} - x_i \in D + c$ for every $i < k - 1$. Then $D + c$ is $r$-accessible.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 10. -/
public theorem_wanted accessible_of_colored_subset_diffsequences (c r : ℕ)
    (hr : 2 ≤ r) (D : Set ℕ) (hD : D ⊆ Set.Ioi 0)
    (hcolor : ∀ χ : ({n : ℕ+ // (n : ℕ) ∈ D} → Fin (r - 1)),
      ∀ k : ℕ, 1 ≤ k →
        ∃ x : Fin k → {n : ℕ+ // (n : ℕ) ∈ D},
          (∀ i j, χ (x i) = χ (x j)) ∧
          IsDDiffSequence {e : ℕ | ∃ d ∈ D, e = d + c}
            (fun i => (((x i : {n : ℕ+ // (n : ℕ) ∈ D}) : ℕ+) : ℕ))) :
    IsRAccessible r {e : ℕ | ∃ d ∈ D, e = d + c}

/-- **Integral quotients of an accessible set.** Let $d \ge 1$ and $r$ be natural numbers and let
$A$ be a set of natural numbers. If $A$ is $rd$-accessible, then the set $\{n \ge 1 : nd \in A\}$,
that is, the positive integers of the form $a/d$ with $a \in A$, is $r$-accessible.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 11(i). -/
public theorem_wanted accessible_integral_quotients (A : Set ℕ) (d r : ℕ)
    (hd : 0 < d) (hA : IsRAccessible (r * d) A) :
    IsRAccessible r {n : ℕ | 0 < n ∧ ∃ a ∈ A, a = n * d}

/-- **A 2-coloring with no monochromatic 6-term progression with positive Fibonacci gap.** There
is a coloring of the positive integers with two colors such that no 6-term arithmetic progression
$a, a + d, \dots, a + 5d$ of positive integers whose gap $d$ is a positive Fibonacci number is
monochromatic.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Proposition 1 (coloring claim). -/
public theorem_wanted fibonacci_two_coloring_avoids_six_term_AP :
    ∃ c : ℕ+ → Fin 2,
      ¬ ∃ x : Fin 6 → ℕ+,
        IsMonochromatic c x ∧ IsDAP positiveFibonacciSet 6 x

/-- **The positive Fibonacci set is not 2-large.** Let $F_n$ denote the $n$-th Fibonacci number,
with $F_0 = 0$ and $F_1 = 1$. The positive Fibonacci set
$\{F_n : n \ge 2\} = \{1, 2, 3, 5, 8, \dots\}$ is not $2$-large.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Proposition 1 (consequence). -/
public theorem_wanted fibonacci_not_two_large :
    ¬ IsRLarge 2 positiveFibonacciSet

/-- **A 2-coloring with no monochromatic 4-term even-Fibonacci diffsequence.** Let $F_m$ denote
the $m$-th Fibonacci number, with $F_0 = 0$ and $F_1 = 1$, and let
$E = \{F_{3n+3} : n \ge 0\} = \{2, 8, 34, \dots\}$ be the even Fibonacci set. There is a coloring
of the positive integers with $2$ colors under which no four positive integers
$x_0, x_1, x_2, x_3$ of the same color satisfy $x_{i+1} - x_i \in E$ for $i = 0, 1, 2$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Proposition 2 (coloring claim). -/
public theorem_wanted even_fibonacci_two_coloring_avoids_four_term_diffsequence :
    ∃ c : ℕ+ → Fin 2,
      ¬ ∃ x : Fin 4 → ℕ+,
        IsMonochromatic c x ∧
          IsDDiffSequence evenFibonacciSet (fun i => ((x i : ℕ) : ℤ))

/-- **The even Fibonacci set is not 2-accessible.** Let $F_m$ denote the $m$-th Fibonacci number,
with $F_0 = 0$ and $F_1 = 1$. The even Fibonacci set
$\{F_{3n+3} : n \ge 0\} = \{2, 8, 34, \dots\}$ is not $2$-accessible.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Proposition 2 (consequence). -/
public theorem_wanted even_fibonacci_not_two_accessible :
    ¬ IsRAccessible 2 evenFibonacciSet

/-- **Furstenberg–Weiss correspondence for translation-invariant families.** Let $\mathcal{A}$ be
a collection of finite sets of integers that is closed under translation, that is,
$A + t \in \mathcal{A}$ for all $A \in \mathcal{A}$ and $t \in \mathbb{Z}$, and let $r \ge 1$.
For a homeomorphism $T$ and an integer $a$, write $T^{-a}(U)$ for the preimage of $U$ under the
$a$-th power of $T$. Then the following three conditions are equivalent: (a) for every coloring
of $\mathbb{Z}$ with $r$ colors there are a color $i$ and a set $A \in \mathcal{A}$ all of whose
elements have color $i$; (b) for every nonempty compact metric space $X$, every homeomorphism
$T$ of $X$ and every cover of $X$ by $r$ open sets $U_1, \dots, U_r$, there are $i$ and
$A \in \mathcal{A}$ such that $\bigcap_{a \in A} T^{-a}(U_i)$ is nonempty; (c) the same holds
for every nonempty compact metric space $X$, every minimal homeomorphism $T$ of $X$ and every
cover of $X$ by $r$ clopen sets $U_1, \dots, U_r$.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Lemma 1. -/
public theorem_wanted furstenberg_weiss_correspondence
    (𝒜 : Set (Finset ℤ))
    (htrans : ∀ A ∈ 𝒜, ∀ t : ℤ, A.image (fun a => a + t) ∈ 𝒜)
    (r : ℕ) (hr : 1 ≤ r) :
    ((∀ c : ℤ → Fin r, ∃ i : Fin r, ∃ A ∈ 𝒜, ∀ a ∈ A, c a = i) ↔
      (∀ (X : Type) [MetricSpace X] [CompactSpace X] [Nonempty X]
        (T : X ≃ₜ X)
        (U : Fin r → Set X),
        (∀ i, IsOpen (U i)) → (∀ x, ∃ i, x ∈ U i) →
          ∃ i : Fin r, ∃ A ∈ 𝒜,
            (⋂ a : A, iteratePreimage T (a : ℤ) (U i)).Nonempty)) ∧
    ((∀ (X : Type) [MetricSpace X] [CompactSpace X] [Nonempty X]
        (T : X ≃ₜ X)
        (U : Fin r → Set X),
        (∀ i, IsOpen (U i)) → (∀ x, ∃ i, x ∈ U i) →
          ∃ i : Fin r, ∃ A ∈ 𝒜,
            (⋂ a : A, iteratePreimage T (a : ℤ) (U i)).Nonempty) ↔
      (∀ (X : Type) [MetricSpace X] [CompactSpace X] [Nonempty X]
        (T : X ≃ₜ X),
        IsMinimalSystem T → ∀ U : Fin r → Set X,
        (∀ i, IsClopen (U i)) → (∀ x, ∃ i, x ∈ U i) →
          ∃ i : Fin r, ∃ A ∈ 𝒜,
            (⋂ a : A, iteratePreimage T (a : ℤ) (U i)).Nonempty))

/-- **Topological recurrence, accessibility and chromatic intersectivity.** Let $D$ be a set
of positive integers. Say that $D$ has *diffsequence recurrence* if for every compact metric
space $X$, every minimal homeomorphism $T$ of $X$, every nonempty open set $U \subseteq X$ and
every $k \ge 1$ there are integers $s_1, \dots, s_k$ forming a $D$-diffsequence such that
$U \cap T^{-s_1}U \cap \dots \cap T^{-s_k}U$ is nonempty, where $T^{-s}U$ is the preimage of $U$
under the integer power $T^s$. Then the following are equivalent: $D$ is a set of topological
recurrence; $D$ has diffsequence recurrence; $D$ is accessible; $D$ is chromatically
intersective.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 13. -/
public theorem_wanted recurrence_accessibility_equivalences (D : Set ℕ)
    (hD : D ⊆ Set.Ioi 0) :
    (IsTopologicalRecurrence D ↔
      ∀ (X : Type) [MetricSpace X] [CompactSpace X] (T : X ≃ₜ X),
        IsMinimalSystem T → ∀ U : Set X, IsOpen U → U.Nonempty →
          ∀ k : ℕ, 1 ≤ k → ∃ s : Fin k → ℤ,
            IsDDiffSequence D s ∧
              (U ∩ ⋂ i : Fin k, iteratePreimage T (s i) U).Nonempty) ∧
    ((∀ (X : Type) [MetricSpace X] [CompactSpace X] (T : X ≃ₜ X),
        IsMinimalSystem T → ∀ U : Set X, IsOpen U → U.Nonempty →
          ∀ k : ℕ, 1 ≤ k → ∃ s : Fin k → ℤ,
            IsDDiffSequence D s ∧
              (U ∩ ⋂ i : Fin k, iteratePreimage T (s i) U).Nonempty) ↔
      IsAccessible D) ∧
    (IsAccessible D ↔ IsChromaticallyIntersective D)

/-- **One part of a union inherits $k$-topological recurrence.** Let $k$ be a natural number
and let $D_1, D_2 \subseteq \mathbb{N}$. If $D_1 \cup D_2$ is a set of $k$-topological recurrence,
then $D_1$ or $D_2$ is a set of $k$-topological recurrence.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 14. -/
public theorem_wanted topological_recurrence_union_partition (k : ℕ)
    (D D₁ D₂ : Set ℕ) (hD : D = D₁ ∪ D₂)
    (hrec : IsLTopologicalRecurrence k D) :
    IsLTopologicalRecurrence k D₁ ∨ IsLTopologicalRecurrence k D₂

end

end MetaMathlibExt
