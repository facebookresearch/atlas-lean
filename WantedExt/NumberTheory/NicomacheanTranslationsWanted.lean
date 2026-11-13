/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Nat.Nth
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Translations and extensions of the Nicomachean identity

Statements from Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the
Nicomachean Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3.

For a finite sequence `σ = (a_1, …, a_n)` the paper's operator is
`ν(σ) = (∑ a_i)^2 - ∑ a_i^3`, here `nicomacheanNu` on lists over a commutative ring; the
classical identity is `ν(1, 2, …, n) = 0`. Sequences are lists (repetitions allowed; `ν` does not
depend on the order).
-/

open Filter Topology PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- **Nicomachean defect.** For a finite sequence $\sigma = (a_1, \ldots, a_n)$ of elements of a
commutative ring, the Nicomachean defect of $\sigma$ is
$\nu(\sigma) = \left(\sum_{i=1}^n a_i\right)^2 - \sum_{i=1}^n a_i^3$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Section 1. -/
def nicomacheanNu {R : Type*} [CommRing R] (σ : List R) : R :=
  σ.sum ^ 2 - (σ.map (· ^ 3)).sum

/-- **Examples of the Nicomachean defect.** For the Nicomachean defect $\nu$ of a sequence of
integers, $\nu(1, 2, 3, 4) = 0$, $\nu(1, 2) = 0$, $\nu(3, 3, 3) = 0$,
$\nu(1, 2, 2, 3, 4, 5, 6, 8) = 0$ and $\nu(1, 2, 2, 3, 4, 6, 6, 8) = -28$.

The last two are the values at $x = 5$ and $x = 6$ of the paper's identity
$\nu(1, 2, 2, 3, 4, x, 6, 8) = (5 - x)(x - 4)(8 + x)$; the identity itself is not stated here.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Section 1. -/
theorem nicomacheanNu_examples :
    nicomacheanNu ([1, 2, 3, 4] : List ℤ) = 0 ∧ nicomacheanNu ([1, 2] : List ℤ) = 0 ∧
      nicomacheanNu ([3, 3, 3] : List ℤ) = 0 ∧
      nicomacheanNu ([1, 2, 2, 3, 4, 5, 6, 8] : List ℤ) = 0 ∧
      nicomacheanNu ([1, 2, 2, 3, 4, 6, 6, 8] : List ℤ) = -28 := by
  decide

/-- **The Nicomachean progression factor.** For rational numbers $n$, $s$ and $a$, define

$$\alpha(n, s, a) = 2n^2 + na - a^2 + \frac{n(n-1)(s - s^2)}{2} - (n-1)as.$$

This is the second factor of $\nu(S_m)$, where
$\nu(a_1, \dots, a_k) = (a_1 + \dots + a_k)^2 - (a_1^3 + \dots + a_k^3)$ is the Nicomachean defect,
$S = (a, a + s, \dots, a + (n-1)s)$, and $S_m$ joins $n$ copies of $n$ with the translated
progressions $S, S + n, \dots, S + mn$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Section 6, equation (nusm). -/
def nicomacheanAlpha (n s a : ℚ) : ℚ :=
  2 * n ^ 2 + n * a - a ^ 2 + n * (n - 1) * (s - s ^ 2) / 2 - (n - 1) * a * s

/-- **Specializations of the Nicomachean factor at $s = 1, 2, 3$.** Let
$\alpha(n, s, a) = 2n^2 + na - a^2 + n(n-1)(s - s^2)/2 - (n-1)as$. For all rational numbers $n$
and $a$, $\alpha(n, 1, a) = 2n^2 + a - a^2$, $\alpha(n, 2, a) = n^2 + (1 - a)n - a^2 + 2a$ and
$\alpha(n, 3, a) = -(a + n - 3)(a + n)$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Section 6. -/
theorem nicomacheanAlpha_one_two_three (n a : ℚ) :
    nicomacheanAlpha n 1 a = 2 * n ^ 2 + a - a ^ 2 ∧
      nicomacheanAlpha n 2 a = n ^ 2 + (1 - a) * n - a ^ 2 + 2 * a ∧
      nicomacheanAlpha n 3 a = -(a + n - 3) * (a + n) := by
  refine ⟨?_, ?_, ?_⟩ <;> · unfold nicomacheanAlpha; ring

/-- **Second differences of roots of translated Nicomachean bag squares.** Write
$\nu(a_1, \dots, a_k) = (a_1 + \dots + a_k)^2 - (a_1^3 + \dots + a_k^3)$ for the Nicomachean defect
of a finite sequence. For natural numbers $m$ let

$$t(m) = \frac{3(m^2 - 6m - 3) + \sqrt{3(m-1)^2(35m^2 + 34m + 11)}}{24},$$

$$s(m) = \frac{3(m^2 - 6m - 3) - \sqrt{3(m-1)^2(35m^2 + 34m + 11)}}{24},$$

let $A_m^2$ be the sequence of the $m^2$ products $ij$ with $1 \le i, j \le m$ (the bag square of
$(1, 2, \dots, m)$), let $A_m^2 + x$ be the sequence obtained by adding $x$ to every entry, and let
$\rho(m)$ be the supremum of the set of real $x$ with $\nu(A_m^2 + x) = 0$. Then, as $m \to \infty$,
the second differences $t(m+2) - 2t(m+1) + t(m)$ and $\rho(m+2) - 2\rho(m+1) + \rho(m)$ converge
to $(3 + \sqrt{105})/12$, and $s(m+2) - 2s(m+1) + s(m)$ converges to $(3 - \sqrt{105})/12$.

For $m \ge 1$, $\nu(A_m^2 + x)$ is a cubic polynomial in $x$ with leading coefficient $-m^2$, so
$\rho(m)$ is its largest real root.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 1
(`jis-2024-24.6.3-prop-1`). -/
public theorem_wanted nicomachean_bagSquare_root_secondDifference_tendsto :
    let t : ℕ → ℝ := fun m => (3 * ((m : ℝ) ^ 2 - 6 * m - 3) +
      Real.sqrt (3 * ((m : ℝ) - 1) ^ 2 * (35 * (m : ℝ) ^ 2 + 34 * m + 11))) / 24
    let s : ℕ → ℝ := fun m => (3 * ((m : ℝ) ^ 2 - 6 * m - 3) -
      Real.sqrt (3 * ((m : ℝ) - 1) ^ 2 * (35 * (m : ℝ) ^ 2 + 34 * m + 11))) / 24
    let ρ : ℕ → ℝ := fun m => sSup {x : ℝ | nicomacheanNu
      (((List.range' 1 m).flatMap fun i => (List.range' 1 m).map fun j => ((i * j : ℕ) : ℝ)).map
        (· + x)) = 0}
    Tendsto (fun m => t (m + 2) - 2 * t (m + 1) + t m) atTop (𝓝 ((3 + Real.sqrt 105) / 12)) ∧
      Tendsto (fun m => s (m + 2) - 2 * s (m + 1) + s m) atTop
        (𝓝 ((3 - Real.sqrt 105) / 12)) ∧
      Tendsto (fun m => ρ (m + 2) - 2 * ρ (m + 1) + ρ m) atTop (𝓝 ((3 + Real.sqrt 105) / 12))

/-- **Nicomachean sequences of rationals with large denominators.** Write
$\nu(a_1, \dots, a_n) = (a_1 + \dots + a_n)^2 - (a_1^3 + \dots + a_n^3)$ for the Nicomachean defect
of a finite sequence. For every natural number $Q$ there is a finite sequence $\sigma$ of positive
rational numbers with $\nu(\sigma) = 0$ having an entry whose denominator in lowest terms is
greater than $Q$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 3
(`jis-2024-24.6.3-prop-3`). -/
public theorem_wanted exists_pos_rat_nicomacheanNu_eq_zero_large_den (Q : ℕ) :
    ∃ σ : List ℚ, (∀ x ∈ σ, 0 < x) ∧ nicomacheanNu σ = 0 ∧ ∃ x ∈ σ, Q < x.den

/-- **Two-valued Nicomachean sequences with a large gap.** Write
$\nu(a_1, \dots, a_n) = (a_1 + \dots + a_n)^2 - (a_1^3 + \dots + a_n^3)$ for the Nicomachean defect
of a finite sequence. For every real $\varepsilon > 0$ there are integers $0 < a < b$ and a finite
sequence $\sigma$ whose entries all equal $a$ or $b$, in which both $a$ and $b$ occur, such that
$\nu(\sigma) = 0$ and $(b - a)/L > 1 - \varepsilon$, where $L$ is the length of $\sigma$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 4
(`jis-2024-24.6.3-prop-4`). -/
public theorem_wanted exists_two_valued_nicomachean_large_gap {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : ℤ, 0 < a ∧ a < b ∧ ∃ σ : List ℤ, (∀ x ∈ σ, x = a ∨ x = b) ∧ a ∈ σ ∧ b ∈ σ ∧
      nicomacheanNu σ = 0 ∧ 1 - ε < ((b - a : ℤ) : ℝ) / σ.length

/-- **Generating functions for run-and-repeat Nicomachean sequences.** For integers $j, m \ge 1$
let $\sigma(j, m)$ be the integer sequence $(1, 2, \ldots, j + 1, m, \ldots, m)$ in which $m$ is
repeated $2j$ times, and let $\nu$ denote the Nicomachean defect. Call $j \ge 1$ admissible if
$\nu(\sigma(j, m)) = 0$ for some integer $m \ge 1$, let $j_k$ be the $k$-th smallest admissible
integer (counting from $k = 0$), and let $m_k = j_k + \lfloor \sqrt{2j_k^2 + 3j_k + 2} \rfloor$.
Then $\nu(\sigma(j_k, m_k)) = 0$ for every $k$, and in the ring of formal power series over
$\mathbb{Z}$
$$
(X - 1)(1 - 6X + X^2)(1 + 6X + X^2) \sum_{k \ge 0} j_k X^k = X^4 + X^3 - 19X^2 - 5X - 2
$$
and
$$
(1 - X)(1 - 6X + X^2)(1 + 6X + X^2) \sum_{k \ge 0} m_k X^k = 6(1 + X)^2.
$$

For admissible $j$ the square root is an integer and $m = j + \sqrt{2j^2 + 3j + 2}$ is the
positive root of $\nu(\sigma(j, m)) = 0$ in $m$, so these say that $(j_k)$ and $(m_k)$ have the
generating functions $(x^4 + x^3 - 19x^2 - 5x - 2)/((x - 1)(1 - 6x + x^2)(1 + 6x + x^2))$ and
$6(1 + x)^2/((1 - x)(1 - 6x + x^2)(1 + 6x + x^2))$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 5
(`jis-2024-24.6.3-prop-5`). -/
public theorem_wanted nicomachean_run_repeat_generatingFunctions :
    let P : ℕ → Prop := fun j => 0 < j ∧ ∃ m : ℤ, 0 < m ∧
      nicomacheanNu ((List.range' 1 (j + 1)).map (fun i : ℕ => (i : ℤ)) ++
        List.replicate (2 * j) m) = 0
    let J : ℕ → ℕ := Nat.nth P
    let M : ℕ → ℕ := fun k => J k + Nat.sqrt (2 * J k ^ 2 + 3 * J k + 2)
    (∀ k, nicomacheanNu ((List.range' 1 (J k + 1)).map (fun i : ℕ => (i : ℤ)) ++
        List.replicate (2 * J k) (M k : ℤ)) = 0) ∧
      (X - 1) * (1 - 6 * X + X ^ 2) * (1 + 6 * X + X ^ 2) * PowerSeries.mk (fun k => (J k : ℤ)) =
        X ^ 4 + X ^ 3 - 19 * X ^ 2 - 5 * X - 2 ∧
      (1 - X) * (1 - 6 * X + X ^ 2) * (1 + 6 * X + X ^ 2) * PowerSeries.mk (fun k => (M k : ℤ)) =
        6 * (1 + X) ^ 2

/-- **Nicomachean sequences with a large gap at the top.** Write
$\nu(a_1, \dots, a_n) = (a_1 + \dots + a_n)^2 - (a_1^3 + \dots + a_n^3)$ for the Nicomachean defect
of a finite sequence. For every natural number $G$ there is a finite sequence $\sigma$ of
positive integers with $\nu(\sigma) = 0$ and entries $a < b$ of $\sigma$ such that $b$ is the
largest entry of $\sigma$ and occurs exactly once, every entry other than $b$ is at most $a$, and
$b - a > G$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 6
(`jis-2024-24.6.3-prop-6`). -/
public theorem_wanted exists_nicomachean_large_top_gap (G : ℕ) :
    ∃ σ : List ℤ, (∀ x ∈ σ, 0 < x) ∧ nicomacheanNu σ = 0 ∧ ∃ a ∈ σ, ∃ b ∈ σ,
      σ.count b = 1 ∧ (∀ x ∈ σ, x ≤ b) ∧ a < b ∧ (∀ x ∈ σ, x ≠ b → x ≤ a) ∧ (G : ℤ) < b - a

/-- **Golden-ratio sequences with vanishing Nicomachean defect.** Let $\varphi = (1 + \sqrt 5)/2$
be the golden ratio and write
$\nu(a_1, \dots, a_k) = (a_1 + \dots + a_k)^2 - (a_1^3 + \dots + a_k^3)$ for the Nicomachean defect
of a finite sequence of real numbers. For every natural number $N$ there is a finite sequence
$\sigma$ of positive real numbers, each of the form $p + q\varphi$ with $p, q \in \mathbb{Z}$, such
that $\nu(\sigma) = 0$, $\sigma$ contains $\varphi^{-n}$ for every $1 \le n \le N$, and $\sigma$ has
a subsequence of irrational entries whose length is more than half the length of $\sigma$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 7
(`jis-2024-24.6.3-prop-7`). -/
public theorem_wanted exists_goldenRatio_nicomachean_sequence (N : ℕ) :
    ∃ σ : List ℝ, (∀ x ∈ σ, 0 < x ∧ ∃ p q : ℤ, x = p + q * Real.goldenRatio) ∧
      (∃ τ : List ℝ, τ.Sublist σ ∧ σ.length < 2 * τ.length ∧ ∀ x ∈ τ, Irrational x) ∧
      nicomacheanNu σ = 0 ∧ ∀ n ∈ Finset.Icc 1 N, Real.goldenRatio⁻¹ ^ n ∈ σ

/-- **Adjoined Nicomachean sequences are eventually arithmetic progressions.** Write
$\nu(a_1, \dots, a_n) = (a_1 + \dots + a_n)^2 - (a_1^3 + \dots + a_n^3)$ for the Nicomachean defect
of a finite sequence. Let $(a_1, \dots, a_n)$ be a finite, possibly empty, sequence of real numbers
and let $x_1, x_2, x_3, \dots$ be nonzero real numbers with $x_{j+1} \ne -x_j$ for every $j \ge 1$.
If $\nu(a_1, \dots, a_n, x_1, \dots, x_l) = 0$ for every $l \ge 1$, then $x_{j+1} = x_j + 1$ for
every $j \ge 2$; that is, $x_2, x_3, \dots$ is an arithmetic progression with difference $1$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 8
(`jis-2024-24.6.3-prop-8`). -/
public theorem_wanted nicomachean_adjoined_arithmeticProgression (a : List ℝ) (x : ℕ → ℝ)
    (hx : ∀ j, x j ≠ 0) (hneg : ∀ j, x (j + 1) ≠ -x j)
    (hν : ∀ l, nicomacheanNu (a ++ (List.range (l + 1)).map x) = 0) :
    ∀ j, 1 ≤ j → x (j + 1) = x j + 1

/-- **Positive integer roots of the Nicomachean factor for $s = 1, 2$.** Let
$\alpha(n, s, a) = 2n^2 + na - a^2 + n(n-1)(s - s^2)/2 - (n-1)as$ and let $F_0 = 0$, $F_1 = 1$,
$F_{k+2} = F_{k+1} + F_k$ be the Fibonacci numbers. Let $n \ge 1$ be a natural number. Then
$\alpha(n, 1, h) = 0$ for some positive integer $h$ if and only if $2n^2 = k(k+1)$ for some natural
number $k$, that is, $n^2$ is a triangular number; $\alpha(n, 2, h) = 0$ for some positive integer
$h$ if and only if $n = F_{2k}$ for some $k \ge 1$; and if $n = F_{2k}$ with $k \ge 1$, then every
positive integer $h$ with $\alpha(n, 2, h) = 0$ equals $F_{2k-1} + 1$.

By the factor theorem, $\alpha(n, s, h) = 0$ says that $a - h$ divides $\alpha(n, s, a)$ as a
polynomial in $a$. The case $n = 0$ is excluded: $\alpha(0, 2, a)$ has the root $2$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 9
(`jis-2024-24.6.3-prop-9`). -/
public theorem_wanted nicomacheanAlpha_posIntRoot_iff {n : ℕ} (hn : 1 ≤ n) :
    ((∃ h : ℕ, 0 < h ∧ nicomacheanAlpha n 1 h = 0) ↔ ∃ k : ℕ, 2 * n ^ 2 = k * (k + 1)) ∧
      ((∃ h : ℕ, 0 < h ∧ nicomacheanAlpha n 2 h = 0) ↔ ∃ k : ℕ, 1 ≤ k ∧ n = Nat.fib (2 * k)) ∧
      ∀ k h : ℕ, 1 ≤ k → n = Nat.fib (2 * k) → 0 < h → nicomacheanAlpha n 2 h = 0 →
        h = Nat.fib (2 * k - 1) + 1

/-- **Nicomachean families sharing a quadratic factor.** Write
$\nu(a_1, \dots, a_n) = (a_1 + \dots + a_n)^2 - (a_1^3 + \dots + a_n^3)$ for the Nicomachean defect
of a finite sequence. For every natural number $N$ there are finite sequences
$\sigma_1, \dots, \sigma_N$ of positive integers, pairwise distinct as multisets, and an integer
$c$ such that for every $i$ we have $\nu(\sigma_i) = 0$ and, for all integers $a$ and $b$, the
sequence $(\sigma_i, a, b)$ obtained by appending $a$ and $b$ to $\sigma_i$ satisfies
$\nu(\sigma_i, a, b) = -(a + b)(a^2 - ab + b^2 - a - b - 2c)$.

Since $\nu(\sigma_i) = 0$, the identity forces $c$ to be the sum of the entries of every
$\sigma_i$. Positivity of the entries, the paper's setting, excludes trivial families such as
$(k, -k, 1)$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 12
(`jis-2024-24.6.3-prop-12`). -/
public theorem_wanted exists_nicomachean_family_same_quadratic_factor (N : ℕ) :
    ∃ σ : Fin N → List ℤ, Function.Injective (fun i => (σ i : Multiset ℤ)) ∧ ∃ c : ℤ, ∀ i,
      (∀ x ∈ σ i, 0 < x) ∧ nicomacheanNu (σ i) = 0 ∧
        ∀ a b : ℤ, nicomacheanNu (σ i ++ [a, b]) = -(a + b) * (a ^ 2 - a * b + b ^ 2 - a - b - 2 * c)

end

end MetaMathlibExt
