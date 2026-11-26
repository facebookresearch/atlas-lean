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
public import MathlibExt.NumberTheory.NicomacheanAdjoinedProgression
public import MathlibExt.NumberTheory.NicomacheanLargeTopGap
public import MathlibExt.NumberTheory.NicomacheanTranslations
public import MathlibExt.NumberTheory.NicomacheanTranslationsExistsGoldenRatioNicomacheanSequence

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
        ∀ a b : ℤ, nicomacheanNu (σ i ++ [a, b]) =
          -(a + b) * (a ^ 2 - a * b + b ^ 2 - a - b - 2 * c)

end

end MetaMathlibExt
