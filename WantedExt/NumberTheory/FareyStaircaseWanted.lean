/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Farey staircases

Statements from David Harry Richman, *Lower Rational Approximations and Farey Staircases*,
INTEGERS 24 (2024), Article A37 (primary text: arXiv:2303.02935).

The Farey staircase `A_n(x) = (1/n) Σ_{k=1}^n ⌊kx⌋/k` averages the lower rational approximations
`⌊kx⌋/k`; `B_n(x) = n A_n(x/n)` zooms in at the origin; `D_n = A_n - A_{n-1}`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.NumberTheory.FareyStaircase

namespace MetaMathlibExt

@[expose] public section

/-- **Limit of the Farey staircase zoomed at the origin.** Let $B_n$ be the zoomed Farey staircase
of order $n$. For every real $x \ge 0$, $B_n(x) \to \sum_{k=1}^{\lfloor x \rfloor} \log(x/k)$ as
$n \to \infty$.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Theorem 1 (`integers-2024-A37-thm-1`). -/
public theorem_wanted tendsto_fareyZoom {x : ℝ} (hx : 0 ≤ x) :
    Filter.Tendsto (fun n : ℕ => fareyZoom n x) Filter.atTop
      (nhds (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / k)))

/-- **Limit of the Farey staircase zoomed at a rational point.** Let $B_n$ be the zoomed Farey
staircase of order $n$, let $x \ge 0$ be real, and let $p$ and $q$ be coprime positive integers.
Then $B_n(x + pn/q) - B_n(pn/q) \to \frac{1}{q} \sum_{k=1}^{\lfloor qx \rfloor} \log(qx/k)$ as
$n \to \infty$.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Theorem 3 (`integers-2024-A37-thm-3`). -/
public theorem_wanted tendsto_fareyZoom_sub_at_rational {x : ℝ} (hx : 0 ≤ x) {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q) :
    Filter.Tendsto
      (fun n : ℕ => fareyZoom n (x + (p : ℝ) / q * n) - fareyZoom n ((p : ℝ) / q * n))
      Filter.atTop
      (nhds ((q : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 ⌊(q : ℝ) * x⌋₊, Real.log (q * x / k)))

/-- **Floor gaps of Farey staircases are dense above $1 - \log 2$.** For $n \ge 1$ and
$x \in \mathbb{R}$ let $f_n(x) = \lfloor nx \rfloor - n A_n(x)$, where $A_n$ is the Farey staircase
of order $n$; thus $f_n(x) = \lfloor nx \rfloor - \sum_{k=1}^n \lfloor kx \rfloor / k$. Every real
number $y \ge 1 - \log 2$ lies in the closure of the set
$S = \{f_n(x) : n \ge 1,\ x \in \mathbb{R}\}$, that is, $S$ is dense in $[1 - \log 2, \infty)$.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Theorem 5 (i) (`integers-2024-A37-thm-5`), also Corollary 6
(`integers-2024-A37-cor-6`). -/
public theorem_wanted Ici_one_sub_log_two_subset_closure_floor_gaps :
    Set.Ici (1 - Real.log 2) ⊆
      closure {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ ∃ x : ℝ, y = ⌊(n : ℝ) * x⌋ - n * fareyStaircase n x}

/-- **Finiteness of small floor gaps of the Farey staircase.** For a natural number $n \ge 1$ and a
real number $x$, let $f_n(x) = \lfloor nx \rfloor - n A_n(x)$, where $A_n$ is the Farey staircase
of order $n$. Then for every real number $\varepsilon > 0$, only finitely many distinct real
numbers that are at most $1 - \log 2 - \varepsilon$ occur as a value $f_n(x)$ with $n \ge 1$ and
$x$ real; here $\log$ is the natural logarithm.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Theorem 5 (ii) (`integers-2024-A37-thm-5`). -/
public theorem_wanted floor_gaps_inter_Iic_finite {ε : ℝ} (hε : 0 < ε) :
    ({y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ ∃ x : ℝ, y = ⌊(n : ℝ) * x⌋ - n * fareyStaircase n x} ∩
      Set.Iic (1 - Real.log 2 - ε)).Finite

/-- **Bounds comparing the Farey staircase with $\lfloor nx \rfloor / n$.** For every natural
number $n \ge 1$ and every real number $x$, the Farey staircase $A_n$ of order $n$ satisfies
$A_n(x) \le \lfloor nx \rfloor / n \le A_n(x) + (\log n)/n$, where $\log$ is the natural
logarithm.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Lemma 8 (a) (`integers-2024-A37-lem-8`). -/
public theorem_wanted fareyStaircase_le_floor_div {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    fareyStaircase n x ≤ ⌊(n : ℝ) * x⌋ / n ∧
      (⌊(n : ℝ) * x⌋ : ℝ) / n ≤ fareyStaircase n x + Real.log n / n

/-- **Bounds on the increment of the Farey staircase.** Let $n \ge 2$ be a natural number and $x$
a real number, and write $A_m$ for the Farey staircase of order $m$. Then
$0 \le A_n(x) - A_{n-1}(x) \le \frac{\log n}{n(n-1)}$, where $\log$ is the natural logarithm.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Lemma 8 (b) (`integers-2024-A37-lem-8`). -/
public theorem_wanted fareyStaircase_sub_mem_Icc {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    0 ≤ fareyStaircase n x - fareyStaircase (n - 1) x ∧
      fareyStaircase n x - fareyStaircase (n - 1) x ≤ Real.log n / (n * (n - 1))

end

end MetaMathlibExt
