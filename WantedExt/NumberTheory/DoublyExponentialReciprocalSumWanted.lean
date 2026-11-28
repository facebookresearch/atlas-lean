/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Data.Int.ModEq
public import MathlibExt.NumberTheory.DoublyExponentialReciprocalSum
public import MathlibExt.NumberTheory.GeneralizedSylvester
public import MathlibExt.NumberTheory.MillinSeries
public import MathlibExt.NumberTheory.DoublyExponentialReciprocalSumExistsTailEqPseudoGreedyExpansion
public import MathlibExt.NumberTheory.DoublyExponentialReciprocalSumEventuallyPseudoGreedyGapEqZero
public import MathlibExt.NumberTheory.DoublyExponentialReciprocalSumSylvester
public import MathlibExt.NumberTheory.DoublyExponentialReciprocalSumEqRoundInvRemainderAdd
public import MathlibExt.NumberTheory.DoublyExponentialReciprocalSumConjectureEquivalence

/-!
# Reciprocal sums of doubly exponential sequences

Statements from Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly
Exponential Sequences*, INTEGERS 26 (2026), Article A28 (arXiv:2504.05933). Sequences are
indexed from `0` (the paper's `a₁` is `a 0`), the nearest-integer function
`⌊x⌉ = ⌊x + 1/2⌋` is written out, and "for `n ≫ 0`" is `∀ᶠ n in atTop`. The Sylvester
sequence is `Nat.generalizedSylvester 1` (`2, 3, 7, 43, …`), and the paper's `F_(2^n)` is
`Nat.fib (2 ^ (n + 1))` after the index shift.
-/

open Filter Topology

namespace MetaMathlibExt

@[expose] public section

/-- **Doubly exponential floors are Type 2 irrationality sequences for all but countably many
bases.** For all real numbers $\alpha > 1$ outside a countable set, the sequence
$(\lfloor \alpha^{2^{n+1}} \rfloor)_{n \ge 0}$ is a Type 2 irrationality sequence: for every
sequence $(b_n)_{n \ge 0}$ of positive integers with $b_n / \lfloor \alpha^{2^{n+1}} \rfloor \to 1$,
the series $\sum_n 1 / b_n$ does not converge to a rational number.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Theorem 2 and the definition of Type 2
irrationality sequences preceding it (`integers-2026-A28-thm-2`). -/
public theorem_wanted countable_not_type2IrrationalitySequence_floor_pow_two_pow :
    Set.Countable {α : ℝ | 1 < α ∧ ¬∀ b : ℕ → ℕ, (∀ n, 0 < b n) →
      Tendsto (fun n => (b n : ℝ) / ⌊α ^ 2 ^ (n + 1)⌋₊) atTop (𝓝 1) →
        ∀ q : ℚ, ¬HasSum (fun n => 1 / (b n : ℝ)) q}

/-- **Structure of the pseudo-greedy expansion of a rational.** Let $p$ and $q$ be positive
integers, let $r = p/q$, and let $(x_n)$, $(a_n)$ and $(\varepsilon_n)$ be the remainder
sequence, the pseudo-greedy expansion and the gap sequence of $r$. Put
$d_n = q a_0 a_1 \cdots a_{n-1}$ (so $d_0 = q$). Then there are positive integers $c_n$ and
integers $e_n$ ($n \ge 0$) such that for every $n$ we have $x_n = c_n / d_n$,
$\varepsilon_n = e_n / c_n$, $e_n \equiv d_n \pmod{c_n}$, $-c_n/2 \le e_n < c_n/2$,
$a_n = (d_n - e_n)/c_n + 1$, $c_{n+1} = c_n - e_n$ and $d_{n+1} = d_n a_n$. Moreover, as
$n \to \infty$, $c_n = O(a_0 \cdots a_{n-1} / a_n)$ and $c_n = O(1.5^n)$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Lemma 4 (`integers-2026-A28-lem-4`). -/
public theorem_wanted pseudoGreedyExpansion_rational_structure {p q : ℕ} (hp : 0 < p)
    (hq : 0 < q) :
    let r : ℝ := p / q
    let a : ℕ → ℤ := pseudoGreedyExpansion r
    let d : ℕ → ℤ := fun n => q * ∏ k ∈ Finset.range n, a k
    ∃ (c : ℕ → ℕ) (e : ℕ → ℤ),
      (∀ n, 0 < c n ∧ pseudoGreedyRemainder r n = (c n : ℝ) / d n ∧
        pseudoGreedyGap r n = (e n : ℝ) / c n) ∧
      (∀ n, e n ≡ d n [ZMOD c n] ∧ -(c n : ℝ) / 2 ≤ e n ∧ (e n : ℝ) < c n / 2 ∧
        (a n : ℝ) = (d n - e n : ℝ) / c n + 1 ∧ (c (n + 1) : ℤ) = c n - e n ∧
        d (n + 1) = d n * a n) ∧
      (fun n => (c n : ℝ)) =O[atTop] (fun n => (∏ k ∈ Finset.range n, (a k : ℝ)) / a n) ∧
      (fun n => (c n : ℝ)) =O[atTop] (fun n => (1.5 : ℝ) ^ n)

/-- **Erdős–Straus and Badea criterion for the Sylvester recurrence.** Let $(a_n)_{n \ge 0}$ be a
sequence of positive integers with $a_n^2 / a_{n+1} \to 1$ such that $\sum_n 1 / a_n$ converges
to a rational number. Suppose that
$\liminf_n (a_0 \cdots a_{n-1} / a_n)(1 - a_n^2 / a_{n+1}) \ge 0$, that is, for every
$\delta > 0$ this quantity is at least $-\delta$ for all sufficiently large $n$; or that
$a_{n+1} \ge a_n^2 - a_n + 1$ for all sufficiently large $n$. Then
$a_{n+1} = a_n^2 - a_n + 1$ for all sufficiently large $n$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Corollary 4 (`integers-2026-A28-cor-4`). -/
public theorem_wanted eventually_sylvester_recurrence_of_rational_sum {a : ℕ → ℕ}
    (hpos : ∀ n, 0 < a n)
    (hratio : Tendsto (fun n => (a n : ℝ) ^ 2 / a (n + 1)) atTop (𝓝 1))
    (hrat : ∃ q : ℚ, HasSum (fun n => 1 / (a n : ℝ)) q)
    (h : (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
        -δ ≤ (∏ k ∈ Finset.range n, (a k : ℝ)) / a n * (1 - (a n : ℝ) ^ 2 / a (n + 1))) ∨
      ∀ᶠ n in atTop, a n ^ 2 - a n + 1 ≤ a (n + 1)) :
    ∀ᶠ n in atTop, a (n + 1) = a n ^ 2 - a n + 1

end

end MetaMathlibExt
