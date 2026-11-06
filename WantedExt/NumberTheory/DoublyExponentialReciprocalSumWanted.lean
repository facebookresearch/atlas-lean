/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.NumberTheory.GeneralizedSylvester

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

/-- **Pseudo-greedy remainder sequence.** For a real number $r$, the remainder sequence
$(x_n)_{n \ge 0}$ of the pseudo-greedy expansion of $r$ is defined by $x_0 = r$ and
$x_{n+1} = x_n - 1/a_n$, where $a_n = \lfloor x_n^{-1} + 1 + 1/2 \rfloor$ is the integer
nearest to $x_n^{-1} + 1$, with halves rounded up.

Here $0^{-1}$ and $1/0$ are read as $0$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Section 2 (definitions of the pseudo-greedy
expansion and its remainder sequence). -/
noncomputable def pseudoGreedyRemainder (r : ℝ) : ℕ → ℝ
  | 0 => r
  | n + 1 => pseudoGreedyRemainder r n -
      1 / (⌊(pseudoGreedyRemainder r n)⁻¹ + 1 + 1 / 2⌋ : ℝ)

/-- **Pseudo-greedy expansion.** Let $r$ be a real number with pseudo-greedy remainder sequence
$(x_n)_{n \ge 0}$. The pseudo-greedy expansion of $r$ is the integer sequence
$a_n = \lfloor x_n^{-1} + 1 + 1/2 \rfloor$ for $n \ge 0$; that is, $a_n$ is the integer nearest
to $x_n^{-1} + 1$, with halves rounded up.

Here $0^{-1}$ is read as $0$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Section 2 (definition of the pseudo-greedy
expansion). -/
noncomputable def pseudoGreedyExpansion (r : ℝ) (n : ℕ) : ℤ :=
  ⌊(pseudoGreedyRemainder r n)⁻¹ + 1 + 1 / 2⌋

/-- **Gap sequence of the pseudo-greedy expansion.** Let $r$ be a real number, and let $(x_n)$
be the remainder sequence and $(a_n)$ the pseudo-greedy expansion of $r$. The gap sequence of
$r$ is the real sequence $\varepsilon_n = x_n^{-1} + 1 - a_n$ for $n \ge 0$.

Here $0^{-1}$ is read as $0$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Section 2 (definition of the gap sequence). -/
noncomputable def pseudoGreedyGap (r : ℝ) (n : ℕ) : ℝ :=
  (pseudoGreedyRemainder r n)⁻¹ + 1 - pseudoGreedyExpansion r n

/-- **Remainder recursion.** For every real number $r$ and every $n \ge 0$, the remainder
sequence $(x_n)$ and the pseudo-greedy expansion $(a_n)$ of $r$ satisfy $x_{n+1} = x_n - 1/a_n$.

Here $1/0$ is read as $0$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Section 2 (definition of the remainder
sequence). -/
theorem pseudoGreedyRemainder_succ (r : ℝ) (n : ℕ) :
    pseudoGreedyRemainder r (n + 1) =
      pseudoGreedyRemainder r n - 1 / (pseudoGreedyExpansion r n : ℝ) := rfl

/-- **The pseudo-greedy expansion of 1 starts with 2.** The first term $a_0$ of the
pseudo-greedy expansion of $1$ equals $2$, the first Sylvester number.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Example 1 (the expansion of `1` is the Sylvester
sequence). -/
theorem pseudoGreedyExpansion_one_zero : pseudoGreedyExpansion 1 0 = 2 := by
  rw [pseudoGreedyExpansion, pseudoGreedyRemainder, Int.floor_eq_iff]
  norm_num

/-- **Second term of the pseudo-greedy expansion of $1$.** The pseudo-greedy expansion
$(a_n)_{n \ge 0}$ of $1$ satisfies $a_1 = 3$.

The remainder after the first term $a_0 = 2$ is $1 - 1/2 = 1/2$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Example 1 (the expansion of `1` is the Sylvester
sequence). -/
theorem pseudoGreedyExpansion_one_one : pseudoGreedyExpansion 1 1 = 3 := by
  have h : pseudoGreedyRemainder 1 1 = 1 / 2 := by
    rw [pseudoGreedyRemainder_succ, pseudoGreedyExpansion_one_zero]
    simp only [pseudoGreedyRemainder]
    norm_num
  rw [pseudoGreedyExpansion, h, Int.floor_eq_iff]
  norm_num

/-- **The first gap of the expansion of 1 vanishes.** The first term $\varepsilon_0$ of the gap
sequence of the pseudo-greedy expansion of $1$ is $0$: the first remainder is $x_0 = 1$ and the
first term of the expansion is $a_0 = 2$, so $\varepsilon_0 = x_0^{-1} + 1 - a_0 = 1 + 1 - 2 = 0$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Example 1 (`ε_n = 0` for the expansion of `1`). -/
theorem pseudoGreedyGap_one_zero : pseudoGreedyGap 1 0 = 0 := by
  rw [pseudoGreedyGap, pseudoGreedyExpansion_one_zero]
  simp only [pseudoGreedyRemainder]
  norm_num

/-- **Recovering a doubly exponential sequence from its reciprocal sum.** Let $\beta \ge 0$ and
$r$ be real numbers, and let $(a_n)_{n \ge 0}$ be a sequence of positive integers with
$|a_n^2 / a_{n+1} - \beta| \le 1/3$ for all $n$ and $\sum_n 1 / a_n = r$. Write
$x_n = r - \sum_{k<n} 1 / a_k$. Then for every $n$ with $a_n \ge 8 (\beta + 1/3)^2$ we have
$a_n = \lfloor x_n^{-1} + \beta + 1/2 \rfloor$, that is, $a_n$ is the integer nearest to
$x_n^{-1} + \beta$, with halves rounded up. Moreover, if $a_n^2 / a_{n+1} \to \beta$, then
$|x_n^{-1} + \beta - a_n| \to 0$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Theorem 1 (`integers-2026-A28-thm-1`). -/
public theorem_wanted eq_round_inv_remainder_add {β r : ℝ} (hβ : 0 ≤ β) {a : ℕ → ℕ}
    (hpos : ∀ n, 0 < a n) (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r) :
    (∀ n, 8 * (β + 1 / 3) ^ 2 ≤ (a n : ℝ) →
      (a n : ℤ) = ⌊(r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ + β + 1 / 2⌋) ∧
    (Tendsto (fun n => (a n : ℝ) ^ 2 / a (n + 1)) atTop (𝓝 β) →
      Tendsto (fun n => |(r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ + β - a n|) atTop (𝓝 0))

/-- **Characterization of the Sylvester sequence.** Let $(a_n)_{n \ge 0}$ be a sequence of
positive integers with $2/3 \le a_n^2 / a_{n+1} \le 4/3$ for all $n$ and $\sum_n 1 / a_n = 1$.
Then $a_n = s_n(1)$ for all $n \ge 0$, where $(s_n(1))_{n \ge 0}$ is the generalized Sylvester
sequence with parameter $1$, that is, the Sylvester sequence $2, 3, 7, 43, \ldots$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Corollary 1 (`integers-2026-A28-cor-1`). -/
public theorem_wanted eq_sylvester_of_ratio_mem_of_hasSum_one {a : ℕ → ℕ}
    (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, 2 / 3 ≤ (a n : ℝ) ^ 2 / a (n + 1) ∧ (a n : ℝ) ^ 2 / a (n + 1) ≤ 4 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) 1) :
    ∀ n, a n = Nat.generalizedSylvester 1 n

/-- **Characterization of the denominators of the Millin series.** Let $(a_n)_{n \ge 0}$ be a
sequence of positive integers with $a_n^2 / a_{n+1} \le 2/3$ for all $n$ and
$\sum_n 1 / a_n = (5 - \sqrt 5) / 2$. Then $a_n = F_{2^{n+1}}$ for all $n \ge 0$, where $F_k$
is the $k$-th Fibonacci number ($F_0 = 0$, $F_1 = 1$); that is, $a$ is the sequence
$F_2, F_4, F_8, \ldots$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Corollary 2 (`integers-2026-A28-cor-2`). -/
public theorem_wanted eq_fib_two_pow_of_ratio_le_of_hasSum_millin {a : ℕ → ℕ}
    (hpos : ∀ n, 0 < a n) (hratio : ∀ n, (a n : ℝ) ^ 2 / a (n + 1) ≤ 2 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) ((5 - √5) / 2)) :
    ∀ n, a n = Nat.fib (2 ^ (n + 1))

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

/-- **Convergence of the pseudo-greedy expansion.** For every real number $r > 0$, the
pseudo-greedy expansion $(a_n)_{n \ge 0}$ of $r$ satisfies $\sum_n 1 / a_n = r$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Lemma 1 (`integers-2026-A28-lem-1`). -/
public theorem_wanted hasSum_one_div_pseudoGreedyExpansion {r : ℝ} (hr : 0 < r) :
    HasSum (fun n => 1 / (pseudoGreedyExpansion r n : ℝ)) r

/-- **Recursion for the pseudo-greedy expansion.** Let $r > 0$ be a real number, and let
$(a_n)$ be its pseudo-greedy expansion and $(\varepsilon_n)$ its gap sequence. Then for every
$n \ge 0$,
$$a_{n+1} = \frac{a_n^2}{1 - \varepsilon_n} - a_n + (1 - \varepsilon_{n+1}).$$

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Lemma 2 (`integers-2026-A28-lem-2`). -/
public theorem_wanted pseudoGreedyExpansion_succ_eq {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (pseudoGreedyExpansion r (n + 1) : ℝ) =
      1 / (1 - pseudoGreedyGap r n) * (pseudoGreedyExpansion r n : ℝ) ^ 2 -
        pseudoGreedyExpansion r n + (1 - pseudoGreedyGap r (n + 1))

/-- **A vanishing gap stays zero.** Let $r > 0$ be a real number and let $(\varepsilon_n)$ be
the gap sequence of its pseudo-greedy expansion. For every $n \ge 0$, if $\varepsilon_n = 0$,
then $\varepsilon_{n+1} = 0$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Lemma 3 (`integers-2026-A28-lem-3`). -/
public theorem_wanted pseudoGreedyGap_succ_eq_zero {r : ℝ} (hr : 0 < r) {n : ℕ}
    (h : pseudoGreedyGap r n = 0) : pseudoGreedyGap r (n + 1) = 0

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

/-- **Eventual vanishing of the pseudo-greedy gaps of a rational number.** Let $r$ be a positive
rational number and let $(\varepsilon_n)_{n \ge 0}$ be the gap sequence of the pseudo-greedy
expansion of $r$. Suppose that $\liminf_n \varepsilon_n \prod_{k<n} (1 - \varepsilon_k) \ge 0$,
that is, for every $\delta > 0$ we have $\varepsilon_n \prod_{k<n} (1 - \varepsilon_k) \ge -\delta$
for all sufficiently large $n$; or that $\varepsilon_n \ge 0$ for all sufficiently large $n$.
Then $\varepsilon_n = 0$ for all sufficiently large $n$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Proposition 1 (`integers-2026-A28-prop-1`). -/
public theorem_wanted eventually_pseudoGreedyGap_eq_zero {r : ℚ} (hr : 0 < r)
    (h : (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
        -δ ≤ pseudoGreedyGap r n * ∏ k ∈ Finset.range n, (1 - pseudoGreedyGap r k)) ∨
      ∀ᶠ n in atTop, 0 ≤ pseudoGreedyGap r n) :
    ∀ᶠ n in atTop, pseudoGreedyGap r n = 0

/-- **Tails that are pseudo-greedy expansions.** Let $(a_n)_{n \ge 0}$ be a sequence of positive
integers with $a_n^2 / a_{n+1} \to 1$ such that $\sum_n 1 / a_n$ converges. Then there is a
natural number $N$ such that, with $r = \sum_{k \ge 0} 1 / a_{N+k}$, the tail
$(a_{N+n})_{n \ge 0}$ is the pseudo-greedy expansion of $r$, and the gap sequence of this
expansion tends to $0$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Corollary 3 (`integers-2026-A28-cor-3`). -/
public theorem_wanted exists_tail_eq_pseudoGreedyExpansion {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n)
    (hratio : Tendsto (fun n => (a n : ℝ) ^ 2 / a (n + 1)) atTop (𝓝 1))
    (hsum : Summable fun n => 1 / (a n : ℝ)) :
    ∃ N : ℕ,
      (∀ n, (a (N + n) : ℤ) = pseudoGreedyExpansion (∑' k, 1 / (a (N + k) : ℝ)) n) ∧
      Tendsto (pseudoGreedyGap (∑' k, 1 / (a (N + k) : ℝ))) atTop (𝓝 0)

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

/-- **Koizumi's conjecture is equivalent to the Erdős–Graham question.** The following are
equivalent. (1) For every positive rational number $r$ whose pseudo-greedy gap sequence
$(\varepsilon_n)_{n \ge 0}$ tends to $0$, we have $\varepsilon_n = 0$ for all sufficiently large
$n$. (2) Every sequence $(a_n)_{n \ge 0}$ of positive integers with $a_n^2 / a_{n+1} \to 1$ such
that $\sum_n 1 / a_n$ converges to a rational number satisfies $a_{n+1} = a_n^2 - a_n + 1$ for
all sufficiently large $n$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Theorem 3, with Conjecture 1 and Question 1
(`integers-2026-A28-thm-3`). -/
public theorem_wanted pseudoGreedy_conjecture_iff_erdos_graham_question :
    (∀ r : ℚ, 0 < r → Tendsto (pseudoGreedyGap r) atTop (𝓝 0) →
        ∀ᶠ n in atTop, pseudoGreedyGap r n = 0) ↔
      ∀ a : ℕ → ℕ, (∀ n, 0 < a n) →
        Tendsto (fun n => (a n : ℝ) ^ 2 / a (n + 1)) atTop (𝓝 1) →
        (∃ q : ℚ, HasSum (fun n => 1 / (a n : ℝ)) q) →
        ∀ᶠ n in atTop, a (n + 1) = a n ^ 2 - a n + 1

end

end MetaMathlibExt
