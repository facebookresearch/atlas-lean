/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Complexity of natural numbers

Statements from Juan Arias de Reyna, "Complexity of
Natural Numbers", *INTEGERS* 24 (2024), Article A19
(<https://math.colgate.edu/~integers/y19/y19.pdf>).

The paper's complexity `‖n‖` (extracted as `knk`) is
MathlibExt's `IntegerComplexity.complexity`; `cx n`
is that function at `⟨n, ·⟩` for positive `n` and `0` at
`0`, so divisor and split statements can be phrased over
`ℕ`. The lower-bound function `g` of Corollary 2 is
`complexityLowerBoundG`: with `a` such that
`3^a ≤ n < 3^(a+1)`, it is `3a` on `[3^a, 3^a + 3^(a-1))`,
`3a + 1` on `[3^a + 3^(a-1), 2 * 3^a)`, and `3a + 2` on
`[2 * 3^a, 3^(a+1))` (the first threshold is written
`3 * (n - 3^a) < 3^a` to stay in `ℕ` at `a = 0`).
The executable statements (Proposition 1, Corollary 1,
and all three parts of Corollary 2) were verified against
DP-computed complexities for `n ≤ 2000`; Proposition 2 is
quantified over all majorants `P` and was only
sanity-checked through its Corollary 1 instance
`P n = log₂ (1 + n)`. The upper bound `L(n)` of
Definition 1 (`L(1) = 1`, `L(p) = 1 + L(p - 1)` for primes
`p`, `L(p₁ ⋯ p_k) = L(p₁) + ⋯ + L(p_k)`) enters Propositions 3
and 4 and Corollary 3 through these three defining equations,
which determine `L` on positive integers. Proposition 5 is
stated for MathlibExt's expressions `IntegerComplexity.Expr`
through the value of `Mₙ`: `3^k`, `4 * 3^(k-1)`, `2 * 3^k` for
`n = 3k, 3k + 1, 3k + 2`. These statements were checked
against the journal text and against DP-computed values
(`‖n‖` for `n ≤ 5000`, `L(n)` for `n ≤ 100000`, maximal
expression values for `n < 60`).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import MathlibExt.NumberTheory.IntegerComplexityRecurrence

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.IntegerComplexityWanted

/-- **A criterion for lower bounds on integer complexity.** Write $\lVert n \rVert$ for the
integer complexity of a positive integer $n$, the least number of ones needed to write $n$ using
$1$, $+$, $\times$ and parentheses. Let $P$ be a real-valued function on the natural numbers with
$P(1) = 1$ such that $P(n + m) \le P(n) + P(m)$ and $P(nm) \le P(n) + P(m)$ for all positive
integers $n$ and $m$. Then $P(n) \le \lVert n \rVert$ for every positive integer $n$.

Source: Juan Arias de Reyna, "Complexity of Natural
Numbers", Proposition 2. -/
theorem_wanted le_complexity_of_subadditive (P : ℕ → ℝ)
    (h1 : P 1 = 1)
    (hadd : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → P (n + m) ≤ P n + P m)
    (hmul : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → P (n * m) ≤ P n + P m)
    (n : ℕ) (hn : 1 ≤ n) :
    P n ≤ (cx n : ℝ)

/-- **Logarithmic lower bound for integer complexity.** Write $\lVert n \rVert$ for the integer
complexity of a positive integer $n$, the least number of ones needed to write $n$ using $1$, $+$,
$\times$ and parentheses. For every positive integer $n$, $\log_2(1 + n) \le \lVert n \rVert$.

Source: Juan Arias de Reyna, "Complexity of Natural
Numbers", Corollary 1. -/
theorem_wanted logb_two_add_one_le (n : ℕ) (hn : 1 ≤ n) :
    Real.logb 2 (1 + n) ≤ (cx n : ℝ)

/-- **Integer complexity of $2^a 3^b$ for $a \le 2$.** Write $\lVert n \rVert$ for the integer
complexity of a positive integer $n$, the least number of ones needed to write $n$ using $1$, $+$,
$\times$ and parentheses. For all natural numbers $a \le 2$ and $b$, not both zero,
$\lVert 2^a 3^b \rVert = 2a + 3b$.

Source: Juan Arias de Reyna, "Complexity of Natural
Numbers", Corollary 2. -/
theorem_wanted complexity_two_pow_mul_three_pow (a b : ℕ)
    (ha : a ≤ 2) (hab : 1 ≤ 2 * a + 3 * b) :
    cx (2 ^ a * 3 ^ b) = 2 * a + 3 * b

/-- **Proposition 3**: `‖n‖ ≤ L(n)` for every positive `n`,
where `L` is the function of Definition 1, given by its
defining equations `L(1) = 1`, `L(p) = 1 + L(p - 1)` for
primes `p`, and `L(p₁ ⋯ p_k) = L(p₁) + ⋯ + L(p_k)` for
products of `k ≥ 2` primes.

Source: Juan Arias de Reyna, *Complexity of Natural
Numbers*, INTEGERS 24 (2024), Article A19, Definition 1 and
Proposition 3 (`integers-2024-A19-prop-3`). -/
theorem_wanted complexity_le_lengthL (L : ℕ → ℕ) (hL1 : L 1 = 1)
    (hLp : ∀ p : ℕ, p.Prime → L p = 1 + L (p - 1))
    (hLprod : ∀ l : List ℕ, (∀ p ∈ l, p.Prime) → 2 ≤ l.length →
      L l.prod = (l.map L).sum)
    (n : ℕ) (hn : 1 ≤ n) :
    cx n ≤ L n

/-- **Proposition 4**: `L(n) ≤ (3 / log 2) log n` for every
`n ≥ 2`, with `L` given by the defining equations of
Definition 1.

Source: Juan Arias de Reyna, *Complexity of Natural
Numbers*, INTEGERS 24 (2024), Article A19, Definition 1 and
Proposition 4 (`integers-2024-A19-prop-4`). -/
theorem_wanted lengthL_le_three_div_log_two_mul_log (L : ℕ → ℕ)
    (hL1 : L 1 = 1) (hLp : ∀ p : ℕ, p.Prime → L p = 1 + L (p - 1))
    (hLprod : ∀ l : List ℕ, (∀ p ∈ l, p.Prime) → 2 ≤ l.length →
      L l.prod = (l.map L).sum)
    (n : ℕ) (hn : 2 ≤ n) :
    (L n : ℝ) ≤ 3 / Real.log 2 * Real.log n

/-- **Corollary 3**: for every `n ≥ 2`,
`3 log n / log 3 ≤ ‖n‖ ≤ L(n) ≤ 3 log n / log 2`, with `L`
given by the defining equations of Definition 1.

Source: Juan Arias de Reyna, *Complexity of Natural
Numbers*, INTEGERS 24 (2024), Article A19, Corollary 3
(`integers-2024-A19-cor-3`). -/
theorem_wanted three_logb_three_le_complexity_le_lengthL (L : ℕ → ℕ)
    (hL1 : L 1 = 1) (hLp : ∀ p : ℕ, p.Prime → L p = 1 + L (p - 1))
    (hLprod : ∀ l : List ℕ, (∀ p ∈ l, p.Prime) → 2 ≤ l.length →
      L l.prod = (l.map L).sum)
    (n : ℕ) (hn : 2 ≤ n) :
    3 * Real.log n / Real.log 3 ≤ (cx n : ℝ) ∧ cx n ≤ L n ∧
      (L n : ℝ) ≤ 3 * Real.log n / Real.log 2

/-- **Proposition 5**: for `n > 1` the expressions
`Mₙ = M₃^k`, `M₃^(k-1) M₄`, `M₃^k M₂` (`n = 3k, 3k + 1, 3k + 2`)
are extremal: their value `3^k`, `4 * 3^(k-1)`, `2 * 3^k` is
the largest value of an expression with `n` ones.

Source: Juan Arias de Reyna, *Complexity of Natural
Numbers*, INTEGERS 24 (2024), Article A19, Proposition 5
(`integers-2024-A19-prop-5`). -/
theorem_wanted isGreatest_eval_of_count (n : ℕ) (hn : 2 ≤ n) :
    IsGreatest {v | ∃ e : IntegerComplexity.Expr, e.count = n ∧ e.eval = v}
      (if n % 3 = 0 then 3 ^ (n / 3)
        else if n % 3 = 1 then 4 * 3 ^ (n / 3 - 1) else 2 * 3 ^ (n / 3))

end MathlibExt.NumberTheory.IntegerComplexityWanted
