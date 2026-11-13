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
MathlibExt's `IntegerComplexity.complexity`; `cx n` below
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
`P n = log₂ (1 + n)`. The paper's `L(n)`-based
results (Corollary 3, Propositions 3, 4, 5) are not stated:
the recursive definition of `L` and of the extremal
expressions `Mₙ` is not recoverable from the extracted
statements (see the source audit table).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import MathlibExt.NumberTheory.IntegerComplexity

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.IntegerComplexityWanted

/-- **Integer complexity extended to all natural numbers.** For a natural number $n$, the value
$\lVert n \rVert$ is the integer complexity of $n$ when $n$ is positive, that is, the least number
of ones needed to write $n$ using $1$, $+$, $\times$ and parentheses, and $\lVert 0 \rVert = 0$. -/
noncomputable def cx (n : ℕ) : ℕ :=
  if h : 0 < n then IntegerComplexity.complexity ⟨n, h⟩ else 0

/-- **Lower-bound function for integer complexity.** For a natural number $n$, let $a$ be the
largest natural number with $3^a \le n$ when $n \ge 1$, and let $a = 0$ when $n = 0$. The function
$g$ on the natural numbers is given by $g(n) = 3a$ if $n < \frac{4}{3} \cdot 3^a$,
$g(n) = 3a + 1$ if $\frac{4}{3} \cdot 3^a \le n < 2 \cdot 3^a$, and $g(n) = 3a + 2$ if
$n \ge 2 \cdot 3^a$. -/
def complexityLowerBoundG (n : ℕ) : ℕ :=
  let a := Nat.log 3 n
  if 3 * (n - 3 ^ a) < 3 ^ a then 3 * a
  else if n < 2 * 3 ^ a then 3 * a + 1
  else 3 * a + 2

/-- **Integer complexity as a minimum over factorizations and sums.** Write
$\lVert m \rVert$ for the integer complexity of a positive integer $m$, the least number of ones
needed to write $m$ using $1$, $+$, $\times$ and parentheses. For every integer $n \ge 2$,
$\lVert n \rVert$ is the least element of the set consisting of the numbers
$\lVert d \rVert + \lVert n/d \rVert$ for the divisors $d \ge 2$ of $n$ and the numbers
$\lVert j \rVert + \lVert n - j \rVert$ for the integers $j$ with $1 \le j \le n/2$.

Source: Juan Arias de Reyna, "Complexity of Natural
Numbers", Proposition 1. -/
theorem_wanted complexity_eq_min (n : ℕ) (hn : 2 ≤ n) :
    IsLeast {k | (∃ d : ℕ, 2 ≤ d ∧ d ∣ n ∧
        k = cx d + cx (n / d)) ∨
      (∃ j : ℕ, 1 ≤ j ∧ j ≤ n / 2 ∧ k = cx j + cx (n - j))}
      (cx n)

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

/-- **Integers above $2^a 3^b$ have complexity above $2a + 3b$ when $a \le 2$ and $2a + 3b \ge 2$.**
Write $\lVert m \rVert$ for the integer complexity of a positive integer $m$, the least number
of ones needed to write $m$ using $1$, $+$, $\times$ and parentheses. Let $a \le 2$ and $b$ be
natural numbers with $2a + 3b \ge 2$. Then every natural number $m > 2^a 3^b$ satisfies
$\lVert m \rVert > 2a + 3b$.

Source: Juan Arias de Reyna, "Complexity of Natural
Numbers", Corollary 2. -/
theorem_wanted complexity_lt_of_gt_extremal (a b m : ℕ)
    (ha : a ≤ 2) (hab : 2 ≤ 2 * a + 3 * b)
    (hm : 2 ^ a * 3 ^ b < m) :
    2 * a + 3 * b < cx m

/-- **The function $g$ bounds integer complexity from below.** Write $\lVert n \rVert$ for the
integer complexity of a positive integer $n$, the least number of ones needed to write $n$ using
$1$, $+$, $\times$ and parentheses. For a positive integer $n$, let $a$ be the largest natural
number with $3^a \le n$, and let $g(n) = 3a$ if $n < \frac{4}{3} \cdot 3^a$, $g(n) = 3a + 1$ if
$\frac{4}{3} \cdot 3^a \le n < 2 \cdot 3^a$, and $g(n) = 3a + 2$ if $n \ge 2 \cdot 3^a$. Then
$g(n) \le \lVert n \rVert$ for every positive integer $n$.

Source: Juan Arias de Reyna, "Complexity of Natural
Numbers", Corollary 2. -/
theorem_wanted complexityLowerBoundG_le (n : ℕ) (hn : 1 ≤ n) :
    complexityLowerBoundG n ≤ cx n

end MathlibExt.NumberTheory.IntegerComplexityWanted
