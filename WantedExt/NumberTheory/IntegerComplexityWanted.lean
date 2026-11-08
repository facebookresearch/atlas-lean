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

/-- Integer complexity `‖n‖` phrased over `ℕ`:
`IntegerComplexity.complexity ⟨n, ·⟩` for positive `n`,
and `0` at `n = 0`. -/
noncomputable def cx (n : ℕ) : ℕ :=
  if h : 0 < n then IntegerComplexity.complexity ⟨n, h⟩ else 0

/-- The lower-bound function `g` of Corollary 2 (see the
module docstring). -/
def complexityLowerBoundG (n : ℕ) : ℕ :=
  let a := Nat.log 3 n
  if 3 * (n - 3 ^ a) < 3 ^ a then 3 * a
  else if n < 2 * 3 ^ a then 3 * a + 1
  else 3 * a + 2

/-- **Proposition 1**: for `n > 1`, `‖n‖` is the minimum of
`‖d‖ + ‖n / d‖` over divisors `d` of `n` with `d ≥ 2` and
of `‖j‖ + ‖n - j‖` over `1 ≤ j ≤ n / 2`.

Source: Juan Arias de Reyna, "Complexity of Natural
Numbers", Proposition 1. -/
theorem_wanted complexity_eq_min (n : ℕ) (hn : 2 ≤ n) :
    IsLeast {k | (∃ d : ℕ, 2 ≤ d ∧ d ∣ n ∧
        k = cx d + cx (n / d)) ∨
      (∃ j : ℕ, 1 ≤ j ∧ j ≤ n / 2 ∧ k = cx j + cx (n - j))}
      (cx n)

/-- **Proposition 2**: if `P : ℕ → ℝ` satisfies `P 1 = 1`
and `P (n + m) ≤ P n + P m`, `P (n * m) ≤ P n + P m` for
all positive `n, m`, then `P n ≤ ‖n‖` for all positive
`n`.

Source: Juan Arias de Reyna, "Complexity of Natural
Numbers", Proposition 2. -/
theorem_wanted le_complexity_of_subadditive (P : ℕ → ℝ)
    (h1 : P 1 = 1)
    (hadd : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → P (n + m) ≤ P n + P m)
    (hmul : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → P (n * m) ≤ P n + P m)
    (n : ℕ) (hn : 1 ≤ n) :
    P n ≤ (cx n : ℝ)

/-- **Corollary 1**: `log₂ (1 + n) ≤ ‖n‖` for every `n`.

Source: Juan Arias de Reyna, "Complexity of Natural
Numbers", Corollary 1. -/
theorem_wanted logb_two_add_one_le (n : ℕ) (hn : 1 ≤ n) :
    Real.logb 2 (1 + n) ≤ (cx n : ℝ)

/-- **Corollary 2**, first claim: `‖2^a * 3^b‖ = 2a + 3b`
for `a ∈ {0, 1, 2}` and all `b`, other than `a = b = 0`.

Source: Juan Arias de Reyna, "Complexity of Natural
Numbers", Corollary 2. -/
theorem_wanted complexity_two_pow_mul_three_pow (a b : ℕ)
    (ha : a ≤ 2) (hab : 1 ≤ 2 * a + 3 * b) :
    cx (2 ^ a * 3 ^ b) = 2 * a + 3 * b

/-- **Corollary 2**, second claim: writing an integer
`v > 1` uniquely as `v = 2a + 3b` with `a ∈ {0, 1, 2}`,
the number `2^a * 3^b` is the greatest `m` with
`‖m‖ = v`; in particular `m > 2^a * 3^b` implies
`‖m‖ > 2a + 3b`.

Source: Juan Arias de Reyna, "Complexity of Natural
Numbers", Corollary 2. -/
theorem_wanted complexity_lt_of_gt_extremal (a b m : ℕ)
    (ha : a ≤ 2) (hab : 2 ≤ 2 * a + 3 * b)
    (hm : 2 ^ a * 3 ^ b < m) :
    2 * a + 3 * b < cx m

/-- **Corollary 2**, third claim: `g n ≤ ‖n‖` for all
positive `n`, for the lower-bound function `g` given by
`complexityLowerBoundG`.

Source: Juan Arias de Reyna, "Complexity of Natural
Numbers", Corollary 2. -/
theorem_wanted complexityLowerBoundG_le (n : ℕ) (hn : 1 ≤ n) :
    complexityLowerBoundG n ≤ cx n

end MathlibExt.NumberTheory.IntegerComplexityWanted
