/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Girgensohn's lemma on dyadic mantissas

For a positive integer `n`, let `p n = 2 ^ Nat.log 2 n` be the largest power of two not exceeding
`n`. The dyadic mantissa `(n - p n) / p n` is a dyadic rational in `[0, 1)`. Two positive integers
`m` and `n` have the same mantissa exactly when `2 ^ Nat.log 2 n * m = 2 ^ Nat.log 2 m * n`, that
is, when they differ by a factor that is a power of two. So a function `G` on the natural numbers
factors through the mantissa if and only if `G (2 * n) = G n` for every positive `n`.

## Main results

* `MetaMathlibExt.dyadicMantissa_wellDefined_iff_doubling_invariant`: Girgensohn's lemma.

## References

* Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*, INTEGERS 26
  (2026), Article A61; arXiv:2407.15201 (version 3), Lemma 1. There the lemma is attributed to
  R. Girgensohn, *Digital Sums and Functional Equations*, Integers 12 (2012), no. 1, 141–160.
-/

namespace MetaMathlibExt

/-- **Girgensohn's lemma.** Let $G$ be a function from the natural numbers to the real numbers, and
for a positive integer $n$ let $p_n = 2^{\lfloor \log_2 n \rfloor}$, so that $(n - p_n)/p_n$ is a
dyadic rational in $[0, 1)$. The following are equivalent: (i) for all positive integers $m$ and
$n$ with $(m - p_m)/p_m = (n - p_n)/p_n$ we have $G(m) = G(n)$, that is, $F((n - p_n)/p_n) = G(n)$
well-defines a function $F$ of these dyadic rationals; (ii) $G(2n) = G(n)$ for every positive
integer $n$.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Lemma 1 (`integers-2026-A61-lem-1`), quoting Girgensohn,
*Digital Sums and Functional Equations*, Lemma 1. -/
public theorem dyadicMantissa_wellDefined_iff_doubling_invariant (G : ℕ → ℝ) :
    (∀ m n : ℕ, 0 < m → 0 < n →
        ((m : ℚ) - 2 ^ Nat.log 2 m) / 2 ^ Nat.log 2 m =
          ((n : ℚ) - 2 ^ Nat.log 2 n) / 2 ^ Nat.log 2 n → G m = G n) ↔
      ∀ n : ℕ, 0 < n → G (2 * n) = G n := by
  constructor
  · -- `2 * n` and `n` have the same mantissa, since `Nat.log 2 (2 * n) = Nat.log 2 n + 1`.
    intro h n hn
    apply h (2 * n) n (by omega) hn
    rw [mul_comm 2 n, Nat.log_mul_base one_lt_two hn.ne', pow_succ]
    push_cast
    field_simp
  · intro h m n hm hn hmn
    -- Doubling invariance gives invariance under multiplication by any power of two.
    have hpow (k a : ℕ) (ha : 0 < a) : G (2 ^ k * a) = G a := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, mul_comm (2 ^ k) 2, mul_assoc, h _ (by positivity), ih]
    -- Equal mantissas mean `m / 2 ^ Nat.log 2 m = n / 2 ^ Nat.log 2 n`.
    have key : 2 ^ Nat.log 2 n * m = 2 ^ Nat.log 2 m * n := by
      rw [div_eq_div_iff (by positivity) (by positivity)] at hmn
      have hcast : ((2 ^ Nat.log 2 n * m : ℕ) : ℚ) = ((2 ^ Nat.log 2 m * n : ℕ) : ℚ) := by
        push_cast
        linear_combination hmn
      exact_mod_cast hcast
    rw [← hpow (Nat.log 2 n) m hm, key, hpow (Nat.log 2 m) n hn]

end MetaMathlibExt
