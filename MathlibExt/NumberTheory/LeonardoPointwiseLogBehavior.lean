/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Insert
public import MathlibExt.NumberTheory.GenLeonardo
import Mathlib.Algebra.Order.Field.Basic
import MathlibExt.Combinatorics.Enumerative.GeneralizedLeonardoLogBehavior
import MathlibExt.NumberTheory.HyperLeonardoHyperFibonacci
import MathlibExt.NumberTheory.LeonardoLogBalanced

/-!
# Pointwise log-convexity and log-concavity of the Leonardo numbers

For the Leonardo numbers (`genLeonardo 1`), the log-convexity inequality holds at indices
1 and 3, the two sides are equal at index 5, and the log-concavity inequality holds at indices
2 and 4 and at every index at least 6.

The Fibonacci formula at order zero gives the small values and positivity. At index 3 we use
`leonardo_logBalanced_three`, and at index 4 and all indices at least 6 we reverse the
log-convexity inequality for the positive reciprocals from `inv_genLeonardo_logBalanced`.

## References

* Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino,
  *A Note on Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, pp. 1–18,
  Proposition 10, with Proposition 6 at order zero and the index-three case of Proposition 11.
* P. Catarino and A. Borges, *On Leonardo numbers*, Acta Mathematica Universitatis
  Comenianae 89 (2020), no. 1, pp. 75–86, Proposition 2.2, for the order-zero Fibonacci formula.
* Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the Generalized Leonardo
  Numbers*, INTEGERS 24 (2024), Article A82, pp. 1–9, Theorem 1, for the reciprocal inequality.
-/

namespace MetaMathlibExt

/-- **Log-convexity and log-concavity of the Leonardo numbers.** Let $Le_n$ be the Leonardo
numbers ($Le_0 = Le_1 = 1$ and $Le_{n+2} = Le_{n+1} + Le_n + 1$). Then
$Le_n^2 \le Le_{n-1} Le_{n+1}$ for $n = 1$ and $n = 3$, $Le_5^2 = Le_4 Le_6$, and
$Le_{n-1} Le_{n+1} \le Le_n^2$ for $n = 2$, $n = 4$ and every $n \ge 6$.

The paper's "the sequence is log-convex for $n = 1$" is read as the defining inequality at
index $n$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 10
(`integers-2026-A48-prop-10`). -/
public theorem leonardo_logConvex_logConcave_pointwise :
    (∀ n ∈ ({1, 3} : Finset ℕ),
      genLeonardo 1 n ^ 2 ≤ genLeonardo 1 (n - 1) * genLeonardo 1 (n + 1)) ∧
    genLeonardo 1 5 ^ 2 = genLeonardo 1 4 * genLeonardo 1 6 ∧
    (∀ n, n = 2 ∨ n = 4 ∨ 6 ≤ n →
      genLeonardo 1 (n - 1) * genLeonardo 1 (n + 1) ≤ genLeonardo 1 n ^ 2) := by
  have hL (i : ℕ) : genLeonardo 1 i = 2 * (Nat.fib (i + 1) : ℤ) - 1 := by
    simpa only [hyperLeonardo_zero, hyperFibonacci_zero, Nat.choose_zero_right, Nat.cast_one]
      using hyperLeonardo_eq_hyperFibonacci 0 i
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · simp only [hL]
      decide
    · exact leonardo_logBalanced_three.1
  · simp only [hL]
    decide
  · intro n hn
    rcases hn with rfl | hn
    · simp only [hL]
      decide
    have hpos (i : ℕ) : (0 : ℝ) < (genLeonardo 1 i : ℝ) := by
      have hf : 0 < (Nat.fib (i + 1) : ℤ) := by
        exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos i)
      exact_mod_cast (show 0 < genLeonardo 1 i by rw [hL]; omega)
    have h := (inv_genLeonardo_logBalanced 1 le_rfl n (by omega)).1
    rw [div_pow, one_pow, div_mul_div_comm, one_mul] at h
    have h' := (one_div_le_one_div (pow_pos (hpos n) 2)
      (mul_pos (hpos (n - 1)) (hpos (n + 1)))).mp h
    exact_mod_cast h'

end MetaMathlibExt
