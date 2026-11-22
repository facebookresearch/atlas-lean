/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Fib.Basic
public import MathlibExt.Combinatorics.Enumerative.MotzkinNumber
public import MathlibExt.Combinatorics.Enumerative.RiordanNumber

namespace MetaMathlibExt

@[expose] public section

/-- The even-indexed Riordan numbers `r₀, r₂, r₄, …` form a log-convex sequence:
`r_{2n}² ≤ r_{2n-2} · r_{2n+2}` for every `n ≥ 1`, written here with `n + 1` in place
of `n`. The Riordan numbers are `MetaMathlibExt.riordanNumber` (`1, 0, 1, 1, 3, 6, 15, …`).

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Corollary 1
(`integers-2026-A55-cor-1`). -/
public theorem_wanted riordanNumber_even_logConvex (n : ℕ) :
    riordanNumber (2 * (n + 1)) ^ 2 ≤
      riordanNumber (2 * n) * riordanNumber (2 * (n + 2))

/-- The alternating sums of Motzkin numbers `T_n = ∑_{k=0}^n (-1)^{n-k} M_k` (OEIS A187306:
`1, 0, 2, 2, 7, 14, 37, …`), with `M_k = MetaMathlibExt.motzkinNumber k`.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Equation (2). -/
public def motzkinAlternatingSum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1) ^ (n - k) * (motzkinNumber k : ℤ)

/-- `T_0 = 1`.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Table 2. -/
public theorem motzkinAlternatingSum_zero : motzkinAlternatingSum 0 = 1 := by
  simp [motzkinAlternatingSum, motzkinNumber_zero]

/-- `T_{n+1} = M_{n+1} - T_n`.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Equation (2). -/
public theorem motzkinAlternatingSum_succ (n : ℕ) :
    motzkinAlternatingSum (n + 1) = motzkinNumber (n + 1) - motzkinAlternatingSum n := by
  rw [motzkinAlternatingSum, Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul,
    motzkinAlternatingSum, sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
  ring

/-- Small values: `T_1 = 0` and `T_2 = 2`.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Table 2. -/
public theorem motzkinAlternatingSum_one_two :
    motzkinAlternatingSum 1 = 0 ∧ motzkinAlternatingSum 2 = 2 := by
  have h1 : motzkinAlternatingSum 1 = 0 := by
    rw [motzkinAlternatingSum_succ, motzkinAlternatingSum_zero, motzkinNumber_one]; norm_num
  refine ⟨h1, ?_⟩
  rw [motzkinAlternatingSum_succ, h1, motzkinNumber_two]; norm_num

/-- The alternating sums of Fibonacci numbers `W_n = ∑_{k=0}^n (-1)^{n-k} F_k`
(`0, 1, 0, 2, 1, 4, 4, 9, …`), with `F_k = Nat.fib k`.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Equation (9). -/
public def fibonacciAlternatingSum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1) ^ (n - k) * (Nat.fib k : ℤ)

/-- `W_0 = 0`.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Table 3. -/
public theorem fibonacciAlternatingSum_zero : fibonacciAlternatingSum 0 = 0 := by
  simp [fibonacciAlternatingSum]

/-- `W_{n+1} = F_{n+1} - W_n`.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Equation (9). -/
public theorem fibonacciAlternatingSum_succ (n : ℕ) :
    fibonacciAlternatingSum (n + 1) = Nat.fib (n + 1) - fibonacciAlternatingSum n := by
  rw [fibonacciAlternatingSum, Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul,
    fibonacciAlternatingSum, sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
  ring

/-- `{T_n}_{n ≥ 8}` is log-balanced and `{T_n}_{n ≥ 5}` is tempered. Following the paper
(Došlić), a positive sequence `z` is log-balanced on `n ≥ N` if `z_n² ≤ z_{n-1} z_{n+1}`
(log-convex) and `z_n/n!` is log-concave, i.e. `n z_{n-1} z_{n+1} ≤ (n+1) z_n²`, for every
`n ≥ N + 1`; it is tempered if its quotients `x_n = z_{n+1}/z_n` satisfy
`n/(n+1) x_{n-1} ≤ x_n ≤ (n+1)/n x_{n-1}`, i.e. `n z_n² ≤ (n+1) z_{n-1} z_{n+1}` and
`n z_{n-1} z_{n+1} ≤ (n+1) z_n²`, for every `n ≥ N + 1`. The factorials and quotient
weights use the original index `n`, as in the paper's proofs; the inequalities are
cleared of denominators (all terms are positive here).

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Theorem 1. -/
public theorem_wanted motzkinAlternatingSum_logBalanced_tempered :
    (∀ n, 9 ≤ n →
      motzkinAlternatingSum n ^ 2 ≤
          motzkinAlternatingSum (n - 1) * motzkinAlternatingSum (n + 1) ∧
        n * (motzkinAlternatingSum (n - 1) * motzkinAlternatingSum (n + 1)) ≤
          (n + 1) * motzkinAlternatingSum n ^ 2) ∧
    (∀ n, 6 ≤ n →
      n * motzkinAlternatingSum n ^ 2 ≤
          (n + 1) * (motzkinAlternatingSum (n - 1) * motzkinAlternatingSum (n + 1)) ∧
        n * (motzkinAlternatingSum (n - 1) * motzkinAlternatingSum (n + 1)) ≤
          (n + 1) * motzkinAlternatingSum n ^ 2)

/-- `{T_n T_{n+1}}_{n ≥ 6}` is log-convex and `{T_n T_{n+1}}_{n ≥ 9}` is log-balanced, with
the notions of `motzkinAlternatingSum_logBalanced_tempered` (conditions at every
`n ≥ N + 1`, original index in the factorial weight).

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Theorem 2. -/
public theorem_wanted motzkinAlternatingSum_mul_succ_logConvex_logBalanced :
    (∀ n, 7 ≤ n →
      (motzkinAlternatingSum n * motzkinAlternatingSum (n + 1)) ^ 2 ≤
        (motzkinAlternatingSum (n - 1) * motzkinAlternatingSum n) *
          (motzkinAlternatingSum (n + 1) * motzkinAlternatingSum (n + 2))) ∧
    (∀ n, 10 ≤ n →
      (motzkinAlternatingSum n * motzkinAlternatingSum (n + 1)) ^ 2 ≤
          (motzkinAlternatingSum (n - 1) * motzkinAlternatingSum n) *
            (motzkinAlternatingSum (n + 1) * motzkinAlternatingSum (n + 2)) ∧
        n * ((motzkinAlternatingSum (n - 1) * motzkinAlternatingSum n) *
            (motzkinAlternatingSum (n + 1) * motzkinAlternatingSum (n + 2))) ≤
          (n + 1) * (motzkinAlternatingSum n * motzkinAlternatingSum (n + 1)) ^ 2)

/-- `{M_n + T_n}_{n ≥ 6}` is log-balanced (notion of
`motzkinAlternatingSum_logBalanced_tempered`: conditions at every `n ≥ 7`).

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Theorem 3. -/
public theorem_wanted motzkinNumber_add_motzkinAlternatingSum_logBalanced (n : ℕ) (hn : 7 ≤ n) :
    ((motzkinNumber n : ℤ) + motzkinAlternatingSum n) ^ 2 ≤
        ((motzkinNumber (n - 1) : ℤ) + motzkinAlternatingSum (n - 1)) *
          ((motzkinNumber (n + 1) : ℤ) + motzkinAlternatingSum (n + 1)) ∧
      n * (((motzkinNumber (n - 1) : ℤ) + motzkinAlternatingSum (n - 1)) *
          ((motzkinNumber (n + 1) : ℤ) + motzkinAlternatingSum (n + 1))) ≤
        (n + 1) * ((motzkinNumber n : ℤ) + motzkinAlternatingSum n) ^ 2

/-- `{W_n}_{n ≥ 11}` is tempered (notion of `motzkinAlternatingSum_logBalanced_tempered`:
conditions at every `n ≥ 12`).

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Theorem 4. -/
public theorem_wanted fibonacciAlternatingSum_tempered (n : ℕ) (hn : 12 ≤ n) :
    n * fibonacciAlternatingSum n ^ 2 ≤
        (n + 1) * (fibonacciAlternatingSum (n - 1) * fibonacciAlternatingSum (n + 1)) ∧
      n * (fibonacciAlternatingSum (n - 1) * fibonacciAlternatingSum (n + 1)) ≤
        (n + 1) * fibonacciAlternatingSum n ^ 2

end

end MetaMathlibExt
