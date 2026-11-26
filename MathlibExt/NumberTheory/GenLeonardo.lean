/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Recurrences.HoradamGeneralizedCatalanIdentity

/-!
# Generalized Leonardo numbers

For an integer `k`, the generalized Leonardo numbers `L_{k,n} = genLeonardo k n` are defined by
`L_{k,0} = L_{k,1} = 1` and `L_{k,n+2} = L_{k,n+1} + L_{k,n} + k`. For `k = 1` they are the
Leonardo numbers `1, 1, 3, 5, 9, 15, …`.

The companion sequence is determined by sums of pairs of generalized Leonardo numbers.

Main results:

* `genLeonardo_shift`: for `1 ≤ t ≤ n` and `n + 1 ≤ m + t`,
  `L_{k,m} L_{k,n} - L_{k,m+t} L_{k,n-t}
    = (-1)^{n-t+1} (L_{k,m+t-n-1} + k) (L_{k,t-1} + k)
      - k (L_{k,m} + L_{k,n} - L_{k,m+t} - L_{k,n-t})`
  (Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci Quarterly 62 (2024),
  Theorem 2.5).

* `genLeonardo_sq_sum_diff` gives the difference and sum of squares at the sum and difference
  indices by specializing the shift identity at two consecutive shifts.

* `genLeonardo_sq_sub_sq`: for `1 ≤ n`,
  `M_{k,n}^2 - L_{k,n}^2 = 4 L_{k,n-1} L_{k,n+1} + 2k L_{k,n} + k^2`
  (Kuhapatanakul, Theorem 2.4). Since `M_{k,n} = L_{k,n-1} + L_{k,n+1}` and
  `L_{k,n} = L_{k,n+1} - L_{k,n-1} - k`, it is a polynomial identity.

Further identities from the paper are stated in `WantedExt.NumberTheory.GenLeonardoWanted`.

## Proof

The shifted sequence `G_n = L_{k,n} + k` satisfies `G_{n+2} = G_{n+1} + G_n` and
`G_0 = G_1 = 1 + k`, so `G_n = (1 + k) F_{n+1}`, where `F_n = Nat.fib n`. Since
`L_{k,i} = G_i - k`, the left side of the identity is
`G_m G_n - G_{m+t} G_{n-t} - k (L_{k,m} + L_{k,n} - L_{k,m+t} - L_{k,n-t})`, so the identity says
`G_m G_n - G_{m+t} G_{n-t} = (-1)^{n-t+1} G_{m+t-n-1} G_{t-1}`. This is `(1 + k) ^ 2` times
Vajda's identity

`F_{a+j} F_{a+t} - F_a F_{a+j+t} = (-1)^a F_j F_t`

with `a = n - t + 1` and `j = m + t - n`. Vajda's identity is the generalized Catalan identity
for Horadam sequences, `horadam_generalized_catalan_identity`, in the case `c₁ = c₂ = 1` with the
Fibonacci numbers as all three sequences.

## References

* Kantaphon Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, The Fibonacci Quarterly 62
  (2024), no. 3, 201–207, Theorems 2.4 and 2.5, the source of the statements.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Generalized Leonardo numbers.** For an integer $k$, the generalized Leonardo numbers
$L_{k,0}, L_{k,1}, L_{k,2}, \ldots$ are the integers defined by $L_{k,0} = L_{k,1} = 1$ and
$L_{k,n+2} = L_{k,n+1} + L_{k,n} + k$ for all $n \ge 0$.

The paper takes $k$ positive; here $k$ may be any integer.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly 62.3 (2024), introduction. -/
public def genLeonardo (k : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => genLeonardo k (n + 1) + genLeonardo k n + k

/-- **Generalized Leonardo number of index two.** For every integer $k$, the generalized
Leonardo number $L_{k,2}$ equals $2 + k$.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024). -/
public theorem genLeonardo_two (k : ℤ) : genLeonardo k 2 = 2 + k := rfl

/-- **Dual generalized Leonardo numbers.** For an integer $k$, let $L_{k,n}$ denote the generalized
Leonardo numbers. The dual generalized Leonardo numbers $M_{k,n}$, for natural numbers $n$, are
defined by $M_{k,0} = 1 - k$ and $M_{k,n+1} = L_{k,n} + L_{k,n+2}$, so that
$M_{k,n} = L_{k,n-1} + L_{k,n+1}$ for $n \ge 1$.

This agrees with the paper's Definition 2.1, which sets $M_{k,0} = 1 - k$, $M_{k,1} = k + 3$, and
$M_{k,n+1} = M_{k,n} + M_{k,n-1} + 2k$ for $n \ge 1$.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*,
Fibonacci Quarterly 62.3 (2024), Definition 2.1 and identity (2.1). -/
public def genLeonardoCompanion (k : ℤ) : ℕ → ℤ
  | 0 => 1 - k
  | n + 1 => genLeonardo k n + genLeonardo k (n + 2)

/-- **The dual generalized Leonardo number of index one.** For every integer $k$, the dual
generalized Leonardo number $M_{k,1}$ equals $3 + k$.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024). -/
public theorem genLeonardoCompanion_one (k : ℤ) :
    genLeonardoCompanion k 1 = 3 + k := by
  change genLeonardo k 0 + genLeonardo k 2 = 3 + k
  have h0 : genLeonardo k 0 = 1 := rfl
  rw [h0, genLeonardo_two]
  ring

end

/-- The generalized Leonardo numbers shifted by `k` are `1 + k` times the Fibonacci numbers:
`L_{k,n} + k = (1 + k) F_{n+1}`. -/
private theorem genLeonardo_add_eq_mul_fib (k : ℤ) :
    ∀ n : ℕ, genLeonardo k n + k = (1 + k) * Nat.fib (n + 1)
  | 0 => by simp [genLeonardo]
  | 1 => by simp [genLeonardo, Nat.fib_two]
  | n + 2 => by
    have h0 := genLeonardo_add_eq_mul_fib k n
    have h1 := genLeonardo_add_eq_mul_fib k (n + 1)
    have hF : (Nat.fib (n + 3) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
      exact_mod_cast Nat.fib_add_two
    rw [genLeonardo, hF]
    linear_combination h0 + h1

/-- **Vajda's identity** `F_{a+j} F_{a+t} - F_a F_{a+j+t} = (-1)^a F_j F_t`, for `a = d + 1`,
`j = e + 1` and `t = s + 1`: the generalized Catalan identity
`horadam_generalized_catalan_identity` for `c₁ = c₂ = 1` and the Fibonacci numbers. -/
private theorem fib_vajda (d e s : ℕ) :
    (Nat.fib (d + e + 2) : ℤ) * Nat.fib (d + s + 2) - Nat.fib (d + 1) * Nat.fib (d + e + s + 3)
      = (-1) ^ (d + 1) * (Nat.fib (e + 1) * Nat.fib (s + 1)) := by
  have hF (n : ℕ) : (Nat.fib (n + 2) : ℤ) = 1 * Nat.fib (n + 1) + 1 * Nat.fib n := by
    rw [Nat.fib_add_two, Nat.cast_add]
    ring
  have h := horadam_generalized_catalan_identity (1 : ℤ) 1 (fun n ↦ (Nat.fib n : ℤ))
    (fun n ↦ (Nat.fib n : ℤ)) (fun n ↦ (Nat.fib n : ℤ)) hF hF hF (by simp) (by simp)
    (d + 1) (e + 1) (s + 1)
  rw [show d + 1 + (e + 1) + (s + 1) = d + e + s + 3 by omega,
    show d + 1 + (e + 1) = d + e + 2 by omega, show d + 1 + (s + 1) = d + s + 2 by omega,
    Nat.fib_zero, Nat.fib_one, Nat.cast_zero, Nat.cast_one] at h
  linear_combination h

/-- **Shift identity for generalized Leonardo numbers.** Let $k$ be an integer and let $L_{k,n}$
denote the generalized Leonardo numbers. For all natural numbers $m$, $n$, $t$ with
$1 \le t \le n$ and $n + 1 \le m + t$,
$$L_{k,m} L_{k,n} - L_{k,m+t} L_{k,n-t}
= (-1)^{n-t+1} (L_{k,m+t-n-1} + k)(L_{k,t-1} + k) -
k\,(L_{k,m} + L_{k,n} - L_{k,m+t} - L_{k,n-t}).$$

The paper also allows $t = 0$, reading $L_{k,-1}$ by extending the sequence to negative indices.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 2.5 (`fq-2024-kuhapatanakul05292024-thm-2.5`). -/
public theorem genLeonardo_shift (k : ℤ) (m n t : ℕ)
    (ht : 1 ≤ t) (htn : t ≤ n) (hmt : n + 1 ≤ m + t) :
    genLeonardo k m * genLeonardo k n
        - genLeonardo k (m + t) * genLeonardo k (n - t)
      = (-1 : ℤ) ^ (n - t + 1)
          * (genLeonardo k (m + t - n - 1) + k) * (genLeonardo k (t - 1) + k)
        - k * (genLeonardo k m + genLeonardo k n
          - genLeonardo k (m + t) - genLeonardo k (n - t)) := by
  -- Write `t = s + 1`, `n = d + s + 1` and `m = d + e + 1`, so that `n - t = d`, `t - 1 = s`
  -- and `m + t - n - 1 = e`.
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, n = d + s + 1 := ⟨n - (s + 1), by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, m = d + e + 1 := ⟨m - (d + 1), by omega⟩
  rw [show d + e + 1 + (s + 1) - (d + s + 1) - 1 = e by omega,
    show d + s + 1 - (s + 1) = d by omega, show s + 1 - 1 = s by omega,
    show d + e + 1 + (s + 1) = d + e + s + 2 by omega]
  -- Each `L_{k,i}` is `(1 + k) F_{i+1} - k`.
  have hL (i : ℕ) : genLeonardo k i = (1 + k) * Nat.fib (i + 1) - k :=
    eq_sub_of_add_eq (genLeonardo_add_eq_mul_fib k i)
  rw [hL (d + e + 1), hL (d + s + 1), hL (d + e + s + 2), hL d, hL e, hL s]
  linear_combination (1 + k) ^ 2 * fib_vajda d e s

/-- **Sum-and-difference square identities for generalized Leonardo numbers.** For every
integer $k$ and all natural numbers $m$, $n$ with $1 \le n < m$, the generalized Leonardo
numbers $L_{k,n}$ satisfy
$$L_{k,m+n}^2 - L_{k,m-n}^2 =
(L_{k,2m+1} + k)(L_{k,2n-1} + k) - 2k (L_{k,m+n} - L_{k,m-n})$$
and
$$L_{k,m+n}^2 + L_{k,m-n-1}^2 =
(L_{k,2m} + k)(L_{k,2n} + k) - 2k (L_{k,m+n} + L_{k,m-n-1}) - 2k^2.$$

In the second identity the last term inside the parentheses is $L_{k,m-n-1}$. The paper as
printed shows $L_{k,m-n}$ there, which is false: at $k = 1$, $m = 3$, $n = 1$ the printed
identity reads $82 = 78$. The reading used here agrees with the paper's outline derivation.

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 2.6 (`fq-2024-kuhapatanakul05292024-thm-2.6`). -/
public theorem genLeonardo_sq_sum_diff (k : ℤ) (m n : ℕ)
    (hn : 1 ≤ n) (hmn : n < m) :
    (genLeonardo k (m + n) ^ 2 - genLeonardo k (m - n) ^ 2
      = (genLeonardo k (2 * m + 1) + k) * (genLeonardo k (2 * n - 1) + k)
        - 2 * k * (genLeonardo k (m + n) - genLeonardo k (m - n))) ∧
    (genLeonardo k (m + n) ^ 2 + genLeonardo k (m - n - 1) ^ 2
      = (genLeonardo k (2 * m) + k) * (genLeonardo k (2 * n) + k)
        - 2 * k * (genLeonardo k (m + n) + genLeonardo k (m - n - 1))
        - 2 * k ^ 2) := by
  constructor
  · -- Shifting both copies of the index `m + n` by `m - n + 1` gives an even exponent.
    have h := genLeonardo_shift k (m + n) (m + n) (m - n + 1) (by omega) (by omega) (by omega)
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel, show m + n + (m - n + 1) = 2 * m + 1 by omega,
      show m + n - (m - n + 1) = 2 * n - 1 by omega, show 2 * n - 1 + 1 = 2 * n by omega,
      (even_two_mul n).neg_one_pow] at h
    linear_combination h
  · -- Shifting by `m - n` instead gives an odd exponent.
    have h := genLeonardo_shift k (m + n) (m + n) (m - n) (by omega) (by omega) (by omega)
    rw [Nat.add_sub_cancel_left, show m + n + (m - n) = 2 * m by omega,
      show m + n - (m - n) = 2 * n by omega, pow_succ, (even_two_mul n).neg_one_pow] at h
    linear_combination h

/-- **Square-difference identity for generalized Leonardo numbers.** For every integer $k$ and
every natural number $n \ge 1$, the generalized Leonardo numbers $L_{k,n}$ and the dual
generalized Leonardo numbers $M_{k,n}$ satisfy
$$M_{k,n}^2 - L_{k,n}^2 = 4 L_{k,n-1} L_{k,n+1} + 2k L_{k,n} + k^2.$$

Source: Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci
Quarterly (2024), Theorem 2.4 (`fq-2024-kuhapatanakul05292024-thm-2.4`). -/
public theorem genLeonardo_sq_sub_sq (k : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    genLeonardoCompanion k n ^ 2 - genLeonardo k n ^ 2
      = 4 * genLeonardo k (n - 1) * genLeonardo k (n + 1)
        + 2 * k * genLeonardo k n + k ^ 2 := by
  -- Write `n = m + 1`; then `M_{k,n} = L_{k,m} + L_{k,m+2}` and
  -- `L_{k,m+2} = L_{k,m+1} + L_{k,m} + k`.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hM : genLeonardoCompanion k (m + 1) = genLeonardo k m + genLeonardo k (m + 2) := rfl
  have hL : genLeonardo k (m + 2) = genLeonardo k (m + 1) + genLeonardo k m + k := rfl
  rw [hM, Nat.add_sub_cancel, show m + 1 + 1 = m + 2 by omega, hL]
  ring

end MetaMathlibExt
