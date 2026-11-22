/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Generalized Leonardo numbers

For an integer `k`, the generalized Leonardo numbers `L_{k,n} = genLeonardo k n` are defined by
`L_{k,0} = L_{k,1} = 1` and `L_{k,n+2} = L_{k,n+1} + L_{k,n} + k`. For `k = 1` they are the
Leonardo numbers `1, 1, 3, 5, 9, 15, …`.

Main result:

* `genLeonardo_shift`: for `1 ≤ t ≤ n` and `n + 1 ≤ m + t`,
  `L_{k,m} L_{k,n} - L_{k,m+t} L_{k,n-t}
    = (-1)^{n-t+1} (L_{k,m+t-n-1} + k) (L_{k,t-1} + k)
      - k (L_{k,m} + L_{k,n} - L_{k,m+t} - L_{k,n-t})`
  (Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci Quarterly 62 (2024),
  Theorem 2.5).

The other identities of that paper are wanted statements in
`WantedExt.NumberTheory.GenLeonardoWanted`.

## Proof

The shifted sequence `G_n = L_{k,n} + k` satisfies `G_{n+2} = G_{n+1} + G_n` and
`G_0 = G_1 = 1 + k`, so `G_n = (1 + k) F_{n+1}`, where `F_n = Nat.fib n`. Since
`L_{k,i} = G_i - k`, the left side of the identity is
`G_m G_n - G_{m+t} G_{n-t} - k (L_{k,m} + L_{k,n} - L_{k,m+t} - L_{k,n-t})`, so the identity says
`G_m G_n - G_{m+t} G_{n-t} = (-1)^{n-t+1} G_{m+t-n-1} G_{t-1}`. This is `(1 + k) ^ 2` times
Vajda's identity

`F_{a+j} F_{a+t} - F_a F_{a+j+t} = (-1)^a F_j F_t`

with `a = n - t + 1` and `j = m + t - n`. With `a = d + 1`, `j = e + 1` and `t = s + 1`, the
addition formula `F_{p+q+1} = F_p F_q + F_{p+1} F_{q+1}` (`Nat.fib_add`) expands the left side of
Vajda's identity to `F_{e+1} F_{s+1} (F_{d+2}^2 - F_{d+1}^2 - F_{d+1} F_{d+2})`, and Cassini's
identity `F_d F_{d+2} - F_{d+1}^2 = (-1)^{d+1}` finishes the proof.

## References

* Kantaphon Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, The Fibonacci Quarterly 62
  (2024), no. 3, 201–207, Theorem 2.5, the source of the statement.
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

/-- **Cassini's identity**, in the form `F_d F_{d+2} - F_{d+1}^2 = (-1)^{d+1}`. -/
private theorem fib_mul_fib_add_two_sub_sq (d : ℕ) :
    (Nat.fib d : ℤ) * Nat.fib (d + 2) - (Nat.fib (d + 1) : ℤ) ^ 2 = (-1) ^ (d + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h2 : (Nat.fib (d + 2) : ℤ) = Nat.fib d + Nat.fib (d + 1) := by
      exact_mod_cast Nat.fib_add_two
    have h3 : (Nat.fib (d + 3) : ℤ) = Nat.fib (d + 1) + Nat.fib (d + 2) := by
      exact_mod_cast Nat.fib_add_two
    rw [h3, pow_succ _ (d + 1)]
    linear_combination -ih - (Nat.fib (d + 2) : ℤ) * h2

/-- **Vajda's identity** `F_{a+j} F_{a+t} - F_a F_{a+j+t} = (-1)^a F_j F_t`, for `a = d + 1`,
`j = e + 1` and `t = s + 1`. -/
private theorem fib_vajda (d e s : ℕ) :
    (Nat.fib (d + e + 2) : ℤ) * Nat.fib (d + s + 2) - Nat.fib (d + 1) * Nat.fib (d + e + s + 3)
      = (-1) ^ (d + 1) * (Nat.fib (e + 1) * Nat.fib (s + 1)) := by
  have hadd (p q : ℕ) : (Nat.fib (p + q + 1) : ℤ) =
      Nat.fib p * Nat.fib q + Nat.fib (p + 1) * Nat.fib (q + 1) := by
    exact_mod_cast Nat.fib_add p q
  have h1 : (Nat.fib (d + e + 2) : ℤ) =
      Nat.fib (d + 1) * Nat.fib e + Nat.fib (d + 2) * Nat.fib (e + 1) := by
    rw [show d + e + 2 = d + 1 + e + 1 by omega]
    exact hadd (d + 1) e
  have h2 : (Nat.fib (d + s + 2) : ℤ) =
      Nat.fib (d + 1) * Nat.fib s + Nat.fib (d + 2) * Nat.fib (s + 1) := by
    rw [show d + s + 2 = d + 1 + s + 1 by omega]
    exact hadd (d + 1) s
  have h3 : (Nat.fib (d + e + s + 3) : ℤ) =
      Nat.fib (d + 1) * Nat.fib (e + s + 1) + Nat.fib (d + 2) * Nat.fib (e + s + 2) := by
    rw [show d + e + s + 3 = d + 1 + (e + s + 1) + 1 by omega]
    exact hadd (d + 1) (e + s + 1)
  have h4 : (Nat.fib (e + s + 1) : ℤ) =
      Nat.fib e * Nat.fib s + Nat.fib (e + 1) * Nat.fib (s + 1) := hadd e s
  have h5 : (Nat.fib (e + s + 2) : ℤ) =
      Nat.fib e * Nat.fib (s + 1) + Nat.fib (e + 1) * Nat.fib (s + 2) := by
    rw [show e + s + 2 = e + (s + 1) + 1 by omega]
    exact hadd e (s + 1)
  have h6 : (Nat.fib (s + 2) : ℤ) = Nat.fib s + Nat.fib (s + 1) := by
    exact_mod_cast Nat.fib_add_two
  have h7 : (Nat.fib (d + 2) : ℤ) = Nat.fib d + Nat.fib (d + 1) := by
    exact_mod_cast Nat.fib_add_two
  rw [h1, h2, h3, h4, h5, h6]
  linear_combination (Nat.fib (e + 1) * Nat.fib (s + 1) : ℤ) * fib_mul_fib_add_two_sub_sq d +
    (Nat.fib (e + 1) * Nat.fib (s + 1) * Nat.fib (d + 2) : ℤ) * h7

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

end MetaMathlibExt
