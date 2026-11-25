/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace MetaMathlibExt

/--
**Tauraso's Cassini-type identity.** Let $f_n$ be the Fibonacci numbers, with $f_0 = 0$ and
$f_1 = 1$. For natural numbers $n, m$ put $L_{n,m} = f_{n+1} f_m + f_n f_{m+1}$ and
$a_n = f_{n+1} f_{n-1} + f_n^2$, where $n - 1$ is truncated subtraction. Then
$L_{n,m} = f_{n+1} f_m + f_n f_{m+1}$ for all $n, m \ge 1$, $L_{n,n-1} = a_n$ for all
$n \ge 2$, and $L_{n,n-1}^2 = L_{n,n} L_{n-1,n-1} + 1$ for all $n \ge 2$.

In the source $L_{n,m}$ is the number of domino tilings of the L-grid, and the Fibonacci
formula for it is a theorem. Here $L_{n,m}$ is defined by that formula, so the first two
equations hold by definition and the content is the Cassini-type identity.

Source: Roberto Tauraso, "A New Domino Tiling Sequence," Journal of Integer
Sequences 7 (2004), Article 04.2.3, Lemma (Section 2, equations Lformula and
Lcassini), lines 200–221,
https://cs.uwaterloo.ca/journals/JIS/VOL7/Tauraso/tauraso3.tex
-/
public theorem domino_tilings_L_grid_via_fibonacci :
    let L : ℕ → ℕ → ℕ := fun n m =>
      Nat.fib (n + 1) * Nat.fib m + Nat.fib n * Nat.fib (m + 1)
    let a : ℕ → ℕ := fun n =>
      Nat.fib (n + 1) * Nat.fib (n - 1) + Nat.fib n ^ 2
    (∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      L n m = Nat.fib (n + 1) * Nat.fib m +
        Nat.fib n * Nat.fib (m + 1)) ∧
    (∀ n : ℕ, 2 ≤ n → L n (n - 1) = a n) ∧
    (∀ n : ℕ, 2 ≤ n →
      (L n (n - 1)) ^ 2 = L n n * L (n - 1) (n - 1) + 1) := by
  dsimp only
  refine ⟨fun _ _ _ _ => rfl, ?_, ?_⟩
  · intro n hn
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n), pow_two]
  · intro n hn
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
    apply (Nat.cast_inj (R := ℤ)).mp
    push_cast
    -- Squaring Cassini removes the alternating sign.
    have h := congrArg (fun x : ℤ => x ^ 2) (Int.fib_succ_mul_fib_pred_sub_fib_sq (n : ℤ))
    rw [← Nat.cast_add_one, ← Int.natCast_pred_of_pos (by omega : 0 < n)] at h
    simp only [Int.fib_natCast, Int.natAbs_natCast] at h
    rw [pow_right_comm (-1 : ℤ), neg_one_sq, one_pow] at h
    linear_combination h

end MetaMathlibExt
