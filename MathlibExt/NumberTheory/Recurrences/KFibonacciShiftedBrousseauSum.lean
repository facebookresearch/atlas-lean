/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.KFibonacciBrousseauSums
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.Recurrences.Internal.BrousseauSum

/-!
# Shifted power-weighted sums of k-Fibonacci numbers

Multiplying the shifted sum by `k` gives a difference of endpoint expressions involving
the Brousseau polynomials and consecutive `k`-Fibonacci numbers.
-/

namespace MetaMathlibExt

-- Keep the nonzero proof in the Lucas parameters inline, as in the wanted statement.
set_option backward.proofsInPublic true in
/-- **Shifted power-weighted sums of k-Fibonacci numbers.** Let $k$ be a nonzero integer and let
$F_{k,n}$ be the $k$-Fibonacci numbers, the Lucas sequence $U(k, -1)$: $F_{k,0} = 0$,
$F_{k,1} = 1$ and $F_{k,n+2} = k F_{k,n+1} + F_{k,n}$. Let $A_k^{(0)} = 1$ and
$A_k^{(p)} = \frac{2}{k} \sum_{j=1}^{\lceil p/2 \rceil} \binom{p}{2j-1} A_k^{(p-2j+1)}$ for
$p \ge 1$, and let $C_k^{(p)}(x) = \sum_{r=0}^{p} (-1)^r A_k^{(r)} \binom{p}{r} x^{p-r}$, with
$0^0 = 1$. Then for all natural numbers $m$, $n$ and $p$,
$$
k \sum_{i=1}^{n} i^p F_{k,m+i} = C_k^{(p)}(n) F_{k,m+n+1} + C_k^{(p)}(n+1) F_{k,m+n} -
C_k^{(p)}(0) F_{k,m+1} - C_k^{(p)}(1) F_{k,m}.
$$

The source takes $k$ to be a positive integer.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Theorem 11 (`jis-2024-24.6.4-thm-11`). -/
public theorem kFibonacci_shifted_brousseau_sum (k : ℤ) (hk : k ≠ 0) (m n p : ℕ) :
    (k : ℚ) * ∑ i ∈ Finset.Icc 1 n, (i : ℚ) ^ p * lucasU ⟨k, -1, by decide⟩ (m + i) =
      brousseauCoeff k p n * lucasU ⟨k, -1, by decide⟩ (m + n + 1) +
        brousseauCoeff k p (n + 1) * lucasU ⟨k, -1, by decide⟩ (m + n) -
        brousseauCoeff k p 0 * lucasU ⟨k, -1, by decide⟩ (m + 1) -
        brousseauCoeff k p 1 * lucasU ⟨k, -1, by decide⟩ m := by
  let F (i : ℕ) : ℚ := lucasU ⟨k, -1, by decide⟩ (m + i)
  let C := brousseauCoeff k p
  change (k : ℚ) * ∑ i ∈ Finset.Icc 1 n, (i : ℚ) ^ p * F i =
    C n * F (n + 1) + C (n + 1) * F n - C 0 * F 1 - C 1 * F 0
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)), mul_add, ih]
    have hC := BrousseauSum.coeff_shift k (by exact_mod_cast hk) p ((n : ℚ) + 1)
    simp only [add_sub_cancel_right] at hC
    have hF : F (n + 2) = k * F (n + 1) + F n := by
      simpa only [F, Nat.add_assoc, neg_one_mul, sub_neg_eq_add, Int.cast_add, Int.cast_mul] using
        congrArg (Int.cast : ℤ → ℚ) (lucasU_add_two ⟨k, -1, by decide⟩ (m + n))
    simp only [Nat.cast_add_one]
    rw [hF]
    linear_combination -F (n + 1) * hC

end MetaMathlibExt
