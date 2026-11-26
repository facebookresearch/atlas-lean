/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.KFibonacciShiftedBrousseauSum

/-! # Brousseau sums of k-Fibonacci numbers -/

namespace MetaMathlibExt

-- Keep the nonzero proof in the Lucas parameters inline, as in the wanted statement.
set_option backward.proofsInPublic true in
/-- **Brousseau sums of $k$-Fibonacci numbers.** For an integer $k$, let $F_{k,n}$ be the
$k$-Fibonacci numbers, the Lucas sequence $U(k, -1)$ ($F_{k,0} = 0$, $F_{k,1} = 1$,
$F_{k,n+2} = k F_{k,n+1} + F_{k,n}$), and let $C_k^{(p)}$ be the coefficient polynomials. For
every nonzero integer $k$ and all $n, p \ge 0$,
$$
k \sum_{i=0}^{n} i^p F_{k,i} = C_k^{(p)}(n) F_{k,n+1} + C_k^{(p)}(n+1) F_{k,n} - C_k^{(p)}(0),
$$
where $0^0 = 1$.

The paper assumes $k \ge 1$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Theorem 6 (`jis-2024-24.6.4-thm-6`). -/
public theorem kFibonacci_brousseau_sum (k : ℤ) (hk : k ≠ 0) (n p : ℕ) :
    (k : ℚ) * ∑ i ∈ Finset.range (n + 1), (i : ℚ) ^ p * lucasU ⟨k, -1, by decide⟩ i =
      brousseauCoeff k p n * lucasU ⟨k, -1, by decide⟩ (n + 1) +
        brousseauCoeff k p (n + 1) * lucasU ⟨k, -1, by decide⟩ n - brousseauCoeff k p 0 := by
  have hrange : insert 0 (Finset.Icc 1 n) = Finset.range (n + 1) := by
    ext i
    simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_range]
    omega
  have hzero : lucasU ⟨k, -1, by decide⟩ 0 = 0 := rfl
  have hone : lucasU ⟨k, -1, by decide⟩ 1 = 1 := rfl
  -- The zero index contributes nothing, including when p = 0.
  rw [← hrange, Finset.sum_insert (by simp), hzero, Int.cast_zero, mul_zero, zero_add]
  simpa only [Nat.zero_add, hone, hzero, Int.cast_one, Int.cast_zero, mul_one, mul_zero, sub_zero]
    using kFibonacci_shifted_brousseau_sum k hk 0 n p

end MetaMathlibExt
