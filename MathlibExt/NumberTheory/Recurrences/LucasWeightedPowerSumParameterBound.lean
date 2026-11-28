/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import MathlibExt.NumberTheory.Recurrences.LucasBinomialSum
import MathlibExt.NumberTheory.Recurrences.LucasParityDivisibility

/-!
# The parameter bound for weighted Lucas power sums

For a Lucas sequence of the first kind with parameters `x > 0` and `y = ±1`, a solution of
`∑ j = 1, …, k, j * U_j^p = U_n^q` with positive `n`, `p`, `q` and `k ≥ 3` satisfies
`x ≤ (k + 1)^2 / 4 + 1` in the rationals. Section 4 of the source assumes `k ≥ 3` throughout.
The bound also covers the small positive `x ≤ 2` outside the paper's main application; there it
holds without the equation.

For larger `x`, reducing the recurrence modulo `x` gives the constant terms used in the source.
Only the odd indices contribute on the left. Their weighted sum is either a square or a signed
count, of magnitude at least two. Subtracting the right-hand residue, of magnitude at most one,
then gives a nonzero multiple of `x`.

## References

* Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
  Equation $\sum_{j=1}^k j F_j^p = F_n^q$ to a Family of Lucas Sequences*, The Fibonacci Quarterly
  62 (2024), no. 3, 241–257, Lemma 4.4 (the bound) and Lemma 2.1 (vii) (the binomial formula).
  The proof uses `lucasU_eq_sum_choose` from `MathlibExt.NumberTheory.Recurrences.LucasBinomialSum`
  at index one and obtains the subsequent odd-index residues from the recurrence.
* Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*, INTEGERS 25 (2025),
  Article A107, 1–32, Proposition 2.3 (v). The proof reuses the even-index part of
  `p_dvd_lucasU_two_mul_and_lucasV_of_odd` from
  `MathlibExt.NumberTheory.Recurrences.LucasParityDivisibility`.
-/

namespace MetaMathlibExt

open Finset

/-- The odd-index residue follows by dropping the first term in each step of the recurrence. -/
private theorem lucasU_two_mul_add_one_modEq (P : LucasSequenceParams) (i : ℕ) :
    lucasU P (2 * i + 1) ≡ (-P.q) ^ i [ZMOD P.p] := by
  induction i with
  | zero =>
    have hOne : lucasU P 1 = 1 := by
      simpa using lucasU_eq_sum_choose P (r := 1) (by decide)
    simp [hOne]
  | succ i ih =>
    rw [show 2 * (i + 1) + 1 = (2 * i + 1) + 2 by omega, lucasU_add_two, pow_succ', neg_mul]
    simpa only [zero_sub] using
      (dvd_mul_right P.p (lucasU P (2 * i + 1 + 1))).modEq_zero_int.sub (ih.mul_left P.q)

/-- Pair the even and odd indices; only the odd terms survive modulo `P.p`. -/
private theorem weighted_lucas_sum_modEq (P : LucasSequenceParams) {p : ℕ} (hp : 0 < p) (k : ℕ) :
    (∑ j ∈ Icc 1 k, (j : ℤ) * lucasU P j ^ p) ≡
      (∑ i ∈ range ((k + 1) / 2), (2 * (i : ℤ) + 1) * ((-P.q) ^ p) ^ i) [ZMOD P.p] := by
  let f (j : ℕ) := (j : ℤ) * lucasU P j ^ p
  let g (i : ℕ) := (2 * (i : ℤ) + 1) * ((-P.q) ^ p) ^ i
  have he (i : ℕ) : f (2 * i) ≡ 0 [ZMOD P.p] := by
    have h := (p_dvd_lucasU_two_mul_and_lucasV_of_odd P).1 i
    simpa only [f, zero_pow hp.ne', mul_zero] using (h.modEq_zero_int.pow p).mul_left (↑(2 * i))
  have ho (i : ℕ) : f (2 * i + 1) ≡ g i [ZMOD P.p] := by
    simpa only [f, g, ← pow_mul, Nat.mul_comm i p, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one] using ((lucasU_two_mul_add_one_modEq P i).pow p).mul_left (↑(2 * i + 1))
  have hpair (m : ℕ) : (∑ j ∈ range (2 * m), f j) ≡ (∑ i ∈ range m, g i) [ZMOD P.p] := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, sum_range_succ, sum_range_succ, sum_range_succ]
      simpa only [add_zero] using (ih.add (he m)).add (ho m)
  have hrange : (∑ j ∈ range (k + 1), f j) = ∑ j ∈ Icc 1 k, f j := by
    symm
    apply sum_subset
    · intro j hj
      have := (mem_Icc.mp hj).2
      exact mem_range.mpr (by omega)
    · intro j hj hj'
      have := mem_range.mp hj
      have hzero : j = 0 := by
        simp only [mem_Icc, not_and_or] at hj'
        omega
      simp [hzero, f]
  change (∑ j ∈ Icc 1 k, f j) ≡ (∑ i ∈ range ((k + 1) / 2), g i) [ZMOD P.p]
  rw [← hrange]
  let m := (k + 1) / 2
  change (∑ j ∈ range (k + 1), f j) ≡ (∑ i ∈ range m, g i) [ZMOD P.p]
  have hcut : k + 1 = 2 * m ∨ k + 1 = 2 * m + 1 := by dsimp [m]; omega
  rcases hcut with hcut | hcut
  · exact hcut ▸ hpair m
  · rw [hcut, sum_range_succ]
    simpa only [add_zero] using (hpair m).add (he m)

/-- Telescoping evaluates the two signed sums of odd weights. -/
private theorem abs_signed_odd_weight_sum {a : ℤ} (ha : a = 1 ∨ a = -1) (m : ℕ) :
    |∑ i ∈ range m, (2 * (i : ℤ) + 1) * a ^ i| = if a = 1 then (m : ℤ) ^ 2 else m := by
  rcases ha with rfl | rfl
  · simp only [one_pow, mul_one, ↓reduceIte]
    have hs : (∑ i ∈ range m, (2 * (i : ℤ) + 1)) = (m : ℤ) ^ 2 := by
      calc
        _ = ∑ i ∈ range m, (((i + 1 : ℕ) : ℤ) ^ 2 - (i : ℤ) ^ 2) := by
          refine sum_congr rfl fun i _ => ?_
          push_cast
          ring
        _ = (m : ℤ) ^ 2 - (0 : ℤ) ^ 2 := sum_range_sub (fun i : ℕ => (i : ℤ) ^ 2) m
        _ = _ := by norm_num
    rw [hs, abs_of_nonneg (sq_nonneg (m : ℤ))]
  · have hs : (∑ i ∈ range m, (2 * (i : ℤ) + 1) * (-1 : ℤ) ^ i) = -((m : ℤ) * (-1) ^ m) := by
      calc
        _ = ∑ i ∈ range m, (-(((i + 1 : ℕ) : ℤ) * (-1) ^ (i + 1)) - -((i : ℤ) * (-1) ^ i)) := by
          refine sum_congr rfl fun i _ => ?_
          push_cast
          rw [pow_succ]
          ring
        _ = _ := by simpa using sum_range_sub (fun i : ℕ => -((i : ℤ) * (-1) ^ i)) m
    rw [hs]
    norm_num [abs_mul, abs_pow]

/-- **Bound on the parameter in the weighted power-sum equation for Lucas sequences.** Let $x$
be a positive integer, let $y \in \{1, -1\}$, and let $(U_n)$ be the Lucas sequence with
parameters $(x, y)$, given by $U_0 = 0$, $U_1 = 1$ and $U_{n+2} = x U_{n+1} - y U_n$.
If $n, p, q$ are positive integers and $k \geq 3$ is an integer with
$$
\sum_{j=1}^{k} j \, U_j^p = U_n^q,
$$
then $x \leq (k + 1)^2/4 + 1$.

The hypothesis $k \geq 3$ cannot be dropped entirely: for $k = 1$ and $y = -1$,
$(n, p, q, x) = (1, 1, 1, 5)$ is a solution and $5 > (1 + 1)^2/4 + 1 = 2$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 4.4 (`fq-2024-earplynch07182024-lem-4.4`). -/
public theorem le_of_weighted_power_sum_eq (P : LucasSequenceParams)
    (hy : P.q = 1 ∨ P.q = -1) (hx : 0 < P.p) {n k p q : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hq : 0 < q) (hk : 3 ≤ k)
    (hsol : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j ^ p = lucasU P n ^ q) :
    (P.p : ℚ) ≤ ((k : ℚ) + 1) ^ 2 / 4 + 1 := by
  -- The modular argument also works at index zero; keep the source's positivity hypothesis.
  have _ := hn
  by_cases hxsmall : P.p ≤ 2
  · have hxQ : (P.p : ℚ) ≤ 2 := by exact_mod_cast hxsmall
    have hkQ : (3 : ℚ) ≤ k := by exact_mod_cast hk
    have hk2 := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 4) (show (4 : ℚ) ≤ k + 1 by linarith) 2
    linarith only [hxQ, hk2]
  let m := (k + 1) / 2
  let a := (-P.q) ^ p
  let S := ∑ i ∈ range m, (2 * (i : ℤ) + 1) * a ^ i
  have hS : lucasU P n ^ q ≡ S [ZMOD P.p] := hsol ▸ weighted_lucas_sum_modEq P hp k
  have ha : a = 1 ∨ a = -1 := by
    rcases hy with hy | hy
    · rcases Nat.even_or_odd p with hp' | hp'
      · exact Or.inl (by simp [a, hy, hp'.neg_one_pow])
      · exact Or.inr (by simp [a, hy, hp'.neg_one_pow])
    · exact Or.inl (by simp [a, hy])
  obtain ⟨t, ht, htAbs⟩ : ∃ t : ℤ, lucasU P n ^ q ≡ t [ZMOD P.p] ∧ |t| ≤ 1 := by
    rcases Nat.even_or_odd n with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · refine ⟨0, ?_, by norm_num⟩
      simpa only [← two_mul, zero_pow hq.ne'] using
        (((p_dvd_lucasU_two_mul_and_lucasV_of_odd P).1 i).modEq_zero_int.pow q)
    · refine ⟨((-P.q) ^ i) ^ q, ?_, ?_⟩
      · simpa only [← two_mul] using (lucasU_two_mul_add_one_modEq P i).pow q
      · rcases hy with hy | hy <;> simp [hy, abs_pow]
  have hm : (2 : ℤ) ≤ m := by
    exact_mod_cast (show 2 ≤ m by dsimp [m]; omega)
  have hSmag : 1 < |S| ∧ |S| ≤ (m : ℤ) ^ 2 := by
    have heq : |S| = if a = 1 then (m : ℤ) ^ 2 else m := abs_signed_odd_weight_sum ha m
    rw [heq]
    split <;> constructor <;> nlinarith only [hm, sq_nonneg ((m : ℤ) - 2)]
  have hne : S - t ≠ 0 := by
    intro heq
    rw [sub_eq_zero.mp heq] at hSmag
    exact (not_lt_of_ge htAbs) hSmag.1
  have hd : P.p ∣ S - t := (ht.symm.trans hS).dvd
  have hb : P.p ≤ (m : ℤ) ^ 2 + 1 := calc
    P.p = |P.p| := (abs_of_pos hx).symm
    _ ≤ |S - t| := Int.le_of_dvd (abs_pos.mpr hne) ((abs_dvd _ _).mpr ((dvd_abs _ _).mpr hd))
    _ ≤ |S| + |t| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le S (-t)
    _ ≤ (m : ℤ) ^ 2 + 1 := add_le_add hSmag.2 htAbs
  have hbQ : (P.p : ℚ) ≤ (m : ℚ) ^ 2 + 1 := by exact_mod_cast hb
  have hmQ : 2 * (m : ℚ) ≤ (k : ℚ) + 1 := by
    exact_mod_cast (show 2 * m ≤ k + 1 by dsimp [m]; omega)
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℚ) * m) hmQ 2
  nlinarith only [hbQ, hsq]

end MetaMathlibExt
