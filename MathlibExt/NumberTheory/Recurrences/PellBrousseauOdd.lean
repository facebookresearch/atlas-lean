/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PellNumberSequence
public import MathlibExt.NumberTheory.Recurrences.KFibonacciBrousseauSums
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.Recurrences.Internal.BrousseauSum
import MathlibExt.NumberTheory.Recurrences.SubsequenceSecondOrderRecurrence

/-! # Brousseau sums of Pell numbers along odd multiples -/

namespace MetaMathlibExt

namespace pell_brousseau_sum_mul_odd

private lemma pellLucas_pos (m : ℕ) : 0 < lucasV ⟨2, -1, by decide⟩ m := by
  induction m using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more m ih₀ ih₁ =>
    change 0 < (2 : ℤ) * lucasV ⟨2, -1, by decide⟩ (m + 1) -
      (-1) * lucasV ⟨2, -1, by decide⟩ m
    simpa only [neg_one_mul, sub_neg_eq_add] using add_pos (mul_pos (by decide) ih₁) ih₀

-- For an odd stride, the power of the second Lucas parameter is still −1.
private lemma pell_step (m : ℕ) (hm : Odd m) (n : ℕ) :
    (pellNumber (m * (n + 2)) : ℚ) =
      (lucasV ⟨2, -1, by decide⟩ m : ℚ) * pellNumber (m * (n + 1)) + pellNumber (m * n) := by
  let params : LucasSequenceParams := ⟨2, -1, by decide⟩
  let w (i : ℕ) : ℤ := pellNumber i
  have hw (i : ℕ) : w (i + 2) = params.p * w (i + 1) - params.q * w i := by
    change (pellNumber (i + 2) : ℤ) = 2 * pellNumber (i + 1) - (-1) * pellNumber i
    rw [pellNumber]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, neg_one_mul, sub_neg_eq_add]
  have hm_pos : 0 < m := by
    obtain ⟨j, hj⟩ := hm
    omega
  have h := (subsequence_secondOrderRecurrence params w hw m 0 hm_pos).1 n
  change (pellNumber (m * (n + 2) + 0) : ℤ) =
    lucasV params m * pellNumber (m * (n + 1) + 0) - (-1 : ℤ) ^ m * pellNumber (m * n + 0) at h
  simp only [Nat.add_zero, hm.neg_one_pow, neg_one_mul, sub_neg_eq_add] at h
  exact_mod_cast h

end pell_brousseau_sum_mul_odd

@[expose] public section

set_option backward.proofsInPublic true in
/-- **Power-weighted Pell sums along odd multiples.** Let $P_n$ be the Pell numbers and $Q_n$ the
Pell–Lucas numbers, the Lucas sequence $V(2, -1)$: $Q_0 = Q_1 = 2$ and
$Q_{n+2} = 2 Q_{n+1} + Q_n$. Let $m$ be an odd natural number and write $k = Q_m$. Let
$A_k^{(0)} = 1$ and
$A_k^{(p)} = \frac{2}{k} \sum_{j=1}^{\lceil p/2 \rceil} \binom{p}{2j-1} A_k^{(p-2j+1)}$ for
$p \ge 1$, and let $C_k^{(p)}(x) = \sum_{r=0}^{p} (-1)^r A_k^{(r)} \binom{p}{r} x^{p-r}$, with
$0^0 = 1$. Then for all natural numbers $n$ and $p$,
$$
Q_m \sum_{i=1}^{n} i^p P_{mi} = C_k^{(p)}(n) P_{m(n+1)} + C_k^{(p)}(n+1) P_{mn} -
C_k^{(p)}(0) P_m.
$$

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Corollary 10
(`jis-2024-24.6.4-cor-10`). -/
theorem pell_brousseau_sum_mul_odd (m : ℕ) (hm : Odd m) (n p : ℕ) :
    (lucasV ⟨2, -1, by decide⟩ m : ℚ) * ∑ i ∈ Finset.Icc 1 n, (i : ℚ) ^ p * pellNumber (m * i) =
      brousseauCoeff (lucasV ⟨2, -1, by decide⟩ m) p n * pellNumber (m * (n + 1)) +
        brousseauCoeff (lucasV ⟨2, -1, by decide⟩ m) p (n + 1) * pellNumber (m * n) -
        brousseauCoeff (lucasV ⟨2, -1, by decide⟩ m) p 0 * pellNumber m := by
  let k := (lucasV ⟨2, -1, by decide⟩ m : ℚ)
  have hk : k ≠ 0 := by
    change (lucasV ⟨2, -1, by decide⟩ m : ℚ) ≠ 0
    exact_mod_cast (pell_brousseau_sum_mul_odd.pellLucas_pos m).ne'
  let P (i : ℕ) : ℚ := pellNumber (m * i)
  let C := brousseauCoeff k p
  let T (i : ℕ) : ℚ := C i * P (i + 1) + C (i + 1) * P i
  have hT0 : T 0 = C 0 * pellNumber m := by simp [T, P, pellNumber]
  have hstep (i : ℕ) : k * ((i + 1 : ℕ) : ℚ) ^ p * P (i + 1) = T (i + 1) - T i := by
    have hC : k * C ((i : ℚ) + 1) + C ((i : ℚ) + 1 + 1) - C i =
        k * ((i : ℚ) + 1) ^ p := by
      simpa only [C, add_sub_cancel_right] using BrousseauSum.coeff_shift k hk p ((i : ℚ) + 1)
    have hP : P (i + 2) = k * P (i + 1) + P i := pell_brousseau_sum_mul_odd.pell_step m hm i
    simp only [T, Nat.cast_add_one]
    rw [hP]
    linear_combination -P (i + 1) * hC
  change k * ∑ i ∈ Finset.Icc 1 n, (i : ℚ) ^ p * P i = T n - C 0 * pellNumber m
  rw [← hT0, Finset.mul_sum]
  calc
    _ = ∑ i ∈ Finset.Ico 0 n, k * ((i + 1 : ℕ) : ℚ) ^ p * P (i + 1) := by
      simp_rw [← mul_assoc]
      rw [Finset.sum_Ico_add' (fun i : ℕ ↦ k * (i : ℚ) ^ p * P i), Nat.zero_add,
        Finset.Ico_add_one_right_eq_Icc]
    _ = ∑ i ∈ Finset.Ico 0 n, (T (i + 1) - T i) := Finset.sum_congr rfl fun i _ ↦ hstep i
    _ = _ := Finset.sum_Ico_sub T (Nat.zero_le n)

end

end MetaMathlibExt
