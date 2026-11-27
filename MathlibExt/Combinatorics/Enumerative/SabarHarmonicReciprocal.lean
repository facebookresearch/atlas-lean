/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SabarTriangle
import MathlibExt.Combinatorics.Enumerative.FrischReciprocalBinomial
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring

/-!
# Harmonic numbers and reciprocal binomial sums in Sabar's triangle

Expanding the triangular sum by columns gives a finite alternating binomial sum in
each column. Completing the column and applying Frisch's identity with reciprocal
order one cancels the reciprocal binomial terms, leaving the harmonic sum.

## References

- Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
  (2026), Article A27, pp. 1–17, Theorem 2 (pp. 7–8).
- Sabar Taoufik, *A Note on the Difference of Powers and Falling Powers*, International
  Journal of Mathematics and Mathematical Sciences 2021 (2021), Article 5593780, pp. 1–4,
  Section 2 (cited in the published proof of Theorem 2 above).
- H. W. Gould and Jocelyn Quaintance, *On the Binomial Identities of Frisch and Klamkin*,
  Journal of Integer Sequences 19 (2016), Article 16.7.7, pp. 1–4, Section 1, equation (2).
  They credit Ragnar Frisch, *Sur les semi-invariants et moments employés dans l'étude des
  distributions statistiques*, Skrifter utgitt av Det Norske Videnskaps-Akademi i Oslo,
  II. Historisk-Filosofisk Klasse 3 (1926), pp. 1–87.
-/

namespace MetaMathlibExt

@[expose] public section

private theorem sum_alternating_choose_div_sub (n j : ℕ) (hj : j < n) :
    ∑ i ∈ Finset.range (j + 1), (-1 : ℚ) ^ (j - i) * (j.choose i : ℚ) / ((n - i : ℕ) : ℚ) =
      1 / ((n : ℚ) * ((n - 1).choose j : ℚ)) := by
  have h := frisch_alternating_reciprocal_binomial j (n - j) 1 Nat.one_pos (by omega)
  have hchoose : (j + 1) * n.choose (j + 1) = n * (n - 1).choose j := by
    simpa only [show n - 1 + 1 = n by omega, Nat.mul_comm] using
      (Nat.add_one_mul_choose_eq (n - 1) j).symm
  rw [show j + (n - j) = n by omega, show n - j - 1 = n - (j + 1) by omega,
    Nat.choose_symm (show j + 1 ≤ n by omega)] at h
  calc
    _ = ∑ k ∈ Finset.range (j + 1),
          (-1 : ℚ) ^ k * (j.choose k : ℚ) * (((n - j + k).choose 1 : ℕ) : ℚ)⁻¹ := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [show j + 1 - 1 - k = j - k by omega, show j - (j - k) = k by omega,
        Nat.choose_symm (show k ≤ j by omega), show n - (j - k) = n - j + k by omega,
        Nat.choose_one_right, div_eq_mul_inv]
    _ = _ := by
      rw [h, Nat.cast_one, ← one_div, one_div_mul_one_div, ← Nat.cast_succ, ← Nat.cast_mul, hchoose,
        Nat.cast_mul]

/-- **Harmonic numbers from Sabar's triangle.** For every natural number $n \ge 2$, the harmonic
number $H_n = \sum_{k=1}^{n} \frac{1}{k}$ and the entries $s(n-1, i)$ of Sabar's triangle satisfy
$$H_n = \frac{1}{n} \sum_{i=0}^{n-1} \binom{n-1}{i}^{-1} +
\sum_{i=0}^{n-2} \frac{(-1)^{n-i} \, s(n-1, i)}{n-i}.$$

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Theorem 2 (`integers-2026-A27-thm-2`). -/
public theorem harmonic_eq_sum_inv_choose_add_sum_sabarNumber (n : ℕ) (hn : 2 ≤ n) :
    harmonic n =
      (1 / (n : ℚ)) * ∑ i ∈ Finset.range n, 1 / ((n - 1).choose i : ℚ) +
        ∑ i ∈ Finset.range (n - 1), (-1 : ℚ) ^ (n - i) * sabarNumber (n - 1) i / ((n - i : ℕ) : ℚ)
    := by
  have hexpand (i : ℕ) :
      (-1 : ℚ) ^ (n - i) * sabarNumber (n - 1) i / ((n - i : ℕ) : ℚ) =
        ∑ j ∈ Finset.Ioc i (n - 1),
          -((-1 : ℚ) ^ (j - i) * (j.choose i : ℚ) / ((n - i : ℕ) : ℚ)) := by
    simp only [sabarNumber]
    push_cast
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ioc] at hj
    have hsign : (-1 : ℚ) ^ (n - i) * (-1) ^ (n - 1 - j) = -((-1) ^ (j - i)) := by
      rw [← pow_add, show n - i + (n - 1 - j) = (j - i) + 2 * (n - 1 - j) + 1 by omega,
        pow_succ, pow_add, pow_mul]
      norm_num
    rw [← mul_assoc, hsign, neg_mul, neg_div]
  rw [Finset.sum_congr rfl (fun i _ => hexpand i),
    Finset.sum_comm' (t' := Finset.range n) (s' := Finset.range) (by
      intro i j
      simp only [Finset.mem_range, Finset.mem_Ioc]
      omega)]
  have hcolumn (j : ℕ) (hj : j ∈ Finset.range n) :
      ∑ i ∈ Finset.range j, -((-1 : ℚ) ^ (j - i) * (j.choose i : ℚ) / ((n - i : ℕ) : ℚ)) =
        1 / ((n - j : ℕ) : ℚ) - 1 / ((n : ℚ) * ((n - 1).choose j : ℚ)) := by
    rw [← sum_alternating_choose_div_sub n j (Finset.mem_range.mp hj), Finset.sum_range_succ,
      Finset.sum_neg_distrib]
    simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul]
    ring
  rw [Finset.sum_congr rfl hcolumn, Finset.sum_sub_distrib, Finset.mul_sum]
  simp_rw [one_div_mul_one_div]
  rw [add_sub_cancel]
  unfold harmonic
  rw [← Finset.sum_range_reflect (fun k => (1 : ℚ) / ((n - k : ℕ) : ℚ))]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show n - (n - 1 - k) = k + 1 by omega, one_div]

end

end MetaMathlibExt
