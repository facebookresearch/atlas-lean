/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The statement formulation is adapted from `lean/ComparatorChallenges/EgyptianFractions.lean`
in OpenAI's `openai/math` repository (https://github.com/openai/math), revision
`3344da59991ed94f9ba711217b29c1d760badfa6`, under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). The source file carries no copyright notice
and names no individual authors. No source Lean proof is included.
Authors: OpenAI (project attribution in lean/formalization.yaml).
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Finset.Fin

/-!
# Short Egyptian fractions

If a strictly increasing `k`-tuple of positive integer denominators has reciprocal sum `1`,
its denominator at each zero-based index `i` is at most `k ^ (2 ^ i.val)`.

## References

* OpenAI, [*Short Egyptian fractions*](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Short-Egyptian-fractions-September-25-2026/Short-Egyptian-fractions-September-25-2026.pdf),
  preprint, September 25, 2026, §6, p. 24, the pointwise bound in the proof of Corollary 1.2.
* OpenAI, [`OAI.Problem337.one_expansions_finite_and_bounded`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L64-L69),
  second conjunct, with `IsOneExpansion` defined on lines 25–27.
-/

open scoped BigOperators

namespace EgyptianFraction

private theorem denominator_le_mul_prefix {k : ℕ} {n : Fin k → ℕ}
    (hn : ∀ i, 1 ≤ n i) (hmono : StrictMono n) (hsum : (∑ i : Fin k, (1 : ℚ) / n i) = 1)
    (i : Fin k) : n i ≤ k * ∏ j ∈ Finset.Iio i, n j := by
  let s := Finset.Iio i
  let t := Finset.univ \ s
  let P : ℕ := ∏ j ∈ s, n j
  let R : ℚ := ∑ j ∈ t, (1 : ℚ) / n j
  have hnpos (j : Fin k) : 0 < (n j : ℚ) := by exact_mod_cast hn j
  have hP : 0 < (P : ℚ) := by
    exact_mod_cast Finset.prod_pos (fun j _ ↦ hn j : ∀ j ∈ s, 0 < n j)
  have hi : i ∈ t := by simp [t, s]
  have hR : 0 < R := Finset.sum_pos (fun j _ ↦ one_div_pos.mpr (hnpos j)) ⟨i, hi⟩
  have hsplit : R + (∑ j ∈ s, (1 : ℚ) / n j) = 1 :=
    (Finset.sum_sdiff (Finset.subset_univ s)).trans hsum
  -- The product of the prefix denominators clears every denominator in the prefix sum.
  let N : ℤ := (P : ℤ) - ∑ j ∈ s, (↑(∏ a ∈ s.erase j, n a : ℕ) : ℤ)
  have hclear : (P : ℚ) * R = (N : ℚ) := by
    dsimp only [N]
    rw [show R = 1 - ∑ j ∈ s, (1 : ℚ) / n j from eq_sub_of_add_eq hsplit,
      mul_sub, mul_one, Finset.mul_sum, Int.cast_sub, Int.cast_sum]
    simp only [Int.cast_natCast]
    congr 1
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    change ((∏ a ∈ s, n a : ℕ) : ℚ) * _ = _
    rw [← Finset.prod_erase_mul s n hj, Nat.cast_mul, mul_assoc, mul_one_div_cancel (hnpos j).ne',
      mul_one]
  have hN : 0 < N := by
    exact_mod_cast (hclear ▸ mul_pos hP hR)
  have hRlower : (1 : ℚ) ≤ (P : ℚ) * R := by
    rw [hclear]
    exact_mod_cast (show (1 : ℤ) ≤ N from hN)
  have hRupper : R ≤ (k : ℚ) / n i := by
    calc
      R ≤ ∑ _j ∈ t, (1 : ℚ) / n i := by
        refine Finset.sum_le_sum fun j hj ↦ one_div_le_one_div_of_le (hnpos i) ?_
        have hij : i ≤ j := by simpa [t, s, not_lt] using hj
        exact_mod_cast hmono.monotone hij
      _ ≤ (k : ℚ) / n i := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
        exact div_le_div_of_nonneg_right (by exact_mod_cast card_finset_fin_le t)
          (hnpos i).le
  have hbound : (1 : ℚ) ≤ ((k : ℚ) * (P : ℚ)) / n i := by
    calc
      1 ≤ (P : ℚ) * R := hRlower
      _ ≤ (P : ℚ) * ((k : ℚ) / n i) := mul_le_mul_of_nonneg_left hRupper hP.le
      _ = ((k : ℚ) * (P : ℚ)) / n i := by rw [← mul_div_assoc, mul_comm (P : ℚ) (k : ℚ)]
  have hcast : (n i : ℚ) ≤ (k : ℚ) * (P : ℚ) := by
    simpa only [one_mul] using (le_div_iff₀ (hnpos i)).mp hbound
  exact_mod_cast hcast

/-- **Pointwise denominator bounds for an Egyptian expansion of one.** Suppose a strictly
increasing $k$-tuple of positive integer denominators has reciprocal sum $1$. The denominator
at index $i$ is at most $k^{2^i}$, with indices starting at $0$.

Source: [*Short Egyptian fractions*, pointwise denominator bound](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L64-L70). -/
public theorem denominator_le_pow_in_expansion_one {k : ℕ} {n : Fin k → ℕ}
    (hn : ∀ i, 1 ≤ n i) (hmono : StrictMono n) (hsum : (∑ i : Fin k, (1 : ℚ) / n i) = 1)
    (i : Fin k) : n i ≤ k ^ (2 ^ i.val) := by
  cases k with
  | zero => exact i.elim0
  | succ k =>
    let P (j : Fin (k + 1)) : ℕ := (k + 1) * ∏ a ∈ Finset.Iio j, n a
    have hle (j : Fin (k + 1)) : n j ≤ P j := denominator_le_mul_prefix hn hmono hsum j
    refine (hle i).trans ?_
    -- The scaled prefix product starts at k + 1 and grows by at most squaring.
    induction i using Fin.induction with
    | zero =>
      have hzero : Finset.Iio (0 : Fin (k + 1)) = ∅ := Finset.Iio_bot
      simp [P, hzero]
    | succ j ih =>
      have hin : Finset.Iio j.succ = insert j.castSucc (Finset.Iio j.castSucc) := by
        rw [Finset.insert_Iio]
        ext a
        simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_def, Fin.le_def,
          Fin.val_succ, Fin.val_castSucc]
        omega
      calc
        P j.succ = P j.castSucc * n j.castSucc := by
          simp only [P, hin, Finset.prod_insert (by simp : j.castSucc ∉ Finset.Iio j.castSucc)]
          rw [mul_comm (n j.castSucc), ← mul_assoc]
        _ ≤ (P j.castSucc) ^ 2 := by
          rw [pow_two]
          exact Nat.mul_le_mul_left _ (hle j.castSucc)
        _ ≤ ((k + 1) ^ (2 ^ j.castSucc.val)) ^ 2 := Nat.pow_le_pow_left ih 2
        _ = (k + 1) ^ (2 ^ j.succ.val) := by
          rw [← pow_mul, Fin.val_castSucc, Fin.val_succ, pow_succ (2 : ℕ) j.val]

end EgyptianFraction
