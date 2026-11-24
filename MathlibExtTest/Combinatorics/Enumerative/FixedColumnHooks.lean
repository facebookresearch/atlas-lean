/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FixedColumnHooks

namespace MetaMathlibExt.columnHook_size_genFun_limit

open Finset PowerSeries MathlibExt

private noncomputable def normalizedSeries (m n k : ℕ) : ℚ⟦X⟧ :=
  X ^ (m - 1) * (∏ i ∈ range (n + 1), (1 - X ^ (k + i)))⁻¹ *
    ∑ l ∈ Icc 1 k, X ^ ((m - 1) * (k - l)) *
      (∏ i ∈ range (l - 1), (1 - X ^ (m + i))) *
      (qPochFin X (l - 1) * qPochFin X (k - l))⁻¹

-- The positive shift makes the constant term vanish even at the smallest allowed column.
example : ∀ᶠ k in Filter.atTop, coeff 0 (normalizedSeries 2 0 k) = 0 := by
  filter_upwards [columnHook_size_genFun_limit 2 (by decide) 0] with k hk
  exact hk.trans (by simp [coeff_zero_eq_constantCoeff_apply])

-- In column two both denominator factors contribute to the coefficient following the leading one.
example : ∀ᶠ k in Filter.atTop, coeff 2 (normalizedSeries 2 2 k) = 2 := by
  filter_upwards [columnHook_size_genFun_limit 2 (by decide) 2] with k hk
  apply hk.trans
  let D : ℚ⟦X⟧ := (1 - X) * qPochFin X 3
  norm_num only [Nat.reduceSub, pow_one, Nat.reduceAdd]
  change coeff (1 + 1) (X * D⁻¹) = 2
  rw [coeff_succ_X_mul]
  have hD : constantCoeff D = 1 := by simp [D, qPochFin, map_prod]
  have h := congrArg (coeff 1) (PowerSeries.mul_inv_cancel D (by simp [hD]))
  have hlin : coeff 1 D = -2 := by
    norm_num [D, qPochFin_succ, coeff_one_mul, coeff_X_pow, coeff_one]
  change coeff 1 (D * D⁻¹) = coeff 1 (1 : ℚ⟦X⟧) at h
  rw [coeff_one_mul, hlin, constantCoeff_inv, hD] at h
  norm_num [coeff_one] at h
  linarith

end MetaMathlibExt.columnHook_size_genFun_limit

namespace MetaMathlibExt

private def fixedHookCount (n m : ℕ) (h : ℤ) : ℤ :=
  ((Finset.univ : Finset n.Partition).filter (fun p =>
    ((Finset.Icc 1 n).filter (fun r =>
      IsFixedColumnHook p m r h ∧ partitionRowLen p r = m)).Nonempty)).card

-- The same partition qualifies at different rows for opposite shifts.
-- For h = 1 the bottom row disappears; for h = -1 the upper row grows.
private def twoTwos : Nat.Partition 4 := ⟨{2, 2}, by decide, by decide⟩

example : (IsFixedColumnHook twoTwos 2 1 1 ∧ partitionRowLen twoTwos 1 = 2) ∧
    (IsFixedColumnHook twoTwos 2 2 (-1) ∧ partitionRowLen twoTwos 2 = 2) := by
  decide

private def fourTwo : Nat.Partition 6 := ⟨{4, 2}, by decide, by decide⟩

-- The image for h = -1 has just enough long parts to restore the hook in row 2.
example : fourTwo.parts.count 2 = 1 ∧
    Disjoint (Finset.Icc 3 3) fourTwo.parts.toFinset ∧
    (fourTwo.parts.filter (4 ≤ ·)).card = 1 := by
  decide

-- For h = 0 both kinds of row transfer occur, with a unique qualifying row.
private def threeTwos : Nat.Partition 6 := ⟨{2, 2, 2}, by decide, by decide⟩

example : (Finset.Icc 1 6).filter (fun r =>
    IsFixedColumnHook threeTwos 2 r 0 ∧ partitionRowLen threeTwos r = 2) = {2} := by
  decide

-- At weight zero the empty target partition cannot contain the required part.
example : fixedHookCount 2 2 1 = 0 := by
  rw [fixedHookCount, card_fixedColumnHook_part_eq_column 2 2 1 (by decide)]
  decide

-- An empty source and strictly negative target weight take the other branch.
example : fixedHookCount 0 2 1 = 0 := by
  rw [fixedHookCount, card_fixedColumnHook_part_eq_column 0 2 1 (by decide)]
  decide

end MetaMathlibExt
