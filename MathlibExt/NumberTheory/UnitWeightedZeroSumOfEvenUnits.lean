/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Nat

/-!
# Unit-weighted zero sums modulo a power of two

Luca's lemma gives unit weights that make a whole sequence sum to zero whenever it contains
a positive even number of units.
-/

namespace MetaMathlibExt

/-- **Luca's lemma on unit-weighted zero sums modulo $2^r$.** Let $r$ and $k$ be natural numbers
and let $x_1, \dots, x_k \in \mathbb{Z}/2^r\mathbb{Z}$. If the number of indices $j$ for which
$x_j$ is a unit is even and nonzero, then there are units $a_1, \dots, a_k$ of
$\mathbb{Z}/2^r\mathbb{Z}$ with $a_1 x_1 + \dots + a_k x_k = 0$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 6.5 (`integers-2024-A38-lem-6-5`). -/
public theorem unitWeightedZeroSum_of_even_units {r k : ℕ} (x : Fin k → ZMod (2 ^ r))
    (h0 : (Finset.univ.filter fun j => IsUnit (x j)).card ≠ 0)
    (he : Even (Finset.univ.filter fun j => IsUnit (x j)).card) :
    ∃ a : Fin k → ZMod (2 ^ r), (∀ i, IsUnit (a i)) ∧ ∑ i, a i * x i = 0 := by
  cases r with
  | zero =>
    have : Subsingleton (ZMod (2 ^ 0)) := by
      rw [pow_zero]
      infer_instance
    exact ⟨fun _ => 1, fun _ => isUnit_one, Subsingleton.elim _ _⟩
  | succ r =>
    have unit_iff (n : ℕ) : IsUnit (n : ZMod (2 ^ (r + 1))) ↔ Odd n := by
      rw [ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two (Nat.succ_pos r),
        ← even_iff_two_dvd, Nat.not_even_iff_odd]
    obtain ⟨i, hi⟩ := Finset.card_ne_zero.mp h0
    have hui := (Finset.mem_filter.mp hi).2
    have hx (j : Fin k) : IsUnit (x j) ↔ Odd (x j).val := by
      simpa using unit_iff (x j).val
    have hsum : Even (∑ j, (x j).val) := by
      rw [Finset.even_sum_iff_even_card_odd]
      simpa only [hx] using he
    -- Removing the chosen unit leaves an odd sum, hence a unit modulo the power of two.
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Nat.even_add'] at hsum
    have hrest : IsUnit (∑ j ∈ Finset.univ.erase i, x j) := by
      simpa only [Nat.cast_sum, ZMod.natCast_zmod_val] using
        (unit_iff _).2 (hsum.mp ((hx i).mp hui))
    let a (j : Fin k) : (ZMod (2 ^ (r + 1)))ˣ :=
      if j = i then -hrest.unit / hui.unit else 1
    refine ⟨fun j => a j, fun j => (a j).isUnit, ?_⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have htail : ∑ j ∈ Finset.univ.erase i, (a j : ZMod (2 ^ (r + 1))) * x j =
        ∑ j ∈ Finset.univ.erase i, x j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [a, (Finset.mem_erase.mp hj).1]
    rw [htail]
    simp [a, div_eq_mul_inv, mul_assoc, hui.val_inv_mul]

end MetaMathlibExt
