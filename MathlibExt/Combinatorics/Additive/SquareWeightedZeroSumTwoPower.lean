/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.SquareWeightedZeroSum
import all MathlibExt.Combinatorics.Additive.SquareSetPrimePowerCount
import Mathlib.Algebra.Ring.Parity

/-!
# A square-weighted zero-sum obstruction modulo even powers of two

For a positive even exponent $r$, three units modulo $2^r$ that all reduce to $1$ modulo $4$
have no nonempty subsequence with a zero sum weighted by nonzero squares.

## References

* Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
  Sequences 27 (2024), Article 24.6.6, pp. 1–16, Lemma 10 (pp. 5–6), using Lemma 4 (p. 3).
* The prime-power decomposition is reused from `squareSet_eq_iUnion_scaled_unitSquares` in
  `MathlibExt.Combinatorics.Additive.SquareSetPrimePowerCount`.
-/

namespace MetaMathlibExt

open scoped Pointwise

-- Keep the source's unit hypothesis even though the reduction hypothesis suffices.
set_option linter.unusedVariables false in
/-- **Square-weighted zero-sum free unit triples modulo even powers of two.** Let $r$ be a nonzero
even natural number, and let $x_1, x_2, x_3$ be units of $\mathbb{Z}_{2^r}$ that are each
congruent to $1$ modulo $4$. Write $S(2^r)$ for the set of nonzero squares in $\mathbb{Z}_{2^r}$.
Then $(x_1, x_2, x_3)$ has no $S(2^r)$-weighted zero-sum subsequence: there are no non-empty set
$J$ of indices and weights $a_j \in S(2^r)$ for $j \in J$ with $\sum_{j \in J} a_j x_j = 0$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 10. -/
public theorem no_squareWeightedSubseq_three_units_twoPower (r : ℕ)
    (hr0 : r ≠ 0) (hrEven : Even r) (S : Fin 3 → ZMod (2 ^ r))
    (hunit : ∀ i, IsUnit (S i))
    (hred : ∀ i, (ZMod.cast (S i) : ZMod 4) = 1) :
    ¬HasWeightedZeroSumSubseq (squareSet (2 ^ r)) S := by
  classical
  have hr := Nat.pos_of_ne_zero hr0
  have : NeZero (2 ^ r) := ⟨pow_ne_zero r (by decide)⟩
  rintro ⟨J, hJ, a, ha, hsum⟩
  have hdecomp (i : J) : ∃ (k : ℕ) (u : ZMod (2 ^ r)),
      2 * k < r ∧ IsUnit u ∧ a i = (2 : ZMod (2 ^ r)) ^ (2 * k) * u ^ 2 := by
    have hi := ha i i.property
    rw [squareSet_eq_iUnion_scaled_unitSquares Nat.prime_two hr, Set.mem_iUnion] at hi
    obtain ⟨k, hk⟩ := hi
    obtain ⟨_, ⟨u, hu, rfl⟩, hku⟩ := Set.mem_smul_set.mp hk
    exact ⟨k, u, by omega, hu, hku.symm⟩
  choose k u hk hu hw using hdecomp
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image J.attach k (Finset.attach_nonempty_iff.mpr hJ)
  have hle (i : J) : k i₀ ≤ k i := hmin i (Finset.mem_attach J i)
  let B := ∑ i ∈ J.attach, 2 ^ (2 * (k i - k i₀)) * (u i).val ^ 2 * (S i).val
  -- Factor out the least power of two in natural representatives before cancelling.
  have hB : ((2 ^ (2 * k i₀) * B : ℕ) : ZMod (2 ^ r)) = 0 := by
    simp only [B, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sum,
      ZMod.natCast_zmod_val, Finset.mul_sum]
    rw [← Finset.sum_attach] at hsum
    refine (Finset.sum_congr rfl fun i _ => ?_).trans hsum
    rw [← mul_assoc, ← mul_assoc, ← pow_add, show 2 * k i₀ + 2 * (k i - k i₀) = 2 * k i by
      have := hle i
      omega, hw i]
  have h4B : 4 ∣ B := by
    have hbound : 2 * k i₀ + 2 ≤ r := by
      obtain ⟨q, hq⟩ := hrEven
      have := hk i₀
      omega
    have hd := (pow_dvd_pow 2 hbound).trans ((ZMod.natCast_eq_zero_iff _ _).mp hB)
    rw [pow_add, show (2 : ℕ) ^ 2 = 4 by decide] at hd
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos (by decide) _) hd
  have hsq (i : J) : ((u i).val : ZMod 4) ^ 2 = 1 := by
    have hodd : Odd (u i).val := by
      apply Nat.not_even_iff_odd.mp
      rw [even_iff_two_dvd]
      exact (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two hr).mp
        (by simpa only [ZMod.natCast_zmod_val] using hu i)
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff, Nat.ModEq.comm]
    exact Nat.modEq_of_dvd' (Nat.one_le_pow _ _ hodd.pos)
      (dvd_trans (by decide : 4 ∣ 8) (Nat.eight_dvd_sq_sub_one_of_odd hodd))
  -- Modulo four, each minimum contributes one and every other term contributes zero.
  let I := J.attach.filter fun i => k i = k i₀
  have hcount : (B : ZMod 4) = (I.card : ZMod 4) := by
    simp only [B, I, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : k i = k i₀
    · rw [ite_eq_left hi, show k i - k i₀ = 0 by omega, mul_zero, pow_zero, one_mul, hsq i, one_mul]
      simpa only [ZMod.cast_eq_val] using hred i
    · obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (show k i - k i₀ ≠ 0 by
        have := hle i
        omega)
      rw [ite_eq_right hi, hd, Nat.mul_succ, pow_add, show (2 : ZMod 4) ^ 2 = 0 by decide,
        mul_zero, zero_mul, zero_mul]
  have hpos : 0 < I.card := Finset.card_pos.mpr ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, rfl⟩⟩
  have hcard : I.card ≤ 3 := calc
    _ ≤ J.attach.card := Finset.card_filter_le _ _
    _ = J.card := Finset.card_attach
    _ ≤ 3 := by simpa only [Fintype.card_fin] using J.card_le_univ
  have hd : 4 ∣ I.card := (ZMod.natCast_eq_zero_iff _ _).mp
    (hcount ▸ (ZMod.natCast_eq_zero_iff _ _).mpr h4B)
  exact (by omega : ¬ 4 ≤ I.card) (Nat.le_of_dvd hpos hd)

end MetaMathlibExt
