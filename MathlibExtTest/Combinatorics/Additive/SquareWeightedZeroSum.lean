/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.IntervalCases
import MathlibExt.Combinatorics.Additive.SquareWeightedZeroSum

open MetaMathlibExt

-- `4 = 2 ^ 2` is a nonzero square modulo `5`.
example : (4 : ZMod 5) ∈ squareSet 5 := ⟨by decide, 2, by decide⟩

-- `0 = 0 ^ 2` is a square but is excluded from the nonzero squares, for every modulus.
example (n : ℕ) : (0 : ZMod n) ∉ squareSet n := fun h => h.1 rfl

-- `2` is not a square modulo `5`.
example : (2 : ZMod 5) ∉ squareSet 5 := by
  unfold squareSet
  decide

-- The empty sequence has no weighted zero-sum subsequence: the index set must be nonempty.
example (n : ℕ) (A : Set (ZMod n)) : ¬HasWeightedZeroSumSubseq A ![] := by
  rintro ⟨J, ⟨j, -⟩, -⟩
  exact j.elim0

-- A zero term is a zero-sum subsequence by itself, with the nonzero square weight `1`.
example : HasWeightedZeroSumSubseq (squareSet 5) ![3, 0] :=
  ⟨{1}, Finset.singleton_nonempty 1, fun _ => 1,
    fun _ _ => show (1 : ZMod 5) ∈ squareSet 5 from ⟨by decide, 1, by decide⟩, by simp⟩

-- Not every pair of units works modulo `5`: `1 * 1 + 4 * 1 = 0` with the nonzero squares `1, 4`.
example : HasWeightedZeroSumSubseq (squareSet 5) ![1, 1] := by
  refine ⟨Finset.univ, Finset.univ_nonempty, ![1, 4], ?_, by decide⟩
  intro i _
  fin_cases i
  · exact ⟨by decide, 1, by decide⟩
  · exact ⟨by decide, 2, by decide⟩

-- Explicit units for `n = 15`: `(1, 7)` reduces to `(1, 1)` modulo `3` and to `(1, 2)` modulo `5`,
-- and neither reduction has a square-weighted zero-sum subsequence.
example : IsUnit (7 : ZMod 15) ∧ ∀ p : ℕ, p.Prime → p ∣ 15 →
    ¬HasWeightedZeroSumSubseq (squareSet p)
      (fun i : Fin 2 => (ZMod.cast (![(1 : ZMod 15), 7] i) : ZMod p)) := by
  refine ⟨IsUnit.of_mul_eq_one 13 (by decide), fun p hp hp15 => ?_⟩
  have hp_le : p ≤ 15 := Nat.le_of_dvd (by decide) hp15
  interval_cases p <;> first
    | exact absurd hp (by decide)
    | exact absurd hp15 (by decide)
    | (unfold HasWeightedZeroSumSubseq squareSet; decide)

-- Proposition 17 for `n = 15 = 3 * 5`.
example : ∃ u v : ZMod 15, IsUnit u ∧ IsUnit v ∧
    ∀ p : ℕ, p.Prime → p ∣ 15 →
      ¬HasWeightedZeroSumSubseq (squareSet p)
        (fun i : Fin 2 => (ZMod.cast (![u, v] i) : ZMod p)) :=
  exists_pair_units_avoiding_prime_squareWeights 15 (by decide) (by decide)

-- The base need not be prime. The nonzero term 16 reduces to zero modulo 4².
example : HasWeightedZeroSum (squareSet (4 ^ 4)) (fun _ : Fin 1 => (16 : ZMod (4 ^ 4))) := by
  refine squareWeightedZeroSum_of_reduction_square 4 4 1 (by decide) (by decide)
    (by decide) _ ?_
  refine ⟨fun _ => 1, fun _ => ⟨1, isUnit_one, by simp⟩, ?_⟩
  have hcast : (ZMod.cast (16 : ZMod (4 ^ 4)) : ZMod (4 ^ 2)) = 0 := by decide
  simp [hcast]

-- In `ZMod 12` the sequence `(1, 2)` reduces to `(1, 2)` modulo `3 = 3 ^ 1`, where
-- `1 * 1 + 1 * 2 = 0`, so it has an `S(12)`-weighted zero sum.
example : HasWeightedZeroSum (squareSet 12) ![1, 2] := by
  refine squareWeightedZeroSum_of_primePower_reduction 12 3 1 2 (by decide) (by decide)
    (by decide) ?_ _ ?_
  · rw [show (12 : ℕ) = 3 * 4 by rfl, Nat.factorization_mul (by decide) (by decide)]
    simp [Nat.Prime.factorization_self (by decide : Nat.Prime 3),
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 4)]
  · refine ⟨fun _ => 1, fun _ => show (1 : ZMod (3 ^ 1)) ∈ squareSet (3 ^ 1) from
      ⟨by decide, 1, by decide⟩, ?_⟩
    decide

-- The full power of two in `12` is `4`: the sequence `(1, 3)` reduces to `(1, 3)` modulo `4`,
-- where `1 * 1 + 1 * 3 = 0`.
example : HasWeightedZeroSum (squareSet 12) ![1, 3] := by
  refine squareWeightedZeroSum_of_primePower_reduction 12 2 2 2 (by decide) (by decide)
    (by decide) ?_ _ ?_
  · rw [show (12 : ℕ) = 2 ^ 2 * 3 by rfl, Nat.factorization_mul (by decide) (by decide),
      Nat.factorization_pow]
    simp [Nat.Prime.factorization_self (by decide : Nat.Prime 2),
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3)]
  · refine ⟨fun _ => 1, fun _ => show (1 : ZMod (2 ^ 2)) ∈ squareSet (2 ^ 2) from
      ⟨by decide, 1, by decide⟩, ?_⟩
    decide

open scoped Pointwise

-- Positive scaling at an odd prime: the reduced unit squares are exactly `1`, `4`, and `7`.
example : ((9 : ZMod 81) • unitSquareSet 81).ncard = 3 := by
  have hunit (u : ZMod 9) : IsUnit u ↔ u.val.Coprime 9 := by
    rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
  have htab : ∀ x : ZMod 9,
      (∃ u : ZMod 9, u.val.Coprime 9 ∧ x = u ^ 2) ↔ x ∈ ({1, 4, 7} : Finset (ZMod 9)) := by
    decide +kernel
  have hs : unitSquareSet 9 = (({1, 4, 7} : Finset (ZMod 9)) : Set (ZMod 9)) := by
    ext x
    simpa only [unitSquareSet, Set.mem_ofPred_eq, hunit, Finset.mem_coe] using htab x
  have h := ncard_scale_unitSquares_primePower 3 4 1 (by decide) (by decide)
  change ((9 : ZMod 81) • unitSquareSet 81).ncard = (unitSquareSet 9).ncard at h
  calc
    _ = (unitSquareSet 9).ncard := h
    _ = 3 := by
      simpa only [hs, Set.ncard_coe_finset] using
        (show ({1, 4, 7} : Finset (ZMod 9)).card = 3 by decide)

-- The largest allowed scale at an even prime reduces to modulus two.
example : ((4 : ZMod 8) • unitSquareSet 8).ncard = (unitSquareSet 2).ncard :=
  ncard_scale_unitSquares_primePower 2 3 1 (by decide) (by decide)

-- The zero exponent and zero scale reduce to the identity on residues modulo one.
example : ((1 : ZMod 1) • unitSquareSet 1).ncard = (unitSquareSet 1).ncard :=
  ncard_scale_unitSquares_primePower 2 0 0 (by decide) (by decide)

private theorem hasBlock_singleton_iff {n k : ℕ} (c : ZMod n) (S : Fin k → ZMod n) :
    HasConsecutiveWeightedZeroSumSubseq ({c} : Set (ZMod n)) S ↔
      ∃ s t : Fin k, s ≤ t ∧ ∑ i ∈ Finset.Icc s t, c * S i = 0 := by
  rw [hasConsecutiveWeightedZeroSumSubseq_iff]
  constructor
  · rintro ⟨s, t, hst, a, ha, hsum⟩
    refine ⟨s, t, hst, (Finset.sum_congr rfl fun i hi => ?_).trans hsum⟩
    rw [Set.mem_singleton_iff.mp (ha i hi)]
  · rintro ⟨s, t, hst, hsum⟩
    exact ⟨s, t, hst, fun _ => c, fun _ _ => Set.mem_singleton c, hsum⟩

private theorem one_not_forcing_squareSet (n : ℕ) :
    1 ∉ weightedConsecutiveDefiningSet n (squareSet n) := by
  intro h
  obtain ⟨s, t, _, a, ha, hsum⟩ := hasConsecutiveWeightedZeroSumSubseq_iff.mp
    ((mem_weightedConsecutiveDefiningSet.mp h).2 (fun _ => 1))
  have hst : t = s := Subsingleton.elim _ _
  subst t
  have hz : a s = 0 := by simpa using hsum
  exact (mem_squareSet_iff.mp (ha s (by simp))).1 hz

private theorem square_weighted_constant_three : weightedConsecutiveConstant 3 (squareSet 3) = 3 := by
  have hA : squareSet 3 = ({1} : Set (ZMod 3)) := by
    ext x
    rw [mem_squareSet_iff, Set.mem_singleton_iff]
    exact (show ∀ x : ZMod 3, (x ≠ 0 ∧ ∃ y : ZMod 3, x = y ^ 2) ↔ x = 1 from by decide) x
  apply (weightedConsecutiveConstant_eq_iff_isLeast (by decide)).mpr
  constructor
  · rw [hA, mem_weightedConsecutiveDefiningSet]
    refine ⟨by decide, fun S => (hasBlock_singleton_iff 1 S).mpr ?_⟩
    exact (show ∀ S : Fin 3 → ZMod 3,
      ∃ s t : Fin 3, s ≤ t ∧ ∑ i ∈ Finset.Icc s t, 1 * S i = 0 from by decide) S
  · intro k hk
    have hpos := (mem_weightedConsecutiveDefiningSet.mp hk).1
    have hne₁ : k ≠ 1 := fun h => one_not_forcing_squareSet 3 (h ▸ hk)
    have hne₂ : k ≠ 2 := by
      rintro rfl
      rw [hA, mem_weightedConsecutiveDefiningSet] at hk
      have h := (hasBlock_singleton_iff 1 (![1, 1] : Fin 2 → ZMod 3)).mp (hk.2 ![1, 1])
      exact (by decide : ¬∃ s t : Fin 2, s ≤ t ∧
        ∑ i ∈ Finset.Icc s t, (1 : ZMod 3) * ![1, 1] i = 0) h
    omega

private theorem square_weighted_constant_six : weightedConsecutiveConstant 6 (squareSet 6) = 2 := by
  apply (weightedConsecutiveConstant_eq_iff_isLeast (by decide)).mpr
  constructor
  · apply mem_weightedConsecutiveDefiningSet.mpr
    refine ⟨by decide, fun S => ?_⟩
    obtain ⟨s, t, hst, hsum⟩ := (show ∀ S : Fin 2 → ZMod 6,
      ∃ s t : Fin 2, s ≤ t ∧ ∑ i ∈ Finset.Icc s t, 3 * S i = 0 from by decide) S
    have hw : (3 : ZMod 6) ∈ squareSet 6 := mem_squareSet_iff.mpr ⟨by decide, 3, by decide⟩
    exact hasConsecutiveWeightedZeroSumSubseq_iff.mpr
      ⟨s, t, hst, fun _ => 3, fun _ _ => hw, hsum⟩
  · intro k hk
    have hpos := (mem_weightedConsecutiveDefiningSet.mp hk).1
    have hne : k ≠ 1 := fun h => one_not_forcing_squareSet 6 (h ▸ hk)
    omega

-- Enumerating the short blocks gives strict inequality, independently of Corollary 8.
example : weightedConsecutiveConstant 6 (squareSet 6) < weightedConsecutiveConstant 3 (squareSet 3) := by
  rw [square_weighted_constant_six, square_weighted_constant_three]
  decide

-- The two outer terms sum to zero modulo five, but no contiguous block does with weight one.
example : (1 : ZMod 5) + 4 = 0 ∧
    ¬HasConsecutiveWeightedZeroSumSubseq ({1} : Set (ZMod 5)) ![1, 2, 4] := by
  refine ⟨by decide, ?_⟩
  rw [hasBlock_singleton_iff]
  decide

-- In both moduli the same block at indices 1 and 2 works; the lifted weight is 9 = 3².
example :
    HasConsecutiveWeightedZeroSumSubseq (squareSet 4)
        (fun i => (ZMod.cast ((![2, 1, 3] : Fin 3 → ZMod 12) i) : ZMod 4)) ∧
      HasConsecutiveWeightedZeroSumSubseq (squareSet 12) ![2, 1, 3] := by
  have h₁ : (1 : ZMod 4) ∈ squareSet 4 := mem_squareSet_iff.mpr ⟨by decide, 1, by decide⟩
  have h₉ : (9 : ZMod 12) ∈ squareSet 12 := mem_squareSet_iff.mpr ⟨by decide, 3, by decide⟩
  exact ⟨hasConsecutiveWeightedZeroSumSubseq_iff.mpr
      ⟨1, 2, by decide, fun _ => 1, fun _ _ => h₁, by decide⟩,
    hasConsecutiveWeightedZeroSumSubseq_iff.mpr
      ⟨1, 2, by decide, fun _ => 9, fun _ _ => h₉, by decide⟩⟩

-- Client check with the full power 2², not just the prime 2.
example : weightedConsecutiveConstant 12 (squareSet 12) ≤ weightedConsecutiveConstant 4 (squareSet 4) := by
  apply weightedConsecutiveConstant_squareSet_le_primePower 12 2 2 (by decide) (by decide)
    (by decide)
  rw [show (12 : ℕ) = 2 ^ 2 * 3 by rfl, Nat.factorization_mul (by decide) (by decide),
    Nat.factorization_pow]
  simp [Nat.Prime.factorization_self (by decide : Nat.Prime 2),
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3)]
