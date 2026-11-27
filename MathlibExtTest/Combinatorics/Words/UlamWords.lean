/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.UlamWords

namespace MetaMathlibExt.isUlamWord_three_ones_zeros_iff

-- The two-letter word 10 needs both levels of the fuel-bounded test.
example : ulamWordAux 1 [true, false] = false ∧ ulamWordAux 2 [true, false] = true := by
  decide

-- Direct computation at the lower bound and in each of the next three residue classes.
example :
    ¬IsUlamWord [true, true, true] ∧
      IsUlamWord [true, true, true, false] ∧
      IsUlamWord [true, true, true, false, false] ∧
      ¬IsUlamWord [true, true, true, false, false, false] := by
  decide

-- The criterion also applies to words of symbolic length.
example (k : ℕ) : IsUlamWord (List.replicate 3 true ++ List.replicate (4 * k + 1) false) := by
  apply (isUlamWord_three_ones_zeros_iff (4 * k + 4) (by omega)).2
  omega

end MetaMathlibExt.isUlamWord_three_ones_zeros_iff

namespace MetaMathlibExt.isUlamWord_map_not_and_ulamResidueCount_eq

-- The complement of the Ulam word 0001 is the Ulam word 1110, of binary value 14.
example : IsUlamWord [true, true, true, false] ∧
    Nat.ofDigits 2 ([true, true, true, false].reverse.map Bool.toNat) = 14 := by
  obtain ⟨hw, hsum⟩ := isUlamWord_map_not_and_ulamResidueCount_eq.1 _
    isUlamWord_length_four_examples.1
  refine ⟨hw, ?_⟩
  change Nat.ofDigits 2 ([true, true, true, false].reverse.map Bool.toNat) + 1 = 15 at hsum
  omega

-- Modulus zero pairs exact integer values, including classes outside the binary range.
example (a : ZMod 0) : ulamResidueCount 0 4 a = ulamResidueCount 0 4 (15 - a) :=
  isUlamWord_map_not_and_ulamResidueCount_eq.2 0 4 a

end MetaMathlibExt.isUlamWord_map_not_and_ulamResidueCount_eq

namespace MetaMathlibExt.ulamResidueCount_mod_two_three

-- At the minimum length both parities occur, and the third residue modulo 3 is absent.
example : ulamResidueCount 2 1 0 = 1 ∧ ulamResidueCount 2 1 1 = 1 ∧
    ulamResidueCount 3 1 0 = 1 ∧ ulamResidueCount 3 1 1 = 1 ∧ ulamResidueCount 3 1 2 = 0 := by
  decide

-- Complementation exchanges 1 and 2 modulo 3 at positive even lengths.
example (k : ℕ) (hk : 0 < k) : ulamResidueCount 3 (2 * k) 1 = ulamResidueCount 3 (2 * k) 2 := by
  simpa only [ite_eq_left (even_two_mul k), show -(1 : ZMod 3) = 2 by decide] using
    (ulamResidueCount_mod_two_three (2 * k) (by omega)).2 1

-- At odd lengths it exchanges 0 and 1 instead.
example (k : ℕ) : ulamResidueCount 3 (2 * k + 1) 0 = ulamResidueCount 3 (2 * k + 1) 1 := by
  simpa using (ulamResidueCount_mod_two_three (2 * k + 1) (by omega)).2 0

end MetaMathlibExt.ulamResidueCount_mod_two_three

namespace MetaMathlibExt.isUlamWord_zeros_four_ones_zeros_iff

-- One zero gives a unique split at either boundary. A zero on each side gives several splits.
example : IsUlamWord [false, true, true, true, true] ∧
    IsUlamWord [true, true, true, true, false] ∧
    ¬IsUlamWord [false, true, true, true, true, false] := by
  decide

-- Five zeros split between the two sides give the first two-sided positive case.
example : IsUlamWord [false, false, true, true, true, true, false, false, false] := by
  decide

example (k : ℕ) :
    IsUlamWord (List.replicate (4 * k + 2) false ++ List.replicate 4 true ++
      List.replicate 3 false) := by
  exact (isUlamWord_zeros_four_ones_zeros_iff _ _ (by omega)).2 (by omega)

end MetaMathlibExt.isUlamWord_zeros_four_ones_zeros_iff

namespace MetaMathlibExt.isUlamWord_zeros_two_ones_zeros_iff

-- At zero padding the halves of 11 coincide. Adding one zero at either end gives a unique cut.
example : ¬IsUlamWord [true, true] ∧ IsUlamWord [false, true, true] ∧
    IsUlamWord [true, true, false] := by
  decide

-- With padding at both ends, 01|10 competes with endpoint cuts in 0110.
-- In 00110 the cut 001|10 is unique.
example : ¬IsUlamWord [false, true, true, false] ∧
    IsUlamWord [false, false, true, true, false] := by
  decide

example (k : ℕ) :
    IsUlamWord (List.replicate k false ++ List.replicate 2 true ++ List.replicate (k + 1) false) :=
  (isUlamWord_zeros_two_ones_zeros_iff k (k + 1)).2 (by omega)

end MetaMathlibExt.isUlamWord_zeros_two_ones_zeros_iff

namespace MetaMathlibExt.isUlamWord_zeros_one_zeros_iff

-- The singleton is accepted; of the two endpoint extensions, precisely one is valid for 0010.
example : IsUlamWord [true] ∧ IsUlamWord [false, false, true, false] := by
  exact ⟨(isUlamWord_zeros_one_zeros_iff 0 0).2 (by decide),
    (isUlamWord_zeros_one_zeros_iff 2 1).2 (by decide)⟩

-- Both endpoint cuts of 010 are valid, so it is not an Ulam word.
example : ¬ IsUlamWord [false, true, false] := by
  intro h
  exact (by decide : ¬ Odd ((1 + 1 : ℕ).choose 1))
    ((isUlamWord_zeros_one_zeros_iff 1 1).1 h)

end MetaMathlibExt.isUlamWord_zeros_one_zeros_iff

namespace MetaMathlibExt.card_ulam_zeros_one_zeros

-- With no padding, the only candidate is the singleton [true].
example : ((Finset.range 1).filter fun a =>
    IsUlamWord (List.replicate a false ++ [true] ++ List.replicate (1 - 1 - a) false)).card = 1 :=
  card_ulam_zeros_one_zeros (n := 1) (hn := by decide)

-- For 6 letters the Pascal row index is 5 = 101₂, with two nonadjacent set bits.
example : ((Finset.range 6).filter fun a =>
    IsUlamWord (List.replicate a false ++ [true] ++ List.replicate (6 - 1 - a) false)).card = 4 :=
  card_ulam_zeros_one_zeros (n := 6) (hn := by decide)

-- Check the actual positions independently against the recursive word predicate.
example : ((Finset.range 6).filter fun a =>
    IsUlamWord (List.replicate a false ++ [true] ++ List.replicate (6 - 1 - a) false)) =
      {0, 1, 4, 5} := by
  decide

end MetaMathlibExt.card_ulam_zeros_one_zeros

namespace MetaMathlibExt.two_mul_add_four_le_ulamWordCount

-- Compute the exact count independently at the first admissible length.
example : ulamWordCount 6 = 26 := by decide

-- Check the boundary and representatives of the three cases through the public API.
example : 16 ≤ ulamWordCount 6 :=
  two_mul_add_four_le_ulamWordCount (n := 6) (hn := by decide)

example : 18 ≤ ulamWordCount 7 :=
  two_mul_add_four_le_ulamWordCount (n := 7) (hn := by decide)

example : 20 ≤ ulamWordCount 8 :=
  two_mul_add_four_le_ulamWordCount (n := 8) (hn := by decide)

example : 22 ≤ ulamWordCount 9 :=
  two_mul_add_four_le_ulamWordCount (n := 9) (hn := by decide)

-- Test representative words independently of the lower-bound theorem.
example : IsUlamWord [false, true, false, true, false, false] ∧
    IsUlamWord [false, false, true, false, false, false, false] ∧
    IsUlamWord [false, false, true, true, true, true, false, false, false] := by
  decide

end MetaMathlibExt.two_mul_add_four_le_ulamWordCount

namespace MetaMathlibExt.ulamDensity_inv_isTheta_ulamGapMean

private theorem values_eq {n : ℕ} {l : List ℕ} (hd : l.Nodup) (hs : l.Pairwise (· ≤ ·))
    (h : (ulamValuesSorted n).toFinset = l.toFinset) : ulamValuesSorted n = l := by
  rw [← (List.toFinset_sort (r := (· ≤ ·)) hd).2 hs, ← h, ulamValuesSorted,
    Finset.sort_toFinset]

-- The empty list has no gaps; at length two there is exactly one gap.
example : ulamGapMean 0 = 0 ∧ ulamValuesSorted 2 = [1, 2] ∧ ulamGapMean 2 = 1 := by
  have h₀ : ulamValuesSorted 0 = [] := by
    apply values_eq (by decide) (by decide)
    rw [ulamValuesSorted, Finset.sort_toFinset]
    decide
  have h₂ : ulamValuesSorted 2 = [1, 2] := by
    apply values_eq (by decide) (by decide)
    rw [ulamValuesSorted, Finset.sort_toFinset]
    decide
  exact ⟨by simp [ulamGapMean, h₀], h₂, by norm_num [ulamGapMean, h₂, List.zipWith_cons_cons]⟩

-- Length three has unequal gaps (2, 1, 2), so the mean is not an integer.
example : ulamValuesSorted 3 = [1, 3, 4, 6] ∧ ulamGapMean 3 = 5 / 3 := by
  have h₃ : ulamValuesSorted 3 = [1, 3, 4, 6] :=
    values_eq (by decide) (by decide) (by simpa using ulamValuesSorted_three)
  exact ⟨h₃, by norm_num [ulamGapMean, h₃, List.zipWith_cons_cons]⟩

example : (fun n : ℕ => (2 : ℝ) ^ n / ulamWordCount n) =Θ[Filter.atTop]
    fun n => (ulamGapMean n : ℝ) :=
  ulamDensity_inv_isTheta_ulamGapMean

end MetaMathlibExt.ulamDensity_inv_isTheta_ulamGapMean
