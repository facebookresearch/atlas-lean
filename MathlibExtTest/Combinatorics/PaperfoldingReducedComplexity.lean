/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.Combinatorics.PaperfoldingReducedComplexity

open InfiniteWord MathlibExt.Combinatorics.ReducedComplexitiesWanted

-- A singleton has one run, with no alternation hypothesis to check.
example (a : Bool) : (redWord (List.ofFn (fun _ : Fin 1 => a))).length = 1 :=
  redWord_length_alternating_even 0 _ (fun i => Fin.elim0 i)

-- The middle letter of the first triple agrees with its left endpoint, and that of the
-- second triple agrees with its right endpoint.
example : (redWord (List.ofFn ![false, false, true, false, false])).length = 3 :=
  redWord_length_alternating_even 2 _ (by decide)

example : rhoRed paperfoldingSeq 2 = 4 :=
  rhoRed_paperfolding_two_mul 1 (hn := by decide)

-- These length-four factors exhibit both reduction lengths for each first letter.
example :
    [1, 3, 5, 11].map (fun i => redWord (factorList paperfoldingSeq 4 i)) =
      [[false, true, false], [false, true], [true, false], [true, false, true]] := by
  decide +kernel

-- The smallest positive even length has one- and two-letter reductions.
example : rhoAbRed paperfoldingSeq 2 = 3 :=
  rhoAbRed_paperfolding_even 2 (by decide) ⟨1, rfl⟩

-- At length four the shorter, rather than the longer, reductions have even length.
example : rhoAbRed paperfoldingSeq 4 = 3 :=
  rhoAbRed_paperfolding_even 4 (by decide) ⟨2, rfl⟩

-- After filling `d` levels in the Toeplitz construction, the filled letters repeat
-- with period `2 ^ (d + 1)`. A gap is a multiple of `2 ^ d` in one-based indexing.
private theorem paperfolding_period_off_gaps (d q i : ℕ) (hi : (i + 1) % 2 ^ d ≠ 0) :
    paperfoldingSeq (i + q * 2 ^ (d + 1)) = paperfoldingSeq i := by
  induction d generalizing i with
  | zero => exact (hi (by rw [pow_zero, Nat.mod_one])).elim
  | succ d ih =>
    obtain ⟨j, rfl | rfl⟩ : ∃ j, i = 2 * j ∨ i = 2 * j + 1 := ⟨i / 2, by omega⟩
    · have h : 2 * j + q * 2 ^ (d + 1 + 1) = 2 * (j + 2 * (q * 2 ^ d)) := by
        simp [pow_succ, Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm]
      simp only [h, paperfoldingSeq_even, show (j + 2 * (q * 2 ^ d)) % 2 = j % 2 by omega]
    · have h : 2 * j + 1 + q * 2 ^ (d + 1 + 1) = 2 * (j + q * 2 ^ (d + 1)) + 1 := by
        simp [pow_succ, Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      rw [h, paperfoldingSeq_odd, paperfoldingSeq_odd]
      apply ih
      intro hgap
      apply hi
      rw [show 2 * j + 1 + 1 = (j + 1) * 2 by omega, pow_succ, Nat.mul_mod_mul_right,
        hgap, Nat.zero_mul]

private def factorTemplate (d n : ℕ) (r : Fin (2 ^ (d + 1))) (b : Bool) : List Bool :=
  List.ofFn fun j : Fin n =>
    if (r.val + j.val + 1) % 2 ^ d = 0 then b else paperfoldingSeq (r.val + j.val)

-- In a block of length at most `2 ^ d` there is at most one gap. One residue for the
-- starting position and one bit for that gap therefore suffice for the upper bound.
private theorem factor_eq_template (d n i : ℕ) (hn : n ≤ 2 ^ d) :
    ∃ (r : Fin (2 ^ (d + 1))) (b : Bool),
      List.ofFn (factor paperfoldingSeq n i) = factorTemplate d n r b := by
  classical
  let r : Fin (2 ^ (d + 1)) := ⟨i % 2 ^ (d + 1), Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  let gap (j : Fin n) := (r.val + j.val + 1) % 2 ^ d = 0
  let b := if h : ∃ j, gap j then paperfoldingSeq (i + h.choose.val) else false
  refine ⟨r, b, congrArg List.ofFn ?_⟩
  funext j
  rw [factor_apply]
  change paperfoldingSeq (i + j.val) = if gap j then b else paperfoldingSeq (r.val + j.val)
  split_ifs with h
  · have hExists : ∃ j, gap j := ⟨j, h⟩
    have hmod : j.val ≡ hExists.choose.val [MOD 2 ^ d] := by
      apply Nat.ModEq.add_left_cancel' (r.val + 1)
      change (r.val + 1 + j.val) % _ = (r.val + 1 + hExists.choose.val) % _
      rw [Nat.add_right_comm _ 1 j.val, Nat.add_right_comm _ 1 hExists.choose.val]
      exact h.trans hExists.choose_spec.symm
    have hj := hmod.eq_of_lt_of_lt (j.isLt.trans_le hn) (hExists.choose.isLt.trans_le hn)
    rw [show b = paperfoldingSeq (i + hExists.choose.val) by simp [b, hExists], hj]
  · have hi : r.val + (i / 2 ^ (d + 1)) * 2 ^ (d + 1) = i := by
      dsimp [r]
      rw [Nat.mul_comm (i / 2 ^ (d + 1))]
      exact Nat.mod_add_div _ _
    rw [show i + j.val = r.val + j.val + (i / 2 ^ (d + 1)) * 2 ^ (d + 1) by omega]
    exact paperfolding_period_off_gaps _ _ _ h

private def reducedSignature (w : List Bool) : ℕ × ℕ :=
  ((redWord w).length, (redWord w).count false)

-- For each length, check every residue and both gap values, then compute actual factors
-- attaining all four signatures. These checks do not use the general complexity theorem.
example : (Set.range fun i => reducedSignature (List.ofFn (factor paperfoldingSeq 5 i))) =
    {(2, 1), (3, 1), (3, 2), (4, 2)} := by
  ext p
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨r, b, hr⟩ := factor_eq_template 3 5 i (by decide)
    rw [hr]
    have h : ∀ (r : Fin 16) (b : Bool),
        let s := reducedSignature (factorTemplate 3 5 r b)
        s = (2, 1) ∨ s = (3, 1) ∨ s = (3, 2) ∨ s = (4, 2) := by decide +kernel
    exact h r b
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨5, by decide +kernel⟩
    · exact ⟨2, by decide +kernel⟩
    · exact ⟨0, by decide +kernel⟩
    · exact ⟨1, by decide +kernel⟩

example : (Set.range fun i => reducedSignature (List.ofFn (factor paperfoldingSeq 9 i))) =
    {(4, 2), (5, 2), (5, 3), (6, 3)} := by
  ext p
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨r, b, hr⟩ := factor_eq_template 4 9 i (by decide)
    rw [hr]
    have h : ∀ (r : Fin 32) (b : Bool),
        let s := reducedSignature (factorTemplate 4 9 r b)
        s = (4, 2) ∨ s = (5, 2) ∨ s = (5, 3) ∨ s = (6, 3) := by decide +kernel
    exact h r b
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨3, by decide +kernel⟩
    · exact ⟨2, by decide +kernel⟩
    · exact ⟨0, by decide +kernel⟩
    · exact ⟨11, by decide +kernel⟩

example : rhoAbRed paperfoldingSeq 5 = 4 :=
  rhoAbRed_paperfolding_mod_four_one 5 (by decide) (by decide)

example : rhoAbRed paperfoldingSeq 9 = 4 :=
  rhoAbRed_paperfolding_mod_four_one 9 (by decide) (by decide)
