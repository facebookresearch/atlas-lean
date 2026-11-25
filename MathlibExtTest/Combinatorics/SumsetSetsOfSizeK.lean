/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SumsetSetsOfSizeK
import Mathlib.Algebra.Order.Group.Int

/-! # Tests for iterated sumsets and their trivial elements -/

open scoped Pointwise
open MetaMathlibExt

-- One summand already gives the claimed size, including for a nonunit step.
example {k : ℕ} (hk : 3 ≤ k) :
    (insert (k • (2 : ℤ)) ((Finset.range (k - 1)).image fun i => i • (2 : ℤ))).card = k := by
  simpa only [one_nsmul, one_mul] using
    card_nsmul_arithProg_skip_penultimate (2 : ℤ) (by decide) k 1 hk le_rfl

-- At the smallest k, doubling fills the original gap at 2 and leaves a gap at 5.
example : (2 : ℕ) • ({0, 1, 3} : Finset ℤ) = {0, 1, 2, 3, 4, 6} := by decide

-- In the same double sumset, 3 is the only sum absent from the list of trivial elements.
example : sumsetTrivialElements 2 3 (fun n => if n = 2 then (3 : ℤ) else n) =
    {0, 1, 2, 4, 6} := by decide

-- The nonadjacent sum 0 + 3 stays nontrivial when 4 is added to {0, 1, 3}.
example : let a : ℕ → ℤ := fun n => if n < 2 then n else n + 1
    3 ∈ (2 : ℕ) • (Finset.range 4).image a ∧ 3 ∉ sumsetTrivialElements 2 4 a := by
  intro a
  have hinc : ∀ i : Fin 3, a i < a (i.val + 1) := by decide
  obtain ⟨hsub, hnontriv⟩ := nsmul_sumset_erase_max_nontrivial 2 4 (by decide) a
    (fun i hi => hinc ⟨i, by omega⟩)
  have hmem : (3 : ℤ) ∈ (2 : ℕ) • (Finset.range (4 - 1)).image a := by decide
  exact ⟨hsub hmem, hnontriv 3 hmem (by decide)⟩

-- With zero summands and a singleton prefix, even its largest sum is trivial on both lists.
example (a : ℕ → ℤ) :
    (0 : ℕ) • (Finset.range 1).image a = sumsetTrivialElements 0 1 a ∧
      sumsetTrivialElements 0 1 a = sumsetTrivialElements 0 2 a := by
  simp [sumsetTrivialElements, Finset.singleton_zero]

-- At the minimum proper multiple, the two witnesses for three summands exhaust the difference.
example : let a : ℕ → ℤ := fun n => if n = 3 then 4 else n
    let extras := (3 : ℕ) • (Finset.range 4).image a \ sumsetTrivialElements 3 4 a
    2 ≤ extras.card ∧ extras = {7, 9} := by
  intro a extras
  constructor
  · exact nontrivial_sumset_card_of_last_gap_eq_nsmul 3 4 (by decide) a (by decide)
      (fun i hi => by
        obtain rfl : i = 0 := by omega
        decide)
      1 (by decide) 2 (by decide) (by decide) (by decide)
  · decide

-- A last gap 1 after a gap 2 is not a multiple: 6 and 8 are the paper's witnesses, 4 is extra.
example : let a : ℕ → ℤ := fun n => if n < 2 then n else n + 1
    let extras := (3 : ℕ) • (Finset.range 4).image a \ sumsetTrivialElements 3 4 a
    2 ≤ extras.card ∧ extras = {4, 6, 8} := by
  intro a extras
  constructor
  · exact nontrivial_sumset_card_of_last_gap_ne_nsmul 3 4 le_rfl a (by decide)
      (fun i hi => by
        obtain rfl : i = 0 := by omega
        decide)
      2 1 (by decide) (by decide) (by decide) (by decide)
      (fun d _ => by rw [Int.nsmul_eq_mul]; omega)
  · decide

-- Equal last gaps (`d = 1`) must be excluded: every sum of three elements of 0, 1, 2, 3 is trivial.
example : (3 : ℕ) • (Finset.range 4).image (fun n : ℕ => (n : ℤ)) \
    sumsetTrivialElements 3 4 (fun n : ℕ => (n : ℤ)) = ∅ := by decide

-- With three summands and four points the forbidden interval is the singleton {11}.
example (A : Finset (ℤ × ℤ)) (hA : A.card = 4) : ((3 : ℕ) • A).card ≠ 11 := by
  intro he
  apply card_nsmul_notMem_Icc_of_isAddTorsionFree 3 4 le_rfl A hA
  rw [he]
  decide

-- Both sizes immediately adjacent to the gap occur.
example : ((3 : ℕ) • ({0, 1, 2, 3} : Finset ℤ)).card = 10 ∧
    ((3 : ℕ) • ({0, 1, 2, 4} : Finset ℤ)).card = 12 := by decide

-- A progression with step two has only trivial sums. The sequence can drop after the prefix.
example : let a : ℕ → ℤ := fun n => if n < 4 then 2 * (n : ℤ) else 0
    ∀ i < 4, a i = i • a 1 := by
  intro a
  have hinc : ∀ i : Fin 3, a i < a (i.val + 1) := by decide
  exact (arithProg_or_nontrivial_sumset_card_of_last_gaps_eq 3 4 le_rfl a (by decide)
    (fun i hi => hinc ⟨i, by omega⟩) (by decide)).resolve_right (by decide)

-- For 0, 1, 3, 5 the shorter sumset attains the bound, with witnesses 0 + 1 + 3 and 0 + 3 + 3.
example : let a : ℕ → ℤ := fun n => if n = 0 then 0 else 2 * (n : ℤ) - 1
    let extras := (3 : ℕ) • (Finset.range 3).image a \ sumsetTrivialElements 3 3 a
    2 ≤ extras.card ∧ extras = {4, 6} := by
  intro a extras
  have hinc : ∀ i : Fin 3, a i < a (i.val + 1) := by decide
  refine ⟨?_, by decide⟩
  apply (arithProg_or_nontrivial_sumset_card_of_last_gaps_eq 3 4 le_rfl a (by decide)
    (fun i hi => hinc ⟨i, by omega⟩) (by decide)).resolve_left
  exact fun hap => (by decide : a 2 ≠ 2 • a 1) (hap 2 (by decide))
