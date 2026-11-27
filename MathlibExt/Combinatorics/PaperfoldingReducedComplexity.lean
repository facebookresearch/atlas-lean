/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.ReducedComplexities
import Mathlib.Data.List.Iterate

/-!
# Reduced complexity of the paperfolding word at even lengths

`rhoRed_paperfolding_two_mul` shows that every positive even length has four distinct reductions
of paperfolding factors. Letters at consecutive even positions differ, so each such pair
contributes one change of letter regardless of the intervening letter.
-/

namespace MathlibExt.Combinatorics.ReducedComplexitiesWanted

open InfiniteWord

namespace rhoRed_paperfolding_two_mul

private theorem paperfoldingSeq_even (j : ℕ) :
    paperfoldingSeq (2 * j) = decide (j % 2 = 1) := by
  have h : (2 * j + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_remainder j (by decide)
  rw [Bool.eq_iff_iff]
  simp only [paperfoldingSeq, h, pow_zero, Nat.div_one, decide_eq_true_eq]
  omega

private theorem paperfoldingSeq_two_step (j : ℕ) :
    paperfoldingSeq (2 * (j + 1)) = !paperfoldingSeq (2 * j) := by
  rw [paperfoldingSeq_even, paperfoldingSeq_even, ← decide_not, Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  omega

private theorem factorList_succ (n i : ℕ) :
    factorList paperfoldingSeq (n + 1) i =
      paperfoldingSeq i :: factorList paperfoldingSeq n (i + 1) := by
  simp only [factorList, List.ofFn_succ, factor_apply, Fin.val_zero, Nat.add_zero]
  congr 2
  funext s
  change paperfoldingSeq (i + (s.val + 1)) = paperfoldingSeq (i + 1 + s.val)
  rw [Nat.add_right_comm, Nat.add_assoc]

private theorem redWord_cons_iterate (a b : Bool) (w : List Bool) (k : ℕ)
    (h : redWord (b :: w) = List.iterate Bool.not b k) :
    redWord (a :: b :: w) =
      List.iterate Bool.not a (k + (decide (a ≠ b)).toNat) := by
  cases a <;> cases b <;> simp [redWord, h]

-- The middle letter agrees with one of its neighbors.
private theorem redWord_skip_middle (a b c : Bool) (w : List Bool) (h : c = !a) :
    redWord (a :: b :: c :: w) = a :: redWord (c :: w) := by
  subst c
  cases a <;> cases b <;> simp [redWord]

private theorem red_factor_one (i : ℕ) :
    redWord (factorList paperfoldingSeq 1 i) = List.iterate Bool.not (paperfoldingSeq i) 1 := by
  simp [factorList, redWord]

private theorem red_factor_succ (k i a : ℕ)
    (h : redWord (factorList paperfoldingSeq (k + 1) (i + 1)) =
      List.iterate Bool.not (paperfoldingSeq (i + 1)) a) :
    redWord (factorList paperfoldingSeq (k + 1 + 1) i) =
      List.iterate Bool.not (paperfoldingSeq i)
        (a + (decide (paperfoldingSeq i ≠ paperfoldingSeq (i + 1))).toNat) := by
  simp only [factorList_succ] at h ⊢
  exact redWord_cons_iterate _ _ _ _ h

-- Adding k aligned pairs before a nonempty suffix adds k letters to the reduction.
private theorem red_factor_even_start (k j r a : ℕ)
    (h : redWord (factorList paperfoldingSeq (r + 1) (2 * (j + k))) =
      List.iterate Bool.not (paperfoldingSeq (2 * (j + k))) a) :
    redWord (factorList paperfoldingSeq (2 * k + r + 1) (2 * j)) =
      List.iterate Bool.not (paperfoldingSeq (2 * j)) (a + k) := by
  induction k generalizing j with
  | zero => simpa using h
  | succ k ih =>
    have htail := ih (j + 1) (by simpa only [show j + 1 + k = j + (k + 1) by omega] using h)
    rw [show 2 * (k + 1) + r + 1 = 2 * k + r + 1 + 1 + 1 by omega,
      factorList_succ, factorList_succ, show 2 * j + 1 + 1 = 2 * (j + 1) by omega,
      factorList_succ, redWord_skip_middle _ _ _ _ (paperfoldingSeq_two_step j),
      ← factorList_succ, htail]
    simp [paperfoldingSeq_two_step j]

private def reducedWord (k : ℕ) (p : Bool × Bool) : List Bool :=
  List.iterate Bool.not p.1 (k + p.2.toNat + 1)

private theorem reducedWord_injective (k : ℕ) : Function.Injective (reducedWord k) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have hfirst : a = c := by simpa [reducedWord] using congrArg List.head? h
  have hlast : b = d := by
    have hlen := congrArg List.length h
    cases b <;> cases d <;> simp [reducedWord, List.length_iterate] at hlen ⊢
  exact Prod.ext hfirst hlast

private def firstLetterAndChange (i : ℕ) : Bool × Bool :=
  (paperfoldingSeq i, decide (paperfoldingSeq i ≠ paperfoldingSeq (i + 1)))

private theorem red_even_length_even_start (k j : ℕ) :
    redWord (factorList paperfoldingSeq (2 * (k + 1)) (2 * j)) =
      reducedWord k (paperfoldingSeq (2 * j), (firstLetterAndChange (2 * (j + k))).2) := by
  have htail := red_factor_succ 0 (2 * (j + k)) 1 (red_factor_one _)
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, red_factor_even_start k j 1 _ htail]
  simp only [reducedWord, firstLetterAndChange]
  congr 1
  omega

private theorem red_even_length_odd_start (k j : ℕ) :
    redWord (factorList paperfoldingSeq (2 * (k + 1)) (2 * j + 1)) =
      reducedWord k (firstLetterAndChange (2 * j + 1)) := by
  have htail := red_factor_even_start k (j + 1) 0 1 (red_factor_one _)
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, Nat.add_zero] at htail
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, red_factor_succ _ _ _ htail]
  simp only [reducedWord, firstLetterAndChange]
  congr 1
  omega

-- Both values of the first letter and both possibilities for the first change occur.
private theorem firstLetterAndChange_odd_surjective :
    Function.Surjective (fun j => firstLetterAndChange (2 * j + 1)) := by
  rintro ⟨a, b⟩
  cases a <;> cases b
  · exact ⟨1, by decide +kernel⟩
  · exact ⟨0, by decide +kernel⟩
  · exact ⟨2, by decide +kernel⟩
  · exact ⟨5, by decide +kernel⟩

private theorem reduced_range (k : ℕ) :
    Set.range (fun i => redWord (factorList paperfoldingSeq (2 * (k + 1)) i)) =
      Set.range (reducedWord k) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨i, rfl⟩
    change redWord (factorList paperfoldingSeq (2 * (k + 1)) i) ∈ _
    obtain ⟨j, rfl | rfl⟩ : ∃ j, i = 2 * j ∨ i = 2 * j + 1 := ⟨i / 2, by omega⟩
    · rw [red_even_length_even_start]
      exact Set.mem_range_self _
    · rw [red_even_length_odd_start]
      exact Set.mem_range_self _
  · rintro _ ⟨p, rfl⟩
    obtain ⟨j, hj⟩ := firstLetterAndChange_odd_surjective p
    refine ⟨2 * j + 1, ?_⟩
    change firstLetterAndChange (2 * j + 1) = p at hj
    change redWord (factorList paperfoldingSeq (2 * (k + 1)) (2 * j + 1)) = _
    rw [red_even_length_odd_start, hj]

end rhoRed_paperfolding_two_mul

/-- **Reduced complexity of the paperfolding word at even lengths.** Let $f$ be the regular
paperfolding sequence and let $\rho^{\mathrm{red}}_f(n)$ be the number of distinct reductions of
length-$n$ factors of $f$. For every $n \ge 1$, $\rho^{\mathrm{red}}_f(2n) = 4$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 5. -/
public theorem rhoRed_paperfolding_two_mul (n : ℕ) (hn : 1 ≤ n) :
    rhoRed paperfoldingSeq (2 * n) = 4 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [rhoRed, factorSet, ← Set.range_comp]
  change (Set.range (fun i => redWord (factorList paperfoldingSeq (2 * (k + 1)) i))).ncard = 4
  rw [rhoRed_paperfolding_two_mul.reduced_range,
    Set.ncard_range_of_injective (rhoRed_paperfolding_two_mul.reducedWord_injective k)]
  simp [Nat.card_eq_fintype_card]

end MathlibExt.Combinatorics.ReducedComplexitiesWanted
