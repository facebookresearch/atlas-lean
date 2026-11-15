/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.InformationRetrieval.DiscountedGain
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Tests for discounted cumulative gain
-/

set_option autoImplicit false

open Cslib.InformationRetrieval

namespace CSLibExtTest.InformationRetrieval.DiscountedGain

/-- Empty cutoff has zero DCG. -/
example {N : ℕ} (g : Fin N → ℝ) (w : Fin 0 → ℝ) (r : Fin 0 → Fin N) :
    dcgAt g w r = 0 := by
  simp [dcgAt]

/-- Empty cutoff has zero ideal DCG. -/
example {N : ℕ} (g : Fin N → ℝ)
    (w : {w : Fin 0 → ℝ // (∀ i, 0 ≤ w i) ∧ Antitone w})
    (s : {s : Equiv.Perm (Fin N) // Antitone (g ∘ s)}) :
    idealDCGAt (Nat.zero_le N) g w s = 0 := by
  simp [idealDCGAt]

/-- All-zero gains have zero DCG. -/
example {N k : ℕ} (w : Fin k → ℝ) (r : Fin k → Fin N) :
    dcgAt (fun _ => 0) w r = 0 := by
  simp [dcgAt]

/-- All-zero discounts have zero DCG. -/
example {N k : ℕ} (g : Fin N → ℝ) (r : Fin k → Fin N) :
    dcgAt g (fun _ => 0) r = 0 := by
  simp [dcgAt]

/-- The bound applies with the sorted permutation supplied by `exists_sortedPerm`. -/
example {N k : ℕ} (hk : k ≤ N) (g : Fin N → ℝ) (w : Fin k → ℝ)
    (r : Fin k → Fin N) (hw0 : ∀ i, 0 ≤ w i)
    (hw : Antitone w) (hr : Function.Injective r) :
    ∃ s : {s : Equiv.Perm (Fin N) // Antitone (g ∘ s)},
      dcgAt g w r ≤ idealDCGAt hk g ⟨w, ⟨hw0, hw⟩⟩ s := by
  obtain ⟨s, hs⟩ := exists_sortedPerm g
  exact ⟨⟨s, hs⟩, dcgAt_le_idealDCGAt hk hw0 hw hr hs⟩

noncomputable def gains321 : Fin 3 → ℝ :=
  ![3, 2, 1]

noncomputable def discounts21 : Fin 2 → ℝ :=
  ![2, 1]

noncomputable def topTwo : Fin 2 → Fin 3 :=
  ![0, 1]

noncomputable def lowerTwo : Fin 2 → Fin 3 :=
  ![1, 2]

noncomputable def sorted321 : {s : Equiv.Perm (Fin 3) // Antitone (gains321 ∘ s)} :=
  ⟨Equiv.refl (Fin 3), by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [gains321]
    norm_num
  ⟩

noncomputable def discounts21Valid :
    {w : Fin 2 → ℝ // (∀ i, 0 ≤ w i) ∧ Antitone w} :=
  ⟨discounts21, by
    constructor
    · intro i
      fin_cases i <;> norm_num [discounts21]
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [discounts21]
  ⟩

/-- The ideal prefix `[0, 1]` for gains `[3, 2, 1]` and discounts `[2, 1]` scores `8`. -/
example : dcgAt gains321 discounts21 topTwo = 8 := by
  simp only [dcgAt, gains321, discounts21, topTwo, Fin.sum_univ_two]
  norm_num

/-- An internally sorted but non-top prefix `[1, 2]` scores only `5`. -/
example : dcgAt gains321 discounts21 lowerTwo = 5 := by
  simp only [dcgAt, gains321, discounts21, lowerTwo, Fin.sum_univ_two]
  norm_num

/-- The bundled ideal ranking for gains `[3, 2, 1]` has ideal DCG `8` at cutoff `2`. -/
example : idealDCGAt (by norm_num) gains321 discounts21Valid sorted321 = 8 := by
  simp only [idealDCGAt, discounts21Valid, sorted321, gains321, discounts21,
    Fin.sum_univ_two]
  norm_num

/-- The main bound instantiated against the non-top prefix `[1, 2]`. -/
example : dcgAt gains321 discounts21 lowerTwo ≤
    idealDCGAt (by norm_num) gains321 discounts21Valid sorted321 := by
  have hr : Function.Injective lowerTwo := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [lowerTwo]
  exact dcgAt_le_idealDCGAt (by norm_num) discounts21Valid.2.1
    discounts21Valid.2.2 hr sorted321.2

/-- Normalized DCG is zero when all gains, hence the ideal DCG, are zero. -/
example {N k : ℕ} (hk : k ≤ N)
    (w : {w : Fin k → ℝ // (∀ i, 0 ≤ w i) ∧ Antitone w})
    (r : Fin k → Fin N)
    (s : {s : Equiv.Perm (Fin N) // Antitone ((fun _ => (0 : ℝ)) ∘ s)}) :
    ndcgAt hk (fun _ => 0) w r s = 0 :=
  ndcgAt_of_ideal_eq_zero hk _ w r s (by simp [idealDCGAt])

/-- The non-top prefix `[1, 2]` has normalized DCG `5 / 8` for gains
`[3, 2, 1]` and discounts `[2, 1]`. -/
example : ndcgAt (by norm_num) gains321 discounts21Valid lowerTwo sorted321
    = 5 / 8 := by
  have hideal : idealDCGAt (by norm_num) gains321 discounts21Valid sorted321 = 8 := by
    simp only [idealDCGAt, discounts21Valid, sorted321, gains321, discounts21,
      Fin.sum_univ_two]
    norm_num
  have hdcg : dcgAt gains321 discounts21 lowerTwo = 5 := by
    simp only [dcgAt, gains321, discounts21, lowerTwo, Fin.sum_univ_two]
    norm_num
  unfold ndcgAt
  rw [hideal]
  norm_num [hdcg, discounts21Valid]

/-- The sorted prefix itself has normalized DCG `1` in the concrete example. -/
example : ndcgAt (by norm_num) gains321 discounts21Valid
    (fun i => sorted321.1 (Fin.castLE (by norm_num) i)) sorted321 = 1 := by
  apply ndcgAt_sortedPrefix_eq_one_of_pos
  have hideal : idealDCGAt (by norm_num) gains321 discounts21Valid sorted321 = 8 := by
    simp only [idealDCGAt, discounts21Valid, sorted321, gains321, discounts21,
      Fin.sum_univ_two]
    norm_num
  rw [hideal]
  norm_num

/-- The normalized-DCG bound instantiated on the concrete non-top prefix. -/
example : ndcgAt (by norm_num) gains321 discounts21Valid lowerTwo sorted321 ∈
    Set.Icc (0 : ℝ) 1 := by
  have hg : ∀ i, 0 ≤ gains321 i := by
    intro i
    fin_cases i <;> norm_num [gains321]
  have hr : Function.Injective lowerTwo := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [lowerTwo]
  exact ndcgAt_mem_Icc (by norm_num) hg hr

end CSLibExtTest.InformationRetrieval.DiscountedGain
