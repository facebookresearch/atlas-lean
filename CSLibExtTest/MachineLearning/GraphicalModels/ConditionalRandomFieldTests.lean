/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.ConditionalRandomField
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Chain conditional random field tests

Closed checks on the all-ones CRF over two states: the partition function counts
label paths, the forward variables count paths ending in each state, the Viterbi
variables are `1`, conditional probabilities sum to `1`, and the theorems
instantiate. An asymmetric CRF checks the tabulated forward/Viterbi algorithms
and backtracking against hand-computed values, and the `ℝ≥0` CRF checks that
normalization needs only a semifield. Axiom audit follows.
-/

namespace Cslib.MachineLearning.GraphicalModels.ConditionalRandomField

/-- The all-ones CRF over two states and `Bool` inputs: every potential is `1`. -/
def onesCRF : ChainCRF (Fin 2) Bool ℚ :=
  ⟨fun _ _ _ => 1, fun _ _ _ _ => 1, fun _ _ _ => zero_le_one, fun _ _ _ _ => zero_le_one⟩

example : partition onesCRF (fun _ => true) 1 = 4 := by
  simp [partition, pathWeight, onesCRF]

example : forward onesCRF (fun _ => true) 1 0 = 2 := by simp [forward, onesCRF]

example : forward onesCRF (fun _ => true) 1 1 = 2 := by simp [forward, onesCRF]

example : (Finset.univ : Finset (Fin 2)).sup' Finset.univ_nonempty
      (viterbi onesCRF (fun _ => true) 1) =
    (Finset.univ : Finset (Fin 2 → Fin 2)).sup' Finset.univ_nonempty
      (pathWeight onesCRF (fun _ => true) 1) :=
  sup'_viterbi_eq (fun _ => true) 1

example (x : ℕ → Bool) : partition onesCRF x 1 = ∑ s, forward onesCRF x 1 s :=
  partition_eq_sum_forward onesCRF x 1

example : ∑ z : Fin 2 → Fin 2, condProb onesCRF (fun _ => true) 1 z = 1 :=
  sum_condProb_eq_one onesCRF (fun _ => true) 1 (by simp [partition, pathWeight, onesCRF])

/-- The all-ones CRF over `ℝ≥0`: the forward API needs only a semiring, so the
natural probability-weight type is now admitted (it is not a field). -/
def nnCRF : ChainCRF (Fin 2) Bool NNReal :=
  ⟨fun _ _ _ => 1, fun _ _ _ _ => 1, fun _ _ _ => zero_le_one, fun _ _ _ _ => zero_le_one⟩

example : partition nnCRF (fun _ => true) 1 = 4 := by
  simp [partition, pathWeight, nnCRF]

example : forward nnCRF (fun _ => true) 1 0 = 2 := by simp [forward, nnCRF]

/-- A CRF whose transition potential looks ahead: it reads `x (t + 1)`, an observation
beyond the current position, which the old `trans : ℕ → S → S → R` could not express. -/
def lookaheadCRF : ChainCRF (Fin 2) Bool ℚ :=
  ⟨fun _ _ _ => 1, fun x t _ _ => if x (t + 1) then 2 else 1, fun _ _ _ => zero_le_one,
    fun x t _ _ => by split <;> norm_num⟩

example (z : Fin 2 → Fin 2) : pathWeight lookaheadCRF (fun _ => true) 1 z = 2 := by
  simp [pathWeight, lookaheadCRF]

example (z : Fin 2 → Fin 2) : pathWeight lookaheadCRF (fun _ => false) 1 z = 1 := by
  simp [pathWeight, lookaheadCRF]

/-- Asymmetric CRF: unary favors state 0 (4 vs 1); the 0→0 transition scores 3, else 1.
The MAP path of length 2 is `00` (weight 48, unique), partition is 57. -/
def asymCRF : ChainCRF (Fin 2) Bool ℚ :=
  ⟨fun _ _ s => if s = 0 then 4 else 1,
   fun _ _ s s' => if s = 0 ∧ s' = 0 then 3 else 1,
   fun _ _ s => by split <;> norm_num,
   fun _ _ s s' => by split <;> norm_num⟩

example : partitionTab (fun _ => true) asymCRF 1 = 57 := by
  norm_num [partitionTab, forwardTab, forwardStep,
    Cslib.MachineLearning.Sequence.HiddenMarkov.sumVec, Fin.sum_univ_two, asymCRF]

example : partitionTab (fun _ => true) asymCRF 0 = 5 := by
  norm_num [partitionTab, forwardTab,
    Cslib.MachineLearning.Sequence.HiddenMarkov.sumVec, Fin.sum_univ_two, asymCRF]

/-- The tabulated Viterbi variables at step 1 for the state-0 end. -/
private theorem asym_viterbiTab_one_zero :
    (viterbiTab (fun _ => true) asymCRF 1)[0] = 48 := by
  have h := viterbiTab_get (fun _ => true) asymCRF 1 0
  refine h.trans ?_
  simp only [viterbi, asymCRF]
  have hsup : (Finset.univ : Finset (Fin 2)).sup' Finset.univ_nonempty
      (fun s' => (if s' = 0 then (4 : ℚ) else 1) *
        (if s' = 0 ∧ True then 3 else 1)) = 12 := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      fin_cases i <;> simp <;> norm_num
    · calc (12 : ℚ) = (fun s' => (if s' = 0 then (4 : ℚ) else 1) *
          (if s' = 0 ∧ True then 3 else 1)) 0 := by norm_num
        _ ≤ _ := Finset.le_sup'
          (fun s' => (if s' = 0 then (4 : ℚ) else 1) *
            (if s' = 0 ∧ True then 3 else 1))
          (Finset.mem_univ (0 : Fin 2))
  rw [hsup]
  norm_num

/-- The tabulated Viterbi variables at step 1 for the state-1 end. -/
private theorem asym_viterbiTab_one_one :
    (viterbiTab (fun _ => true) asymCRF 1)[1] = 4 := by
  have h := viterbiTab_get (fun _ => true) asymCRF 1 1
  refine h.trans ?_
  simp only [viterbi, asymCRF]
  have hsup : (Finset.univ : Finset (Fin 2)).sup' Finset.univ_nonempty
      (fun s' => (if s' = 0 then (4 : ℚ) else 1) *
        (if s' = 0 ∧ (1 : Fin 2) = 0 then 3 else 1)) = 4 := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      fin_cases i <;> simp <;> norm_num
    · calc (4 : ℚ) = (fun s' => (if s' = 0 then (4 : ℚ) else 1) *
          (if s' = 0 ∧ (1 : Fin 2) = 0 then 3 else 1)) 0 := by norm_num
        _ ≤ _ := Finset.le_sup'
          (fun s' => (if s' = 0 then (4 : ℚ) else 1) *
            (if s' = 0 ∧ (1 : Fin 2) = 0 then 3 else 1))
          (Finset.mem_univ (0 : Fin 2))
  rw [hsup]
  norm_num

/-- Backtracking starts from state 0 at step 0. -/
private theorem asym_argmaxVec_zero :
    Cslib.MachineLearning.Sequence.HiddenMarkov.argmaxVec
      (viterbiTab (fun _ => true) asymCRF 0) = 0 := by
  have hfun : (fun s : Fin 2 => (viterbiTab (fun _ => true) asymCRF 0)[s]) =
      (fun s : Fin 2 => if s = 0 then (4 : ℚ) else 1) := by
    funext s
    refine Fin.cases ?_ ?_ s
    · simp [viterbiTab, asymCRF]
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp [Fin.succ_zero_eq_one, viterbiTab, asymCRF]
      · intro j
        exact Fin.elim0 j
  simp only [Cslib.MachineLearning.Sequence.HiddenMarkov.argmaxVec, hfun]
  decide

/-- Backtracking starts from state 0 at step 1. -/
private theorem asym_argmaxVec_one :
    Cslib.MachineLearning.Sequence.HiddenMarkov.argmaxVec
      (viterbiTab (fun _ => true) asymCRF 1) = 0 := by
  have hfun : (fun s : Fin 2 => (viterbiTab (fun _ => true) asymCRF 1)[s]) =
      (fun s : Fin 2 => if s = 0 then (48 : ℚ) else 4) := by
    funext s
    refine Fin.cases ?_ ?_ s
    · simp [asym_viterbiTab_one_zero]
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp [Fin.succ_zero_eq_one, asym_viterbiTab_one_one]
      · intro j
        exact Fin.elim0 j
  simp only [Cslib.MachineLearning.Sequence.HiddenMarkov.argmaxVec, hfun]
  decide

/-- The backpointer at step 0 picks state 0. -/
private theorem asym_back_zero :
    back (fun _ => true) asymCRF 0
      (viterbiTab (fun _ => true) asymCRF 0) 0 = 0 := by
  have hv0 : (viterbiTab (fun _ => true) asymCRF 0)[0] = 4 := by
    simp [viterbiTab, asymCRF]
  have hv1 : (viterbiTab (fun _ => true) asymCRF 0)[1] = 1 := by
    simp [viterbiTab, asymCRF]
  have htrans0 : asymCRF.trans (fun _ => true) 0 0 0 = 3 := by simp [asymCRF]
  have htrans1 : asymCRF.trans (fun _ => true) 0 1 0 = 1 := by simp [asymCRF]
  have hfun : (fun s' : Fin 2 => (viterbiTab (fun _ => true) asymCRF 0)[s'] *
      asymCRF.trans (fun _ => true) 0 s' 0) =
      (fun s' : Fin 2 => if s' = 0 then (12 : ℚ) else 1) := by
    funext s'
    refine Fin.cases ?_ ?_ s'
    · have hnum : (4 : ℚ) * 3 = 12 := by norm_num
      exact (congrArg₂ (· * ·) hv0 htrans0).trans hnum
    · intro i
      refine Fin.cases ?_ ?_ i
      · have hnum : (1 : ℚ) * 1 = 1 := by norm_num
        exact (congrArg₂ (· * ·) hv1 htrans1).trans hnum
      · intro j
        exact Fin.elim0 j
  simp only [back, hfun]
  decide

example : (viterbiTab (fun _ => true) asymCRF 1)[0] = 48 := asym_viterbiTab_one_zero

example : (viterbiTab (fun _ => true) asymCRF 1)[1] = 4 := asym_viterbiTab_one_one

example : (viterbiTab (fun _ => true) asymCRF 0)[0] = 4 := by
  simp [viterbiTab, asymCRF]

example : (viterbiTab (fun _ => true) asymCRF 0)[1] = 1 := by
  simp [viterbiTab, asymCRF]

example : (crfPath (fun _ => true) asymCRF 1) 0 = 0 := by
  simp [crfPath, bestPath, asym_argmaxVec_one, asym_back_zero]

example : (crfPath (fun _ => true) asymCRF 1) 1 = 0 := by
  simp only [crfPath, bestPath, asym_argmaxVec_one]
  rw [show (1 : Fin 2) = Fin.last 1 from rfl, Fin.snoc_last]

example : (crfPath (fun _ => true) asymCRF 0) 0 = 0 := by
  simp [crfPath, bestPath, asym_argmaxVec_zero]

example : (crfPath (fun _ => true) asymCRF 0) 1 = 0 := by
  simp [crfPath, bestPath, asym_argmaxVec_zero]

/-- Conditional probabilities over `ℝ≥0` sum to `1`: normalization needs only a
semifield, since `ℝ≥0` is not a field. -/
example : ∑ z : Fin 2 → Fin 2, condProb nnCRF (fun _ => true) 1 z = 1 :=
  sum_condProb_eq_one nnCRF (fun _ => true) 1 (by simp [partition, pathWeight, nnCRF])

#print axioms partition_eq_sum_forward
#print axioms sup'_viterbi_eq
#print axioms sum_condProb_eq_one
#print axioms hmmToCRF_pathWeight

end Cslib.MachineLearning.GraphicalModels.ConditionalRandomField
