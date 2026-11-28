/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.DepthSeparationOscillation

/-!
Tests for the depth-separation oscillation lower bound.
-/

@[expose] public section

namespace CSLibExtTest.MachineLearning.DepthSeparationOscillation

open Cslib.MachineLearning.DepthSeparation
open Cslib.MachineLearning.DepthSeparationPieces
open Cslib.MachineLearning.Backpropagation

-- T1: the `L = 2` iterate `tentIter 6` at a zero, a peak, a half point.
example : tentIter 6 (0 : ℝ) = 0 := by
  show tentIter (5 + 1) (0 : ℝ) = 0
  rw [tentIter_succ_eq_tent_fract 5 0 (by norm_num) (by norm_num)]
  have hmul : (2 : ℝ) ^ 5 * (0 : ℝ) = 0 := by ring
  rw [hmul, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩,
    tent_eq_two_mul _ (by norm_num) (by norm_num)]
  norm_num

example : tentIter 6 ((1 : ℝ) / 64) = 1 := by
  show tentIter (5 + 1) ((1 : ℝ) / 64) = 1
  rw [tentIter_succ_eq_tent_fract 5 ((1 : ℝ) / 64) (by norm_num)
    (by norm_num)]
  have hmul : (2 : ℝ) ^ 5 * ((1 : ℝ) / 64) = 1 / 2 := by norm_num
  rw [hmul, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩,
    tent_eq_two_mul _ (by norm_num) (by norm_num)]
  norm_num

example : tentIter 6 ((1 : ℝ) / 128) = 1 / 2 := by
  show tentIter (5 + 1) ((1 : ℝ) / 128) = 1 / 2
  rw [tentIter_succ_eq_tent_fract 5 ((1 : ℝ) / 128) (by norm_num)
    (by norm_num)]
  have hmul : (2 : ℝ) ^ 5 * ((1 : ℝ) / 128) = 1 / 4 := by norm_num
  rw [hmul, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩,
    tent_eq_two_mul _ (by norm_num) (by norm_num)]
  norm_num

-- T2: the core lemma at `L = 2` for the zero and constant-one functions.
example : (1 / 32 : ℝ) ≤ ∫ x in (0 : ℝ)..1,
    |tentIter (2 ^ 2 + 2) x - 0| := by
  have hz : PiecesLE 1 (fun _ : ℝ => (0 : ℝ)) :=
    ⟨∅, by simp [Finset.card_empty], fun x y z _ _ _ => by simp⟩
  have h1 : ((1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 ^ 2) := by norm_num
  exact tentIter_l1_ge_of_piecesLE 2 (by norm_num) _ hz h1

example : (1 / 32 : ℝ) ≤ ∫ x in (0 : ℝ)..1,
    |tentIter (2 ^ 2 + 2) x - 1| := by
  have hc : PiecesLE 1 (fun _ : ℝ => (1 : ℝ)) :=
    ⟨∅, by simp [Finset.card_empty], fun x y z _ _ _ => by simp⟩
  have h1 : ((1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 ^ 2) := by norm_num
  exact tentIter_l1_ge_of_piecesLE 2 (by norm_num) _ hc h1

-- T3: the deep realization identity at `L = 2`, plus axiom audits.
example : ∀ x : ℝ, (tentNet.forward (2 * (2 ^ 2 + 2)) (single x)) 0
    = tentIter (2 ^ 2 + 2) x :=
  fun x => tentNet_forward _ x

-- The shallow-network corollary at `L = 2`, applied to an explicit network.
example (d : ℕ → ℕ) (Nnet : Net d) (M : ℕ) (hM0 : 0 < M) (hM : M ≤ 2)
    (hN : IsReluNetUpTo d Nnet M) (hd0 : d 0 = 1) (hdM : d M = 1)
    (hpos : ∀ j < M, 0 < d j)
    (hsum : ((∑ i ∈ Finset.Icc 1 M, d i) : ℝ) ≤ (2 : ℝ) ^ 2) :
    (1 / 32 : ℝ) ≤ ∫ x in (0 : ℝ)..1,
      |tentIter (2 ^ 2 + 2) x - (Nnet.forward M (inputVec d x)) ⟨0, by omega⟩| := by
  exact tentIter_l1_ge_of_reluNet 2 (by norm_num) d Nnet M hM0 hM hN hd0 hdM
    hpos hsum

-- The depth-separation conjunction at `L = 2`, projecting both components.
example (d : ℕ → ℕ) (Nnet : Net d) (M : ℕ) (hM0 : 0 < M) (hM : M ≤ 2)
    (hN : IsReluNetUpTo d Nnet M) (hd0 : d 0 = 1) (hdM : d M = 1)
    (hpos : ∀ j < M, 0 < d j)
    (hsum : ((∑ i ∈ Finset.Icc 1 M, d i) : ℝ) ≤ (2 : ℝ) ^ 2) :
    (∀ x : ℝ, (tentNet.forward (2 * (2 ^ 2 + 2)) (single x)) 0
        = tentIter (2 ^ 2 + 2) x) ∧
    (1 / 32 : ℝ) ≤ ∫ x in (0 : ℝ)..1,
      |tentIter (2 ^ 2 + 2) x - (Nnet.forward M (inputVec d x)) ⟨0, by omega⟩| := by
  have hsep := depth_separation 2 (by norm_num) d Nnet M hM0 hM hN hd0 hdM
    hpos hsum
  exact ⟨fun x => hsep.1 x, hsep.2⟩

#print axioms tentIter_l1_ge_of_piecesLE
#print axioms tentIter_l1_ge_of_reluNet
#print axioms depth_separation

end CSLibExtTest.MachineLearning.DepthSeparationOscillation
