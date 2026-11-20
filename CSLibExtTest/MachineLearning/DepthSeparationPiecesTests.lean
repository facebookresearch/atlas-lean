/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.MachineLearning.DepthSeparationPieces
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Tests for piece-count bounds of univariate ReLU networks
-/

namespace CSLibExtTest.MachineLearning.DepthSeparationPieces

open Cslib.MachineLearning.Backpropagation
open Cslib.MachineLearning.DepthSeparationPieces

/-- Identity base case. -/
example : PiecesLE 1 (fun x : ℝ => x) := by exact piecesLE_id

/-- Constant base case. -/
example : PiecesLE 1 (fun _ : ℝ => (3 : ℝ)) := by exact piecesLE_const 3

/-- ReLU base case. -/
example : PiecesLE 2 (fun x : ℝ => x⁺) := by exact piecesLE_relu

/-- A concrete one-layer width function: input width one, output width two. -/
def widths12 : ℕ → ℕ
  | 0 => 1
  | _ => 2

/-- The ReLU-network predicate is inhabited: the zero network. -/
example : IsReluNet widths12 ⟨fun _ _ => 0⟩ := by
  intro k
  refine ⟨0, 0, ?_⟩
  intro x j
  simp

/-- One-layer bound instance: any output coordinate has at most two pieces. -/
example (Nnet : Net widths12) (hN : IsReluNet widths12 Nnet)
    (j : Fin (widths12 1)) :
    PiecesLE 2 (fun x => (Nnet.forward 1 (inputVec widths12 x)) j) := by
  have hpos : ∀ k, 0 < widths12 k := by
    intro k
    cases k with
    | zero => decide
    | succ n => show (0:ℕ) < 2; decide
  have h := node_piecesLE widths12 Nnet hN rfl hpos 1 j
  have hbound : (2 ^ 1) * ∏ k ∈ Finset.Icc 1 (1 - 1), widths12 k = 2 := by simp
  rw [hbound] at h
  exact h

/-- Sum-rule instance: two shifted ReLUs have at most four pieces in total. -/
example : PiecesLE 4 ((fun x : ℝ => x⁺) + (fun x : ℝ => (x - 1)⁺)) := by
  have h1 : PiecesLE 2 (fun x : ℝ => x⁺) := piecesLE_relu
  have haff : PiecesLE 1 (fun x : ℝ => 1 * x + -1) := piecesLE_affine 1 (-1)
  have hfun : (fun x : ℝ => 1 * x + -1) = fun x => x - 1 := by
    funext x
    simp [sub_eq_add_neg]
  have hshift : PiecesLE 1 (fun x : ℝ => x - 1) := by rwa [hfun] at haff
  have hrelu2 : PiecesLE 2 (fun x : ℝ => (x - 1)⁺) := piecesLE_relu_comp 1 _ hshift
  simpa using piecesLE_add 2 2 (fun x : ℝ => x⁺) (fun x : ℝ => (x - 1)⁺) h1 hrelu2

/-- Sum-rule instance values. -/
example (f g : ℝ → ℝ) (hf : f = fun x => x⁺)
    (hg : g = fun x => (x - 1)⁺) :
    (f + g) (-1) = 0 ∧ (f + g) (1 / 2) = 1 / 2 ∧ (f + g) 2 = 3 := by
  simp only [hf, hg, Pi.add_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [posPart_eq_zero.mpr (show (-1 : ℝ) ≤ 0 by norm_num),
      posPart_eq_zero.mpr (show (-1 : ℝ) - 1 ≤ 0 by norm_num)]
    norm_num
  · rw [posPart_eq_self.mpr (show (0 : ℝ) ≤ 1 / 2 by norm_num),
      posPart_eq_zero.mpr (show (1 : ℝ) / 2 - 1 ≤ 0 by norm_num)]
    norm_num
  · rw [posPart_eq_self.mpr (show (0 : ℝ) ≤ 2 by norm_num),
      posPart_eq_self.mpr (show (0 : ℝ) ≤ (2 : ℝ) - 1 by norm_num)]
    norm_num

/-- A network whose layers output zero has one-piece output. -/
example (d : ℕ → ℕ) (L : ℕ) (hL : 0 < L) (Nnet : Net d)
    (hzero : ∀ (k : ℕ) (x : EuclideanSpace ℝ (Fin (d k))),
      Nnet.layer k x = 0)
    (j : Fin (d L)) :
    PiecesLE 1 (fun x => (Nnet.forward L (inputVec d x)) j) := by
  obtain ⟨L', rfl⟩ := (⟨L - 1, by omega⟩ : ∃ L', L = L' + 1)
  have hfun : (fun x => (Nnet.forward (L' + 1) (inputVec d x)) j) = fun _ => 0 :=
    funext fun x => by simp only [Net.forward, hzero, PiLp.zero_apply]
  rw [hfun]
  exact piecesLE_const 0

/-- Nothing has zero pieces, in particular the identity. -/
example : ¬ PiecesLE 0 id := by exact piecesLE_zero_none id

#print axioms piecesLE_relu_comp
#print axioms node_piecesLE
#print axioms net_piecesLE

end CSLibExtTest.MachineLearning.DepthSeparationPieces
