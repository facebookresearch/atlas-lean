/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.MachineLearning.OneHiddenLayerNet
import CSLibExt.MachineLearning.InterpolationExpressivity
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace CSLibExtTest.MachineLearning.InterpolationExpressivity

open Cslib.MachineLearning.InterpolationExpressivity
open Cslib.MachineLearning.OneHiddenLayerNet

def threePoints : Fin 3 → EuclideanSpace ℝ (Fin 2) :=
  ![WithLp.toLp 2 ![0, 0], WithLp.toLp 2 ![1, 0], WithLp.toLp 2 ![0, 1]]

def threeLabels : Fin 3 → ℝ := ![1, 2, 3]

example : ∃ (a : EuclideanSpace ℝ (Fin 2)) (b w : Fin 3 → ℝ), ∀ i,
    (oneHiddenLayerNet 2 3 (fun x => max x 0) (fun _ => a) (fun j => -b j) w).forward
      2 (threePoints i) 0 = threeLabels i := by
  have hz : Function.Injective threePoints := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · have h0 := congrArg (fun v => v 0) hij
      simp [threePoints] at h0
    · have h1 := congrArg (fun v => v 1) hij
      simp [threePoints] at h1
    · have h0 := congrArg (fun v => v 0) hij
      simp [threePoints] at h0
    · rfl
    · have h0 := congrArg (fun v => v 0) hij
      simp [threePoints] at h0
    · have h1 := congrArg (fun v => v 1) hij
      simp [threePoints] at h1
    · have h0 := congrArg (fun v => v 0) hij
      simp [threePoints] at h0
    · rfl
  exact exists_interpolating_net 3 2 threePoints hz threeLabels

def emptyPoints : Fin 0 → EuclideanSpace ℝ (Fin 2) := fun i => Fin.elim0 i

def emptyLabels : Fin 0 → ℝ := fun i => Fin.elim0 i

example : ∃ (a : EuclideanSpace ℝ (Fin 2)) (b w : Fin 0 → ℝ), ∀ i,
    (oneHiddenLayerNet 2 0 (fun x => max x 0) (fun _ => a) (fun j => -b j) w).forward
      2 (emptyPoints i) 0 = emptyLabels i := by
  have hz : Function.Injective emptyPoints := fun i => Fin.elim0 i
  exact exists_interpolating_net 0 2 emptyPoints hz emptyLabels

def singlePoint : Fin 1 → EuclideanSpace ℝ (Fin 2) :=
  ![WithLp.toLp 2 ![5, 7]]

def singleLabel : Fin 1 → ℝ := ![42]

example : ∃ (a : EuclideanSpace ℝ (Fin 2)) (b w : Fin 1 → ℝ), ∀ i,
    (oneHiddenLayerNet 2 1 (fun x => max x 0) (fun _ => a) (fun j => -b j) w).forward
      2 (singlePoint i) 0 = singleLabel i := by
  have hz : Function.Injective singlePoint := by
    intro i j _
    fin_cases i
    fin_cases j
    rfl
  exact exists_interpolating_net 1 2 singlePoint hz singleLabel

#print axioms Cslib.MachineLearning.InterpolationExpressivity.exists_interpolating_net

end CSLibExtTest.MachineLearning.InterpolationExpressivity
