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
    (oneHiddenLayerNet 2 3 (fun x => x⁺) (fun _ => a) (fun j => -b j) w).forward
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
    (oneHiddenLayerNet 2 0 (fun x => x⁺) (fun _ => a) (fun j => -b j) w).forward
      2 (emptyPoints i) 0 = emptyLabels i := by
  have hz : Function.Injective emptyPoints := fun i => Fin.elim0 i
  exact exists_interpolating_net 0 2 emptyPoints hz emptyLabels

def singlePoint : Fin 1 → EuclideanSpace ℝ (Fin 2) :=
  ![WithLp.toLp 2 ![5, 7]]

def singleLabel : Fin 1 → ℝ := ![42]

example : ∃ (a : EuclideanSpace ℝ (Fin 2)) (b w : Fin 1 → ℝ), ∀ i,
    (oneHiddenLayerNet 2 1 (fun x => x⁺) (fun _ => a) (fun j => -b j) w).forward
      2 (singlePoint i) 0 = singleLabel i := by
  have hz : Function.Injective singlePoint := by
    intro i j _
    fin_cases i
    fin_cases j
    rfl
  exact exists_interpolating_net 1 2 singlePoint hz singleLabel

def triB : Fin 2 → ℝ := ![0, 2]

def triX : Fin 2 → ℝ := ![1, 3]

def triY : Fin 2 → ℝ := ![1, 3]

example : ∃ w : Fin 2 → ℝ, ∀ i, (∑ j, w j * (triX i - triB j)⁺) = triY i := by
  have hb : ∀ i, triB i < triX i := by
    intro i
    fin_cases i <;> simp only [triB, triX] <;> norm_num
  have htri : ∀ i j, i < j → triX i < triB j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd hij (by decide)
    · simp only [triX, triB]
      norm_num
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
  exact interleaving_interpolation 2 triB triX hb htri triY

example : ∀ i, (∑ j, ![1, 0] j * (triX i - triB j)⁺) = triY i := by
  intro i
  fin_cases i
  · norm_num [triX, triB, triY]
  · norm_num [triX, triB, triY]

#print axioms Cslib.MachineLearning.InterpolationExpressivity.exists_separating_direction
#print axioms Cslib.MachineLearning.InterpolationExpressivity.interleaving_interpolation
#print axioms Cslib.MachineLearning.InterpolationExpressivity.exists_interpolating_net

end CSLibExtTest.MachineLearning.InterpolationExpressivity
