/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.NearestNeighbor
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

/-!
# Tests for the 1-nearest-neighbor rule

Tests cover ordinary predictions, distance ties, and the strict Bayes threshold of §19.2.1 of
Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms* (2014).
-/

namespace Cslib.MachineLearning.PACLearning

example : oneNearestNeighbor (![(0, true)] : LabeledSample ℝ Bool 1) 4 = true := by
  have hi : nearestNeighborIndex (![0] : Fin 1 → ℝ) 4 = 0 := Subsingleton.elim _ _
  change ((![(0, true)] : LabeledSample ℝ Bool 1)
    (nearestNeighborIndex (![0] : Fin 1 → ℝ) 4)).2 = true
  rw [hi]
  rfl

example : nearestNeighborIndex (![3, 1] : Fin 2 → ℝ) 0 = 1 := by
  rw [nearestNeighborIndex_eq_iff]
  intro j
  fin_cases j <;> norm_num [Real.dist_eq]

example : oneNearestNeighbor (![(3, false), (-1, true), (1, false)] : LabeledSample ℝ Bool 3)
    0 = true := by
  let S : LabeledSample ℝ Bool 3 := ![(3, false), (-1, true), (1, false)]
  have hi : nearestNeighborIndex (fun i => (S i).1) 0 = 1 := by
    rw [nearestNeighborIndex_eq_iff]
    intro j
    fin_cases j <;> norm_num [S, Real.dist_eq]
  change (S (nearestNeighborIndex (fun i => (S i).1) 0)).2 = true
  rw [hi]
  rfl

example : binaryBayesClassifier (fun _ : Unit => ⟨(1 : ℝ) / 2, by norm_num⟩) () = false := by
  simp [binaryBayesClassifier]

example : binaryBayesClassifier (fun _ : Unit => (1 : unitInterval)) () = true := by
  norm_num [binaryBayesClassifier]

end Cslib.MachineLearning.PACLearning
