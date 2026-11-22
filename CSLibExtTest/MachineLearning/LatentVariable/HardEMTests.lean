/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.HardEM

/-!
# Hard-EM limit tests

Closed checks: the zero-variance limit instantiated for three components in the plane.
- A point with a unique nearest mean has responsibilities tending to its nearest-mean indicator.
- A dataset with unique nearest means gets the `KMeans.Nearest` assignment as the limit.
- The M-step mean of a nonempty cluster tends to its k-means centroid.

The definitions are real-valued and not executable.
-/

namespace Cslib.MachineLearning.LatentVariable.HardEM

open Filter Topology

example (w : Fin 3 → ℝ) (hw : ∀ k, 0 < w k) (μ : Fin 3 → EuclideanSpace ℝ (Fin 2))
    (x : EuclideanSpace ℝ (Fin 2)) (h1 : ‖x - μ 0‖ < ‖x - μ 1‖) (h2 : ‖x - μ 0‖ < ‖x - μ 2‖) :
    Tendsto (fun v : ℝ => softAssign w μ v x 0) (𝓝[>] 0) (𝓝 1) := by
  have := tendsto_softAssign hw μ x (j := 0) (fun k hk => by
    fin_cases k
    · exact absurd rfl hk
    · exact h1
    · exact h2) 0
  simpa using this

example (xs : Fin 4 → EuclideanSpace ℝ (Fin 2)) (w : Fin 3 → ℝ) (hw : ∀ k, 0 < w k)
    (μ : Fin 3 → EuclideanSpace ℝ (Fin 2)) (a : Fin 4 → Fin 3)
    (ha : ∀ n k, k ≠ a n → ‖xs n - μ (a n)‖ < ‖xs n - μ k‖) :
    KMeans.Nearest xs μ a :=
  (nearest_and_tendsto_softAssign xs hw μ a ha).1

example (xs : Fin 4 → EuclideanSpace ℝ (Fin 2)) (w : Fin 3 → ℝ) (hw : ∀ k, 0 < w k)
    (μ : Fin 3 → EuclideanSpace ℝ (Fin 2)) (a : Fin 4 → Fin 3)
    (ha : ∀ n k, k ≠ a n → ‖xs n - μ (a n)‖ < ‖xs n - μ k‖) (h0 : a 0 = 1) :
    Tendsto (fun v : ℝ => softMean w μ v xs 1) (𝓝[>] 0) (𝓝 (KMeans.centers xs a 1)) :=
  tendsto_softMean xs hw μ a ha 1 ⟨0, h0⟩

#print axioms tendsto_softAssign
#print axioms tendsto_softMean
#print axioms nearest_and_tendsto_softAssign

end Cslib.MachineLearning.LatentVariable.HardEM
