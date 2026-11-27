/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.MachineLearning.PACLearning.NearestNeighbor
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite-sample bound for the 1-nearest-neighbor rule

S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*
(Cambridge University Press, 2014), §§19.1 and 19.2, Theorem 19.3 ([author copy][uml]).

The cube inherits the Euclidean metric and Borel sigma-algebra from `EuclideanSpace`.
The sample risk is integrable by `integrable_oneNearestNeighbor_error`; the probability
of a test error is the mass of a measurable set for each sample by joint measurability
of the prediction. The Lipschitz hypothesis makes `η` and its Bayes threshold measurable.

[uml]: https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/
-/

@[expose] public section

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory
open scoped NNReal

local notation "Cube" d:arg => @Subtype (EuclideanSpace ℝ (Fin d))
  (fun x => WithLp.ofLp x ∈ Set.pi (Set.univ : Set (Fin d)) (fun _ : Fin d => unitInterval))

/-- **Finite-sample bound for the 1-nearest-neighbor rule** (Shalev-Shwartz and Ben-David,
Theorem 19.3). Let `d, m ≥ 1` and `D` be a probability law on the Euclidean Borel cube
`[0, 1]^d` times the discrete labels `false` (0) and `true` (1). Suppose `η` takes values in
`[0, 1]` and is `c`-Lipschitz for `c > 0`. Assume `η` is a version of the conditional
probability of label 1: for every measurable `A` in the cube, the mass of `A × {1}` under `D`
is the integral of `η` over `A` against the feature marginal of `D`.

For `m` i.i.d. examples `S` from `D`, predict the label of the closest sample point, using the
least index in a tie. The expected 0-1 risk of this rule is at most twice the 0-1 risk of
predicting 1 exactly when `η(x) > 1/2`, plus `4 c √d m^(-1/(d+1))`. Here the 0-1 risk is
the probability of misclassification under `D`. -/
theorem_wanted expected_error_oneNearestNeighbor_le {d m : ℕ} (hd : 0 < d) [NeZero m]
    (D : Measure (Cube d × Bool)) [IsProbabilityMeasure D]
    (η : Cube d → unitInterval) {c : ℝ≥0} (hc : 0 < c) (hLip : LipschitzWith c η)
    (hη : ∀ A : Set (Cube d), MeasurableSet A →
      D (A ×ˢ {true}) = ∫⁻ x in A, ENNReal.ofReal (η x : ℝ) ∂D.fst) :
    (∫ S, (error D (oneNearestNeighbor S)).toReal ∂(Measure.pi fun _ : Fin m => D)) ≤
      2 * (error D (binaryBayesClassifier η)).toReal +
        4 * (c : ℝ) * Real.sqrt d * (m : ℝ) ^ (-1 / ((d : ℝ) + 1))

end Cslib.MachineLearning.PACLearning
