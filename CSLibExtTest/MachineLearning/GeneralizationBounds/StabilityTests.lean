/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.GeneralizationBounds.Stability
import Mathlib.Probability.UniformOn

open MeasureTheory

namespace CSLibExt.MachineLearning.GeneralizationBounds

-- A constant algorithm is `0`-uniformly stable.
example {𝒵 H : Type*} (L : H → 𝒵 → ℝ) (h : H) :
    IsUniformlyStable (n := 3) L (fun _ => h) 0 := by
  intro S i z' z
  simp

-- The algorithm returning the first example, with a loss in `[0, 1]`, is `1`-uniformly stable.
example : IsUniformlyStable (n := 2) (fun (w : ℝ) (z : ℝ) => min 1 |w - z|)
    (fun S => S 0) 1 := by
  intro S i z' z
  have h1 : min 1 |Function.update S i z' 0 - z| ≤ 1 := min_le_left _ _
  have h2 : 0 ≤ min 1 |S 0 - z| := le_min zero_le_one (abs_nonneg _)
  linarith

-- Replace-one sampling preserves the law of an i.i.d. sample (here of two uniform bits).
example (i : Fin 2) :
    ((Measure.pi fun _ : Fin 2 => ProbabilityTheory.uniformOn (Set.univ : Set Bool)).prod
        (ProbabilityTheory.uniformOn (Set.univ : Set Bool))).map
      (fun p => Function.update p.1 i p.2) =
      Measure.pi fun _ : Fin 2 => ProbabilityTheory.uniformOn (Set.univ : Set Bool) :=
  map_update_prod_pi _ i

-- The generalization theorem applies, with gap `0`, to a constant algorithm and a bounded
-- measurable loss; the hypotheses are satisfiable.
example (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    |∫ S, (empiricalRisk (fun (w : ℝ) (z : ℝ) => min 1 |w - z|) S ((fun _ => (0 : ℝ)) S) -
        risk (fun (w : ℝ) (z : ℝ) => min 1 |w - z|) ν ((fun _ => (0 : ℝ)) S))
        ∂(Measure.pi fun _ : Fin 4 => ν)| ≤ 0 := by
  refine abs_integral_empiricalRisk_sub_risk_le ?_ (M := 1) ?_ ?_
  · fun_prop
  · intro S z
    rw [abs_of_nonneg (le_min zero_le_one (abs_nonneg _))]
    exact min_le_left _ _
  · intro S i z' z
    simp

end CSLibExt.MachineLearning.GeneralizationBounds
