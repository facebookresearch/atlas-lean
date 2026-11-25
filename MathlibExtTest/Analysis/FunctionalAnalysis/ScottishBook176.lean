/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook176

open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook176Wanted

-- Check the refutation with the claim unfolded, including both inverse hypotheses.
example :
    ¬ (∀ (A : Type) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
      (a b : A), a * b = 1 → b * a = 1 →
      ∃ p : ℕ → Polynomial ℝ,
        Filter.Tendsto (fun n => Polynomial.aeval a (p n)) Filter.atTop (nhds b)) :=
  eidelheit176_refuted

-- In the scalar algebra, constant polynomials already give exact approximation.
example (a b : ℝ) :
    Filter.Tendsto (fun _ : ℕ => Polynomial.aeval a (Polynomial.C b)) Filter.atTop (nhds b) := by
  simp
