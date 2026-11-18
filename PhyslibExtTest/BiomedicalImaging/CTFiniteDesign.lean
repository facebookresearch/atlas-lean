/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.BiomedicalImaging.CTFiniteDesign

/-! Tests: design linearity under a zero measure is `0 = 0`. -/

namespace PhyslibExtTest.BiomedicalImaging.CTFiniteDesign

open PhyslibExt.BiomedicalImaging.CTFiniteDesign

/-- Under the zero measure both sides vanish. -/
example (phi : Fin 2 → ℝ → ℝ) (x : Fin 2 → ℝ) :
    (∫ a, (∑ i ∈ Finset.univ, x i * phi i a) ∂(0 : MeasureTheory.Measure ℝ)) =
      ∑ i ∈ Finset.univ, x i * (∫ a, phi i a ∂(0 : MeasureTheory.Measure ℝ)) :=
  ct_design_apply _ _ _ (fun i _ => MeasureTheory.integrable_zero_measure)

end PhyslibExtTest.BiomedicalImaging.CTFiniteDesign
