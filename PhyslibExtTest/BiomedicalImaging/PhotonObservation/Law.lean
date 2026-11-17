/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.BiomedicalImaging.PhotonObservation.Law

/-! Tests for the photon law: a one-ray nonzero attenuation case where
equal laws force equal attenuation, and zero attenuation. -/

namespace PhyslibExtTest.BiomedicalImaging.PhotonObservation.Law

open PhyslibExt.BiomedicalImaging.PhotonObservation Matrix
open scoped NNReal

/-- One ray, unit intensity, `A = ![![2]]`: laws at `x` and `x'`
agree iff `2 * x = 2 * x'`. -/
example {x x' : Fin 1 → ℝ} :
    photonLaw (fun _ => (1 : ℝ≥0)) ![![2]] x = photonLaw (fun _ => (1 : ℝ≥0)) ![![2]] x' ↔
    ![![2]] *ᵥ x = ![![2]] *ᵥ x' :=
  photon_law_agree_iff (fun _ => one_pos)

/-- Zero attenuation: the transmitted rate is the source intensity. -/
example : transmittedRate (fun _ => (3 : ℝ≥0)) ![![0]] (fun _ => (5 : ℝ)) 0 = 3 := by
  simp [transmittedRate, Matrix.mulVec, dotProduct]

end PhyslibExtTest.BiomedicalImaging.PhotonObservation.Law
