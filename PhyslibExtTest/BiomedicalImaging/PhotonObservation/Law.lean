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

/-- Rectangular case: two rays, three cells, `A = ![![1,0,0],![0,1,0]]`
reads the first two cells. -/
example {x x' : Fin 3 → ℝ} :
    photonLaw (fun _ => (1 : ℝ≥0)) ![![1, 0, 0], ![0, 1, 0]] x =
      photonLaw (fun _ => (1 : ℝ≥0)) ![![1, 0, 0], ![0, 1, 0]] x' ↔
    ![![1, 0, 0], ![0, 1, 0]] *ᵥ x = ![![1, 0, 0], ![0, 1, 0]] *ᵥ x' :=
  photon_law_agree_iff (fun _ => one_pos)

/-- Identification on the whole space for the injective one-ray design. -/
example :
    Set.InjOn (fun x : Fin 1 → ℝ => photonLaw (fun _ => (1 : ℝ≥0)) ![![2]] x) Set.univ ↔
      Set.InjOn (fun x : Fin 1 → ℝ => ![![2]] *ᵥ x) Set.univ :=
  photon_identify_iff (fun _ => one_pos) ![![2]] Set.univ

/-- Kernel vector `(0, 1)` for `![![1, 0]]` defeats identification on the whole space. -/
example :
    ¬ Set.InjOn (fun x : Fin 2 → ℝ =>
      photonLaw (fun _ => (1 : ℝ≥0)) ![![1, 0]] x) Set.univ :=
  photon_not_identify_of_kernel ![![1, 0]] Set.univ
    (by intro h; have hh := congrFun h 1; simp at hh) (by ext j; fin_cases j; simp [Matrix.mulVec, dotProduct]) (Set.mem_univ 0)
    (Set.mem_univ (0 + ![0, 1]))

end PhyslibExtTest.BiomedicalImaging.PhotonObservation.Law
