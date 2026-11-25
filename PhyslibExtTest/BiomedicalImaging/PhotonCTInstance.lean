/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.BiomedicalImaging.PhotonCTInstance

/-! Tests: the nullspace pair gives equal rates. -/

open Matrix
open scoped NNReal

namespace PhyslibExtTest.BiomedicalImaging.PhotonCTInstance

open PhyslibExt.BiomedicalImaging.PhotonCTInstance

/-- Equal photon laws at unit incident intensity. -/
example : PhyslibExt.BiomedicalImaging.PhotonObservation.photonLaw (fun _ => (1:ℝ≥0)) ctRow ![1, 0] =
    PhyslibExt.BiomedicalImaging.PhotonObservation.photonLaw (fun _ => (1:ℝ≥0)) ctRow ![0, 1] :=
  ct_photon_law_pair _

/-- Equal photon laws also at zero incident intensity. -/
example : PhyslibExt.BiomedicalImaging.PhotonObservation.photonLaw (fun _ => (0:ℝ≥0)) ctRow ![1, 0] =
    PhyslibExt.BiomedicalImaging.PhotonObservation.photonLaw (fun _ => (0:ℝ≥0)) ctRow ![0, 1] :=
  ct_photon_law_pair _

end PhyslibExtTest.BiomedicalImaging.PhotonCTInstance
