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

namespace PhyslibExtTest.BiomedicalImaging.PhotonCTInstance

open PhyslibExt.BiomedicalImaging.PhotonCTInstance

/-- Equal transmitted intensities at unit incident intensity. -/
example : (1:ℝ) * Real.exp (-(ctRow *ᵥ ![1, 0]) 0) =
    (1:ℝ) * Real.exp (-(ctRow *ᵥ ![0, 1]) 0) :=
  ct_equal_rates 1

end PhyslibExtTest.BiomedicalImaging.PhotonCTInstance
