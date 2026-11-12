/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSurfaceTensionNOneBlocksGenerated
import Code.FrontierA.IsingSurfaceTensionNOneFactorGenerated

namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in


theorem clearedSkewPoly_eq_generated :
    clearedSkewPoly = generatedClearedSkewPoly := by
  unfold clearedSkewPoly
  rw [rawMomentPoly_eq_generated]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
