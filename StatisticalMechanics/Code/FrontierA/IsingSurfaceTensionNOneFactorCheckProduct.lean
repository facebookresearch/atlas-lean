/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSurfaceTensionNOneFactorGenerated

namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in

theorem generatedClearedSkewPoly_eq_factors :
    generatedClearedSkewPoly =
      generatedQuotientPoly * BiPoly.xSquareSubOne *
        BiPoly.ySquareSubOne := by
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
