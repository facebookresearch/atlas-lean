/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSurfaceTensionNOneFactorGenerated

namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in


theorem generatedQuotientPoly_shiftToOne :
    generatedQuotientPoly.shiftToOne = generatedShiftedQuotientPoly := by
  rfl

set_option maxRecDepth 100000 in
theorem generatedQuotientPoly_exponents_nonnegative :
    ∀ t ∈ generatedQuotientPoly.terms, 0 ≤ t.ex ∧ 0 ≤ t.ey := by
  decide

set_option maxRecDepth 100000 in
theorem generatedShiftedQuotientPoly_coefficients_nonnegative :
    ∀ t ∈ generatedShiftedQuotientPoly.terms, 0 ≤ t.coeff := by
  decide

end StatMech.FrontierA.NOneSymmetricMeanCertificate
