/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.IntegralGeometry.RadonLineAgreement

/-! Tests: coordinate line in the plane. -/

namespace MathlibExtTest.Analysis.IntegralGeometry.RadonLineAgreement

open MathlibExt.Analysis.IntegralGeometry.RadonLineAgreement

/-- The vertical line through the standard basis pair is the range. -/
example : Set.range (fun s : ℝ => (3:ℝ) • EuclideanSpace.basisFun (Fin 2) ℝ 0 + s • EuclideanSpace.basisFun (Fin 2) ℝ 1) =
    Set.range (fun s : ℝ => (3:ℝ) • EuclideanSpace.basisFun (Fin 2) ℝ 0 + s • (- EuclideanSpace.basisFun (Fin 2) ℝ 1)) :=
  line_range_neg 3

end MathlibExtTest.Analysis.IntegralGeometry.RadonLineAgreement
