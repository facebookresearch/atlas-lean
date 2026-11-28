/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.WeightedProjectiveSimplexCoefficients

/-! # Boundary cases for the almost-IDP coefficient vector -/

open MetaMathlibExt

-- The even geometric sum has no terms at zero.
example : evenGeometricFactor 0 = 0 := by simp [evenGeometricFactor]

-- At the lower bound the repeated block is empty.
example : List.ofFn (fun k : Fin 7 => (evenGeometricFactor 2 * almostIDPQuartic).coeff k.val) =
    [1, 7, 15, 14, 15, 7, 1] := by
  exact almostIDP_hStar_coefficients 2 (by decide)

-- The next product contains the first pair of interior coefficients.
example : List.ofFn (fun k : Fin 9 => (evenGeometricFactor 3 * almostIDPQuartic).coeff k.val) =
    [1, 7, 15, 14, 16, 14, 15, 7, 1] := by
  exact almostIDP_hStar_coefficients 3 (by decide)
