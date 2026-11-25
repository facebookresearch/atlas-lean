/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WatsonCotangentDerivatives

open MetaMathlibExt

-- The first derivative at the smallest admissible denominator, where cotangent is zero.
example : watsonOddCotangentDeriv 1 2 1 < 0 :=
  watson_odd_cotangent_deriv_neg 1 2 1 (hr := by decide)
    (hνpos := by decide) (hνmax := by decide)

-- The third derivative at the largest admissible numerator for denominator three.
example : watsonOddCotangentDeriv 2 3 2 < 0 :=
  watson_odd_cotangent_deriv_neg 2 3 2 (by decide) (by decide) (by decide)
