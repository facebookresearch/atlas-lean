/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.MovingSofaHammersley

/-!
# Hammersley upper bound for the ambidextrous sofa

`AmbidextrousSofaWanted.hammersley_upper` bounds the ambidextrous optimal area by
twice the square root of two: every ambidextrous sofa is a sofa, so Hammersley's
bound for ordinary sofas applies.
-/

namespace AmbidextrousSofaWanted

/-- **Hammersley upper bound for the ambidextrous sofa.** The supremum of the areas of
ambidextrous sofas, taken in $[0, \infty]$, is at most $2\sqrt{2}$.

Source: catalogue upper row, Hammersley (1968), adapted from C41a. -/
public theorem hammersley_upper :
    MovingSofa.ambidextrousOptimalArea ≤ ENNReal.ofReal (2 * Real.sqrt 2) :=
  MovingSofa.ambidextrousOptimalArea_le_optimalArea.trans
    MovingSofaWanted.hammersley_upper

end AmbidextrousSofaWanted
