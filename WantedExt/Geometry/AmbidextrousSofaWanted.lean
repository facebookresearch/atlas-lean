/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Geometry.MovingSofa

/-!
# Ambidextrous moving-sofa catalogue bounds: unproved requests

Source: Optimization Problems, constants/41b.md, revision
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; SHA-256
`e14e62660245f08f00684cc15b85ac1e2d2697d28787d2ef30b51af06269be76`.
The full source ledger is the C41b section of
`WantedExt/Sources/MovingSofa.md`.

The Lean constant is `MovingSofa.ambidextrousOptimalArea`: the `ENNReal`
supremum over shapes that are ordinary sofas (`IsSofa`) and also pass, in a
single continuous passage, a Z corridor `corridorZ d` at every
sufficiently large corner separation `d` (entrance arm
`0 ≤ Im z ≤ 1`, bounded middle channel of height `2 + d`, exit arm
`1 + d ≤ Im z ≤ 2 + d`; formally `∃ D, ∀ d ≥ D, CanPassZAt K d`, the
eventual/atTop form). This encodes the catalogue's "sufficiently
separated corners". Two separate passages (ordinary plus mirrored)
would not suffice and are not the model. Remaining gap: the threshold
`D` is not compared with any specific separation in the catalogue
constructions, which are not formalized.
-/

open scoped ENNReal

namespace AmbidextrousSofaWanted

/-- Source: catalogue upper row, Hammersley (1968), adapted from C41a. -/
theorem_wanted hammersley_upper :
    MovingSofa.ambidextrousOptimalArea ≤ ENNReal.ofReal (2 * Real.sqrt 2)

/-- Source: catalogue upper row, Baek (2024) naive bound from C41a,
exact decimal endpoint `22195 / 10000`. -/
theorem_wanted baek_upper :
    MovingSofa.ambidextrousOptimalArea ≤
      ENNReal.ofReal ((22195 : ℝ) / 10000)

/-- Source: catalogue lower row, Gibbs (2014) numerical construction,
exact decimal endpoint `164495 / 100000`. -/
theorem_wanted gibbs_lower :
    ENNReal.ofReal ((164495 : ℝ) / 100000) ≤
      MovingSofa.ambidextrousOptimalArea

/-- Source: catalogue lower row, Romik (2016), exact decimal endpoint
`164495521 / 100000000`. -/
theorem_wanted romik_lower :
    ENNReal.ofReal ((164495521 : ℝ) / 100000000) ≤
      MovingSofa.ambidextrousOptimalArea

end AmbidextrousSofaWanted
