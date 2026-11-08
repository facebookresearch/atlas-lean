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
# Moving sofa catalogue bounds: unproved public requests

Source: Optimization Problems, constants/41a.md, revision
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`. The full source and variant ledger
is `WantedExt/Sources/MovingSofa.md`.

These requests retain printed inequalities, not proofs or exact shape areas.
No Baek numerical upper endpoint or maximum-attainment request is introduced.
The Gerver row is only the printed lower target, not an exact Gerver optimum.
The primary texts, constructions and numerical certificate are not retained.
-/

open scoped ENNReal

@[expose] public section

namespace MovingSofaWanted

/-- Source: catalogue line 13, attributed to Hammersley (1968). Primary not retained. -/
public theorem_wanted hammersley_upper :
    MovingSofa.optimalArea ≤ ENNReal.ofReal (2 * Real.sqrt 2)

/-- Source: catalogue line 14, Kallus-Romik (2018). Numerical certificate not retained. -/
public theorem_wanted kallus_romik_upper :
    MovingSofa.optimalArea ≤ ENNReal.ofReal ((237 : ℝ) / 100)

/-- Source: catalogue line 21, Hammersley (1968). Construction not retained. -/
public theorem_wanted hammersley_lower :
    ENNReal.ofReal (Real.pi / 2 + 2 / Real.pi) ≤ MovingSofa.optimalArea

/-- Source: catalogue line 22, printed Gerver lower target, not an exact area formula. -/
public theorem_wanted gerver_printed_lower :
    ENNReal.ofReal ((4439 : ℝ) / 2000) ≤ MovingSofa.optimalArea

end MovingSofaWanted
