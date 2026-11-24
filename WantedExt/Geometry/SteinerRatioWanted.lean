/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Geometry.SteinerRatio

@[expose] public section

namespace MathlibExt.Geometry.SteinerRatioWanted

open MathlibExt.Geometry.SteinerRatio

/-!
# Catalogue bounds for the Steiner ratio

The classical published bounds from Optimization Problems record 43a,
as proof requests against `steinerRatioConstant`. The stronger 2026
catalogue rows (`0.8559`, and `0.860` asterisked) are computer-assisted
and conditional on the KHSHGW2026 lemma layer, so they are recorded in
the Sources entry and omitted here. The Gilbert--Pollak conjecture
(`GilbertPollakConjecture`) remains open and is not asserted.
-/

/-- **Gilbert–Pollak upper bound for the Steiner ratio.** The Steiner ratio constant, the infimum
over finite sets $V$ of at least two points in the Euclidean plane of the length of a Steiner
minimal tree for $V$ divided by the length of a minimum spanning tree of $V$, is at most
$\sqrt{3}/2$.

Source: Gilbert and Pollak, *Steiner minimal trees* (1968): the
equilateral triangle gives the upper bound `√3 / 2`. Known literature
result; the triangle computation is not supplied here. -/
theorem_wanted gilbertPollakUpperBound_wanted :
    steinerRatioConstant ≤ Real.sqrt 3 / 2

/-- **Chung–Graham lower bound for the Steiner ratio.** The Steiner ratio constant, the infimum
over finite sets $V$ of at least two points in the Euclidean plane of the length of a Steiner
minimal tree for $V$ divided by the length of a minimum spanning tree of $V$, is at least $0.824$.

Source: Chung and Graham (1985), via the frozen catalogue's best
unconditional published lower bound `0.824` before the conditional 2026
computer-assisted rows. Known literature result; its proof is not
supplied here. -/
theorem_wanted chungGrahamLowerBound_wanted :
    (824 / 1000 : ℝ) ≤ steinerRatioConstant

end MathlibExt.Geometry.SteinerRatioWanted
