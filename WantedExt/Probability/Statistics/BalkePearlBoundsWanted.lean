/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Balke–Pearl bounds: width at most the noncompliance rate

Let `Z` (assignment), `D` (treatment received) and `Y` (response) be binary, with `Z` randomized
and affecting `Y` only through `D`. The model, its sixteen response types, the observed law
`q.obs y d z = P(Y = y, D = d | Z = z)` of a type law `q`, and the Balke–Pearl bounds (4) and (5)
on the average causal effect are those of
`CSLibExt.MachineLearning.GraphicalModels.BalkePearlBounds`, which proves the bounds sound
(`lowerBound_le_ace`, `ace_le_upperBound`), sharp (`isLeast_ace_fiber`, `isGreatest_ace_fiber`)
and the instrumental inequalities (6) (`instrumental_inequalities`).

Recorded here is the remaining statement of Balke and Pearl (1997, p. 1173): the width of the
bounds never exceeds the noncompliance rate `P(D = 1 | Z = 0) + P(D = 0 | Z = 1)`.

Sources: A. Balke and J. Pearl, "Bounds on treatment effects from studies with imperfect
compliance", J. Amer. Statist. Assoc. 92 (1997) 1171–1176, equations (1)–(6).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.MachineLearning.GraphicalModels.BalkePearlBounds

@[expose] public section

namespace WantedExt.Probability.Statistics.BalkePearlBoundsWanted

open Cslib.MachineLearning.GraphicalModels.BalkePearl

/-- **The width is at most the noncompliance rate.** For every
distribution `q` of the sixteen response types (a `TypeLaw`), the Balke–Pearl upper bound (5)
minus the lower bound (4), both computed from the observed law `q.obs`, is at most the
noncompliance rate `P(D = 1 | Z = 0) + P(D = 0 | Z = 1)
= p_{01.0} + p_{11.0} + p_{00.1} + p_{10.1}`, where `p_{yd.z} = q.obs y d z`.

Sources: A. Balke and J. Pearl, "Bounds on treatment effects from studies with imperfect
compliance", J. Amer. Statist. Assoc. 92 (1997) 1171–1176, p. 1173. -/
public theorem_wanted width_le_noncompliance (q : TypeLaw) :
    upperBound q.obs - lowerBound q.obs ≤
      q.obs false true false + q.obs true true false + q.obs false false true +
        q.obs true false true

end WantedExt.Probability.Statistics.BalkePearlBoundsWanted
