/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Monge–Kantorovich existence theorem

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.OptimalTransport` — monge_kantorovich (manifest `manifests/problems/monge_kantorovich.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.OptimalTransportWanted` namespace. Mathematical
statements are unchanged. Source: L. V. Kantorovich (1942), after G. Monge (1781). Listed as §73 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.OptimalTransportWanted
namespace Analysis

/-!
# Monge–Kantorovich existence theorem

§73 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. Given Polish
probability spaces `(X, P)` and `(Y, Q)` and a continuous cost
`c : X × Y → [0, ∞]`, the Kantorovich functional `I(π) = ∫ c dπ` attains its
infimum on the set of couplings `Π(P, Q)` — the probability measures on `X × Y`
with marginals `P` and `Q` (Kantorovich 1942, after Monge 1781).

mathlib has Polish spaces, marginals (`Measure.fst`, `Measure.snd`), the
weak-convergence topology, Prokhorov's theorem, lower semicontinuity, and the
extreme-value theorem, but no optimal-transport content: no couplings, no
Kantorovich functional, and no existence of an optimal coupling
(`grep -ri "kantorovich\|monge\|wasserstein\|coupling"` in mathlib returns no
algorithmic content). The couplings and the functional are supplied as helper
definitions here.
-/

open MeasureTheory Set

/-- `Couplings P Q`: the probability measures on `X × Y` whose marginals are `P`
on `X` and `Q` on `Y`. -/
def Couplings {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) : Set (Measure (X × Y)) :=
  {π | IsProbabilityMeasure π ∧ π.fst = P ∧ π.snd = Q}

/-- The Kantorovich functional `I(π) = ∫ c dπ` on measures over `X × Y`. -/
noncomputable def kantorovichCost {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (c : X × Y → ENNReal) (π : Measure (X × Y)) : ENNReal :=
  ∫⁻ p, c p ∂π

/- **Monge–Kantorovich existence theorem** (§73). For Polish probability spaces
`(X, P)` and `(Y, Q)` and a continuous cost `c : X × Y → [0, ∞]`, the Kantorovich
functional `I(π) = ∫ c dπ` attains its infimum on the set of couplings `Π(P, Q)`
of `P` and `Q`. -/
/-- Source: L. V. Kantorovich (1942), after G. Monge (1781). Listed as §73 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `monge_kantorovich`. -/
public theorem_wanted monge_kantorovich_exists
    {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (P : Measure X) (Q : Measure Y)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (c : X × Y → ENNReal) (_hc : Continuous c) :
    ∃ π ∈ Couplings P Q,
      ∀ π' ∈ Couplings P Q, kantorovichCost c π ≤ kantorovichCost c π'

end Analysis

end MathlibExt.Analysis.OptimalTransportWanted
