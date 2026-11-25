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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.OptimalTransport` —
monge_kantorovich (manifest `manifests/problems/monge_kantorovich.toml`, rev 1,
submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.OptimalTransportWanted` namespace.
Mathematical statements are unchanged. Later change (ATLAS, 2026): the `theorem_wanted` was
proved and the module moved from `WantedExt/Analysis/OptimalTransportWanted.lean` to this
MathlibExt module, keeping the declaration names; the statement is unchanged,
`public import Mathlib` was replaced by narrow imports, and a bridge lemma `mem_couplings_iff`
was added. Source: L. V. Kantorovich (1942), after G. Monge (1781). Listed as §73 in O. Knill,
Some Fundamental Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import MathlibExt.MeasureTheory.OptimalTransport.Existence
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Monge–Kantorovich existence theorem

§73 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. Given Polish
probability spaces `(X, P)` and `(Y, Q)` and a continuous cost
`c : X × Y → [0, ∞]`, the Kantorovich functional `I(π) = ∫ c dπ` attains its
infimum on the set of couplings `Π(P, Q)` — the probability measures on `X × Y`
with marginals `P` and `Q` (Kantorovich 1942, after Monge 1781).

Formerly a `theorem_wanted` of `WantedExt`; it is now proved from
`MathlibExt.MeasureTheory.OptimalTransport.Existence.exists_isCoupling_forall_lintegral_le`
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, Theorem 4.1), through the bridge
`mem_couplings_iff` between `Couplings` and `IsCoupling`. The declarations keep their original
names, so the namespace still reads `OptimalTransportWanted`.
-/

@[expose] public section

open MeasureTheory Set

open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (IsCoupling)

namespace MathlibExt.Analysis.OptimalTransportWanted
namespace Analysis

set_option linter.dupNamespace false in
/-- `Couplings P Q`: the probability measures on `X × Y` whose marginals are `P`
on `X` and `Q` on `Y`. -/
def Couplings {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) : Set (Measure (X × Y)) :=
  {π | IsProbabilityMeasure π ∧ π.fst = P ∧ π.snd = Q}

set_option linter.dupNamespace false in
/-- The Kantorovich functional `I(π) = ∫ c dπ` on measures over `X × Y`. -/
noncomputable def kantorovichCost {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (c : X × Y → ENNReal) (π : Measure (X × Y)) : ENNReal :=
  ∫⁻ p, c p ∂π

set_option linter.dupNamespace false in
/-- **Couplings as sets and as predicates.** For probability measures `μ` on `X` and `ν` on
`Y` and a probability measure `π` on `X × Y`, `π` lies in `Couplings μ ν` exactly when it is a
coupling in the sense of
`MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted.IsCoupling`: both say that the
marginals of `π` are `μ` and `ν` (C. Villani, *Optimal Transport: Old and New*, Springer 2009,
Chapter 1, couplings). -/
theorem mem_couplings_iff {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) (π : ProbabilityMeasure (X × Y)) :
    (π : Measure (X × Y)) ∈ Couplings (μ : Measure X) (ν : Measure Y) ↔ IsCoupling μ ν π := by
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨inferInstance, h1.symm, h2.symm⟩

set_option linter.dupNamespace false in
/-- **Monge–Kantorovich existence theorem** (§73). For Polish probability spaces
`(X, P)` and `(Y, Q)` and a continuous cost `c : X × Y → [0, ∞]`, the Kantorovich
functional `I(π) = ∫ c dπ` attains its infimum on the set of couplings `Π(P, Q)`
of `P` and `Q`. Source: L. V. Kantorovich (1942), after G. Monge (1781). Listed as §73 in
O. Knill, Some Fundamental Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `monge_kantorovich`. Proved here from the existence of an
optimal coupling, C. Villani, *Optimal Transport: Old and New*, Springer 2009, Theorem 4.1. -/
theorem monge_kantorovich_exists
    {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (P : Measure X) (Q : Measure Y)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (c : X × Y → ENNReal) (_hc : Continuous c) :
    ∃ π ∈ Couplings P Q,
      ∀ π' ∈ Couplings P Q, kantorovichCost c π ≤ kantorovichCost c π' := by
  let μ : ProbabilityMeasure X := ⟨P, inferInstance⟩
  let ν : ProbabilityMeasure Y := ⟨Q, inferInstance⟩
  obtain ⟨π, hπ, hmin⟩ :=
    MathlibExt.MeasureTheory.OptimalTransport.Existence.exists_isCoupling_forall_lintegral_le
      μ ν _hc
  refine ⟨π, (mem_couplings_iff μ ν π).2 hπ, fun π' hπ' => ?_⟩
  have : IsProbabilityMeasure π' := hπ'.1
  exact hmin ⟨π', this⟩ ((mem_couplings_iff μ ν ⟨π', this⟩).1 hπ')

end Analysis

end MathlibExt.Analysis.OptimalTransportWanted
