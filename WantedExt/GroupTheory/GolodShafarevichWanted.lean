/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Golod–Shafarevich inequality

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.GroupTheory.GolodShafarevich` — golod_shafarevich_inequality (manifest `manifests/problems/golod_shafarevich_inequality.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.GolodShafarevichWanted` namespace. Mathematical
statements are unchanged. Source: NSW (J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Grundlehren 323, Springer 2008), Theorem 3.9.7; J.-P. Serre, *Galois Cohomology*, Chapter I, Appendix 2, Theorem 1. Lean hypothesis: https://github.com/logical-intelligence/erdos-unit-distance (Hyp_GolodShafarevichInequality).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.GroupTheory.GolodShafarevichWanted
namespace GroupTheory

/-!
# The Golod–Shafarevich inequality

`golod_shafarevich_inequality` is the Golod–Shafarevich inequality for finite
`p`-groups: for a nontrivial finite `p`-group `Q`,

```
d(Q) ^ 2 < 4 r(Q),
```

where `d(Q)` is the generator rank (minimal size of a generating set) and
`r(Q)` is the relation rank (`𝔽_p`-dimension of `H²(Q; 𝔽_p)`).

References: NSW (Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*),
Theorem 3.9.7; Serre, *Galois Cohomology*, Chapter I, Appendix 2, Theorem 1.

This is one of the two external inputs of Logical Intelligence's formalization
of the disproof of Erdős's unit-distance conjecture
(<https://github.com/logical-intelligence/erdos-unit-distance>,
`Hyp_GolodShafarevichInequality`), where it is taken as a hypothesis. It is not
currently available in Mathlib.

The two helper definitions `generatorRank` and `relationRank` below are trusted
(they are not holes); they fix the meaning of `d(Q)` and `r(Q)`. A finite
`p`-group is viewed as a topological group with the discrete topology, so that
topological generation agrees with ordinary generation and continuous
cohomology agrees with ordinary group cohomology. These definitions follow
`ErdosUnitDistance.Defs.ProPGroups`.
-/

open CategoryTheory

/-- The generator rank `d(G)`: the minimal cardinality of a (topological)
generating set of `G`. For a finite discrete group this is the ordinary minimal
number of generators. -/
noncomputable def generatorRank
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : ℕ :=
  sInf {k : ℕ | ∃ S : Finset G, S.card = k ∧
    (Subgroup.closure (S : Set G)).topologicalClosure = ⊤}

/-- The trivial `ZMod p`-representation of `G`, as an object of
`TopRep (ZMod p) G`. -/
noncomputable def trivialZModpRep
    (p : ℕ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    TopRep (ZMod p) G :=
  TopRep.of (ContRepresentation.trivial (ZMod p) G (ZMod p))

/-- The relation rank `r(G) = dim_{𝔽_p} H²(G; 𝔽_p)`, computed via continuous
cohomology in degree `2` with trivial `ZMod p` coefficients. -/
noncomputable def relationRank
    (p : ℕ) [Fact p.Prime] (G : Type)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : ℕ :=
  Module.finrank (ZMod p)
    (continuousCohomology 2 (trivialZModpRep p G))

/- **Golod–Shafarevich inequality.**

For every prime `p` and every nontrivial finite `p`-group `Q`,

```
d(Q) ^ 2 < 4 r(Q),
```

where `d(Q) = generatorRank Q` is the generator rank and
`r(Q) = relationRank p Q` is the relation rank `dim_{𝔽_p} H²(Q; 𝔽_p)`.

A finite `p`-group is presented as a topological group with the discrete
topology (`[DiscreteTopology Q] [Finite Q]`), in which setting both ranks
agree with their abstract group-theoretic counterparts.

References: NSW, Theorem 3.9.7; Serre, Chapter I, Appendix 2, Theorem 1. -/
/-- Source: NSW (J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Grundlehren 323, Springer 2008), Theorem 3.9.7; J.-P. Serre, *Galois Cohomology*, Chapter I, Appendix 2, Theorem 1. Lean hypothesis: https://github.com/logical-intelligence/erdos-unit-distance (Hyp_GolodShafarevichInequality). Via leanprover/lean-eval@38361be, problem `golod_shafarevich_inequality`. -/
public theorem_wanted golod_shafarevich_inequality
    (p : ℕ) [Fact p.Prime] (Q : Type)
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [DiscreteTopology Q] [Finite Q] :
    IsPGroup p Q → Nontrivial Q →
      (generatorRank Q : ℝ) ^ 2 < 4 * (relationRank p Q : ℝ)

end GroupTheory

end MathlibExt.GroupTheory.GolodShafarevichWanted
