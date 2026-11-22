/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Four-cycle-free subgraphs of the hypercube

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
the values below are taken from the "Known values" section of
leansolving/SqueezeBench at commit e2e19eef093a77882da57f348def029533ec2d5e
(`SqueezeBench/Problems/HypercubeC4/README.md`; authors P. Manrique, H. Xia,
S. Szeider), distributed under the Apache License, Version 2.0. SqueezeBench
ships no `NOTICE` file. Changes made: SqueezeBench's `HypercubeC4.f n`, the
largest edge count of a `C₄`-free spanning subgraph of its own `hypercube n`,
is stated through the repository's `SimpleGraph.hypercubeTuranNumber n
(cycleGraph 4)` over `SimpleGraph.hypercubeGraph n`, which maximizes over all
`C₄`-free subgraphs of `Q_n` (a subgraph and its spanning coercion have the
same edges and the same four-cycles). The values and bounds, which SqueezeBench
reports without stating theorems, become Batteries `theorem_wanted`
declarations; the `Q₈` lower bound is raised from the README's `680` to `682`
(arXiv:2603.29127v5).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import MathlibExt.Combinatorics.SimpleGraph.HypercubeExtremal

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted

open _root_.SimpleGraph

/-!
`hypercubeTuranNumber n (cycleGraph 4)` is `ex(Qₙ, C₄)`, the largest number of
edges in a subgraph of the `n`-cube with no four-cycle (OEIS A245762, offset 1).
-/

/-- `ex(Qₙ, C₄)` for `1 ≤ n ≤ 6`: `1, 3, 9, 24, 56, 132`.

Source: OEIS A245762; `ex(Q₆, C₄) = 132` is H. Harborth and H. Nienborg,
*Maximum number of edges in squarefree subgraphs of the n-cube*, Bull. Inst.
Combin. Appl. 12 (1994), 55–60; listed in leansolving/SqueezeBench
`SqueezeBench/Problems/HypercubeC4/README.md`. -/
public theorem_wanted hypercubeTuranNumber_cycleGraph_four_one_to_six :
    (List.range 6).map (fun i => hypercubeTuranNumber (i + 1) (cycleGraph 4)) =
      [1, 3, 9, 24, 56, 132]

/-- `ex(Q₇, C₄) ≥ 304`, by an explicit construction.

Source: M. Minamoto, *C₄-free subgraphs of the hypercubes Q₆, Q₇, and Q₈*,
arXiv:2603.29127 (2026); listed in SqueezeBench
`SqueezeBench/Problems/HypercubeC4/README.md`. -/
public theorem_wanted le_hypercubeTuranNumber_seven_cycleGraph_four :
    304 ≤ hypercubeTuranNumber 7 (cycleGraph 4)

/-- `ex(Q₇, C₄) ≤ 308`: averaging over the fourteen facets of `Q₇`, each edge
lies in six of them, so `ex(Q₇, C₄) ≤ 14 · ex(Q₆, C₄) / 6 = 308`.

Source: the averaging bound applied to `ex(Q₆, C₄) = 132` (Harborth and
Nienborg 1994), as stated in SqueezeBench
`SqueezeBench/Problems/HypercubeC4/README.md`. -/
public theorem_wanted hypercubeTuranNumber_seven_cycleGraph_four_le :
    hypercubeTuranNumber 7 (cycleGraph 4) ≤ 308

/-- `ex(Q₈, C₄) ≥ 682`, by an explicit construction.

Source: M. Minamoto, *C₄-free subgraphs of the hypercubes Q₆, Q₇, and Q₈*,
arXiv:2603.29127v5 (2026), which improves the bound `680` of its earlier
versions; SqueezeBench `SqueezeBench/Problems/HypercubeC4/README.md` and OEIS
A245762 still list `680`. -/
public theorem_wanted le_hypercubeTuranNumber_eight_cycleGraph_four :
    682 ≤ hypercubeTuranNumber 8 (cycleGraph 4)

end MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted
