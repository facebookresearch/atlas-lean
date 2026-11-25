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
public import MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeEight
public import MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeSevenLower
public import MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeSevenUpper

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted

open _root_.SimpleGraph

/-!
`hypercubeTuranNumber n (cycleGraph 4)` is `ex(Qₙ, C₄)`, the largest number of
edges in a subgraph of the `n`-cube with no four-cycle (OEIS A245762, offset 1).
-/

/-- **Four-cycle-free subgraphs of the hypercubes of dimensions one to six.** For a natural
number $n$, let $Q_n$ be the $n$-dimensional hypercube, let $C_4$ be the cycle on four vertices,
and let $\mathrm{ex}(Q_n, C_4)$ be the largest number of edges of a subgraph of $Q_n$ that
contains no copy of $C_4$. Then for $n = 1, 2, 3, 4, 5, 6$ the value of $\mathrm{ex}(Q_n, C_4)$
is $1$, $3$, $9$, $24$, $56$ and $132$ respectively.

Source: OEIS A245762; `ex(Q₆, C₄) = 132` is H. Harborth and H. Nienborg,
*Maximum number of edges in squarefree subgraphs of the n-cube*, Bull. Inst.
Combin. Appl. 12 (1994), 55–60; listed in leansolving/SqueezeBench
`SqueezeBench/Problems/HypercubeC4/README.md`. -/
public theorem_wanted hypercubeTuranNumber_cycleGraph_four_one_to_six :
    (List.range 6).map (fun i => hypercubeTuranNumber (i + 1) (cycleGraph 4)) =
      [1, 3, 9, 24, 56, 132]

end MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted
