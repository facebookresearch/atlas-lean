/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Extremal numbers of the four-cycle

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
(`SqueezeBench/Problems/ExC4/README.md`; authors P. Manrique, H. Xia,
S. Szeider), distributed under the Apache License, Version 2.0. SqueezeBench
ships no `NOTICE` file. Changes made: SqueezeBench's `ExC4.f` is Mathlib's
`SimpleGraph.extremalNumber n (cycleGraph 4)` pinned to `0` at `n = 0`; the
statements use the Mathlib function directly, and the values and Füredi's
theorem, which SqueezeBench reports without stating theorems, become Batteries
`theorem_wanted` declarations.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.FourCycleExtremalValuesWanted

open _root_.SimpleGraph

/-!
`extremalNumber n (cycleGraph 4)` is the largest number of edges of a graph on
`Fin n` with no (not necessarily induced) four-cycle (OEIS A006855).
-/

/-- `ex(n; C₄)` for `1 ≤ n ≤ 20`:
`0, 1, 3, 4, 6, 7, 9, 11, 13, 16, 18, 21, 24, 27, 30, 33, 36, 39, 42, 46`.

Source: C. R. J. Clapham, A. Flockhart, and J. Sheehan, *Graphs without
four-cycles*, J. Graph Theory 13 (1989), 29–47 (`n ≤ 21`); OEIS A006855;
listed in leansolving/SqueezeBench `SqueezeBench/Problems/ExC4/README.md`. -/
public theorem_wanted extremalNumber_cycleGraph_four_one_to_twenty :
    (List.range 20).map (fun i => extremalNumber (i + 1) (cycleGraph 4)) =
      [0, 1, 3, 4, 6, 7, 9, 11, 13, 16, 18, 21, 24, 27, 30, 33, 36, 39, 42, 46]

/-- Füredi's theorem: for every prime power `q > 13`,
`ex(q² + q + 1; C₄) = q (q + 1)² / 2`, attained by the polarity graph of the
projective plane of order `q`.

Source: Z. Füredi, *On the number of edges of quadrilateral-free graphs*,
J. Combin. Theory Ser. B 68 (1996), 1–6; listed in SqueezeBench
`SqueezeBench/Problems/ExC4/README.md`. -/
public theorem_wanted extremalNumber_cycleGraph_four_projectivePlane_order
    (q : ℕ) (hq : IsPrimePow q) (h13 : 13 < q) :
    extremalNumber (q ^ 2 + q + 1) (cycleGraph 4) = q * (q + 1) ^ 2 / 2

end MathlibExt.Combinatorics.SimpleGraph.FourCycleExtremalValuesWanted
