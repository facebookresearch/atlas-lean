/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Extremal numbers for girth at least five

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
the definition `girthFiveExtremalNumber` is taken from leansolving/SqueezeBench
at commit e2e19eef093a77882da57f348def029533ec2d5e,
`SqueezeBench/Problems/ExGirthFive/Def.lean` (`f`; authors P. Manrique,
H. Xia, S. Szeider), and the values from the "Known values" section of
`SqueezeBench/Problems/ExGirthFive/README.md`, distributed under the Apache
License, Version 2.0. SqueezeBench ships no `NOTICE` file. Changes made:
renamed `f` to `girthFiveExtremalNumber`, dropped the `nMin = 1` pin (at
`n = 0` the supremum is already `0`) and the helper lemmas, and turned the
README values, which SqueezeBench marks as reporting only, into Batteries
`theorem_wanted` declarations.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Girth

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.GirthFiveExtremalValuesWanted

open Finset _root_.SimpleGraph

open Classical in
/-- **Girth-five extremal number.** For a natural number $n$, $\mathrm{ex}(n; \{C_3, C_4\})$
is the largest number of edges of a simple graph on $n$ vertices whose girth is at least $5$,
that is, which contains no triangle and no four-cycle (OEIS A006856). An acyclic graph has
infinite girth, so the empty graph always qualifies. -/
noncomputable def girthFiveExtremalNumber (n : ℕ) : ℕ :=
  (univ.filter fun G : SimpleGraph (Fin n) => 5 ≤ G.egirth).sup (fun G => #G.edgeFinset)

/-- **Girth-five extremal numbers up to twenty vertices.** For $n = 1, 2, \dots, 20$ the
girth-five extremal numbers $\mathrm{ex}(n; \{C_3, C_4\})$, the largest numbers of edges of a
simple graph on $n$ vertices that contains no triangle and no four-cycle, are, in order,
$0, 1, 2, 3, 5, 6, 8, 10, 12, 15, 16, 18, 21, 23, 26, 28, 31, 34, 38, 41$.

Source: D. K. Garnick, Y. H. H. Kwong, and F. Lazebnik, *Extremal graphs without
three-cycles or four-cycles*, J. Graph Theory 17 (1993), 633–645 (`n ≤ 24`);
OEIS A006856; listed in leansolving/SqueezeBench
`SqueezeBench/Problems/ExGirthFive/README.md`. -/
public theorem_wanted girthFiveExtremalNumber_one_to_twenty :
    (List.range 20).map (fun i => girthFiveExtremalNumber (i + 1)) =
      [0, 1, 2, 3, 5, 6, 8, 10, 12, 15, 16, 18, 21, 23, 26, 28, 31, 34, 38, 41]

/-- **Girth-five extremal number on fifty vertices.** The girth-five extremal number
$\mathrm{ex}(50; \{C_3, C_4\})$, the largest number of edges of a simple graph on $50$
vertices that contains no triangle and no four-cycle, equals $175$.

For graphs on $n$ vertices of girth at least $5$, the Hoffman–Singleton graph attains the
Moore-type bound $\frac{n}{2} \sqrt{n - 1}$ on the number of edges, with $n = 50$.

Source: A. J. Hoffman and R. R. Singleton, *On Moore graphs with diameters 2
and 3*, IBM J. Res. Develop. 4 (1960), 497–504; OEIS A006856; listed in
SqueezeBench `SqueezeBench/Problems/ExGirthFive/README.md`. -/
public theorem_wanted girthFiveExtremalNumber_fifty : girthFiveExtremalNumber 50 = 175

end MathlibExt.Combinatorics.SimpleGraph.GirthFiveExtremalValuesWanted
