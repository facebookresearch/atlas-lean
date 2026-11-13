/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# List chromatic number of almost all graphs (Erdős Problem 799)

Erdős Problem 799 (Erdős, Rubin and Taylor): is `χ_L(G) = o(n)` for almost all graphs on `n`
vertices?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import MathlibExt.Combinatorics.SimpleGraph.ListColoring

@[expose] public section

namespace MathlibExt.GraphTheory.RandomGraphListChromaticErdosProblem799Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #799, https://www.erdosproblems.com/799 (status
PROVED). UnsolvedMath record UM-30007038 (`EP-799`), dataset ulamai/UnsolvedMath v1.8.0.

"Almost all graphs" is the uniform proportion over the graphs on `Fin n`. `χ_L(G) ≤ q` is
`MathlibExt`'s `SimpleGraph.IsListColorable G q`, and `χ_L(G) = o(n)` is: for every `ε > 0` the
proportion of graphs with `χ_L(G) ≤ ε n` tends to `1`.
-/

open Classical in
/-- The proportion of the graphs on `Fin n` (the uniform model `G(n, 1/2)`) whose list chromatic
number is at most `ε n`, i.e. that are `q`-list-colorable for some `q ≤ ε n`. -/
noncomputable def smallListChromaticProportion (ε : ℝ) (n : ℕ) : ℝ :=
  ((Finset.univ.filter fun G : SimpleGraph (Fin n) =>
      ∃ q : ℕ, (q : ℝ) ≤ ε * n ∧ G.IsListColorable q).card : ℝ) /
    Fintype.card (SimpleGraph (Fin n))

/-- Erdős Problem 799 (Erdős, Rubin, Taylor): `χ_L(G) = o(n)` for almost all graphs `G` on `n`
vertices: for every `ε > 0` the proportion of graphs with `χ_L(G) ≤ ε n` tends to `1`. -/
def listChromaticNumberSublinearAlmostAll : Prop :=
  ∀ ε : ℝ, 0 < ε → Filter.Tendsto (smallListChromaticProportion ε) Filter.atTop (nhds 1)

/--
Resolved true: Alon proved `χ_L(G) ≪ (log log n / log n) n` almost surely for `G(n, 1/2)`, and Alon,
Krivelevich and Sudakov sharpened this to `χ_L(G) ≍ n / log n`; erdosproblems.com/799 lists the
problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #799,
https://www.erdosproblems.com/799 (status PROVED); resolution: N. Alon, Choice numbers of graphs: a
probabilistic approach, Combin. Probab. Comput. 1 (1992), 107-114, χ_L(G(n, 1/2)) ≪ (log log n / log
n) n almost surely (erdosproblems.com/799), https://doi.org/10.1017/S0963548300000122.
-/
public theorem_wanted listChromaticNumberSublinearAlmostAll_holds :
    listChromaticNumberSublinearAlmostAll

end MathlibExt.GraphTheory.RandomGraphListChromaticErdosProblem799Wanted
