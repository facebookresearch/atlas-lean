/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Completing connected triangle-free graphs to diameter four (Erdős Problem 619)

Erdős Problem 619 (Erdős, Gyárfás and Ruszinkó): for a triangle-free graph `G` let `h_r(G)` be the
smallest number of edges that need to be added to `G` so that it has diameter `r` (while preserving
the property of being triangle-free). Is it true that there exists a constant `c > 0` such that if
`G` is a connected graph on `n` vertices then `h₄(G) < (1 - c) n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Diam

@[expose] public section

namespace MathlibExt.GraphTheory.TriangleFreeDiameterFourCompletionErdosProblem619Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #619, https://www.erdosproblems.com/619 (status SOLVED
(LEAN)). UnsolvedMath record UM-00002215 (`EP-619`), dataset ulamai/UnsolvedMath v1.8.0.

Diameter `r` is read as diameter at most `r` (`SimpleGraph.ediam ≤ r`; a disconnected graph has
infinite diameter); graphs are on `Fin n`, and the hypothesis that `G` is triangle-free, implicit in
the definition of `h_r`, is explicit. Compared with the formal-conjectures statement
`ErdosProblems/619.lean` (equivalent; no code imported).
-/

/-- `h_r(G)`: the least number of edges whose addition to `G` gives a triangle-free graph of
diameter at most `r` (a disconnected graph has infinite diameter `SimpleGraph.ediam`, and the graph
on the empty vertex type, `n = 0`, has extended diameter `0`). For connected triangle-free `G` and
`r ≥ 2` a maximal triangle-free supergraph qualifies. -/
noncomputable def diameterCompletionCost {n : ℕ} (r : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k | ∃ H : SimpleGraph (Fin n), G ≤ H ∧ H.CliqueFree 3 ∧ H.ediam ≤ r ∧
    (H \ G).edgeSet.ncard = k}

/-- Erdős Problem 619 (Erdős, Gyárfás and Ruszinkó): there is `c > 0` such that every connected
triangle-free graph `G` on `n` vertices has `h₄(G) < (1 - c) n`. -/
def diameterFourCompletionLinearSaving : Prop :=
  ∃ c > (0 : ℝ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.Connected → G.CliqueFree 3 →
    (diameterCompletionCost 4 G : ℝ) < (1 - c) * n

/--
Resolved false: erdosproblems.com/619 records a disproof by Claude Fable 5 (prompted by Kuhn, who
sketches the construction in the discussion thread). No refereed proof is published: the disproof
is recorded only on erdosproblems.com/619 and in its discussion thread. The construction gives,
for every `η > 0`, a connected triangle-free graph `G` on `n` vertices with `h₄(G) > (1 - η) n`;
optimising its parameters, as T. F. Bloom does in the thread, gives
`h₄(G) ≥ n - O(n^{8/9} (log n)^{2/9})` for infinitely many `n`. The disproof is formalized in
Lean and the problem is listed as solved (Lean); on the main branch of formal-conjectures,
`FormalConjectures/ErdosProblems/619.lean` states `erdos_619` without its proof and links the two
formal proofs named below. Source: T. F. Bloom, Erdős Problems, Problem #619,
https://www.erdosproblems.com/619 (status SOLVED (LEAN)); resolution: the disproof recorded on
erdosproblems.com/619 and in its discussion thread, https://www.erdosproblems.com/forum/thread/619;
formal proofs: nick-kuhn/erdos-619 at commit 7f65718b8c1019ecc24e6c9a6b04ec4c66a4e26f,
Solution.lean, line 5869 (`erdos_619_fc_solution`), and google-deepmind/formal-conjectures at
commit b8c7a76f267c29eaa41d1212c211a920be8b05ea, FormalConjectures/ErdosProblems/619.lean, line
6009 (`erdos_619`).
-/
public theorem_wanted diameterFourCompletionLinearSaving_refuted :
    ¬ diameterFourCompletionLinearSaving

end MathlibExt.GraphTheory.TriangleFreeDiameterFourCompletionErdosProblem619Wanted
