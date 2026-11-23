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
diameter at most `r` (a disconnected graph has infinite diameter `SimpleGraph.ediam`). For
connected triangle-free `G` and `r ≥ 2` a maximal triangle-free supergraph qualifies. -/
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
sketches the construction in the discussion thread): for infinitely many `n` there is a connected
triangle-free graph `G` on `n` vertices with `h₄(G) ≥ n - O(n^{8/9} (log n)^{2/9})`; the disproof is
formalized in Lean in formal-conjectures, and the problem is listed as solved (Lean). Source: T. F.
Bloom, Erdős Problems, Problem #619, https://www.erdosproblems.com/619 (status SOLVED (LEAN));
resolution: Claude Fable 5 (prompted by N. Kuhn), disproof recorded on erdosproblems.com/619 and in
its discussion thread; formal proof in google-deepmind/formal-conjectures,
FormalConjectures/ErdosProblems/619.lean, erdosproblems.com/619: resolved in the negative; for
infinitely many n a connected triangle-free G on n vertices has h₄(G) ≥ n - O(n^{8/9} (log
n)^{2/9}), https://www.erdosproblems.com/forum/thread/619.
-/
public theorem_wanted diameterFourCompletionLinearSaving_refuted :
    ¬ diameterFourCompletionLinearSaving

end MathlibExt.GraphTheory.TriangleFreeDiameterFourCompletionErdosProblem619Wanted
