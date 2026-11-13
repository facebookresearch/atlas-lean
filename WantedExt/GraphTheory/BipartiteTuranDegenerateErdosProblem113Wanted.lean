/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bipartite Turán exponent `3/2` and `2`-degeneracy (Erdős Problem 113)

Erdős Problem 113 (Erdős and Simonovits): if `G` is bipartite then `ex(n; G) ≪ n^{3/2}` if and only
if `G` is `2`-degenerate, that is, `G` contains no induced subgraph with minimal degree at least
`3`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
public import MathlibExt.Combinatorics.SimpleGraph.Degeneracy

@[expose] public section

namespace MathlibExt.GraphTheory.BipartiteTuranDegenerateErdosProblem113Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #113, https://www.erdosproblems.com/113 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006727 (`EP-113`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are finite; bipartite is `G.Colorable 2`; `ex(n; G)` is Mathlib's
`SimpleGraph.extremalNumber`; `2`-degenerate is `MathlibExt`'s `SimpleGraph.IsDegenerate G 2`
(every nonempty vertex set contains a vertex with at most two neighbours in it, i.e. no induced
subgraph has minimum degree at least `3`). Compared with the formal-conjectures statement
`ErdosProblems/113.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 113 (Erdős and Simonovits): a finite bipartite graph `G` has
`ex(n; G) = O(n^{3/2})` if and only if it is `2`-degenerate. -/
def bipartiteTuranThreeHalvesIffDegenerate : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Colorable 2 →
    (Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (SimpleGraph.extremalNumber n G : ℝ))
        (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 2)) ↔ G.IsDegenerate 2)

/--
Resolved false: Janzer constructed, for every `ε > 0`, a `3`-regular bipartite graph `H` with `ex(n;
H) ≪ n^{4/3 + ε}`; `H` is not `2`-degenerate, which refutes the "only if" direction.
erdosproblems.com/113 lists the problem as disproved, with a formal proof in plby/lean-proofs
(`Erdos113.lean`). Source: T. F. Bloom, Erdős Problems, Problem #113,
https://www.erdosproblems.com/113 (status DISPROVED (LEAN)); resolution: O. Janzer, Disproof of a
conjecture of Erdős and Simonovits on the Turán number of graphs with minimum degree 3, Int. Math.
Res. Not. IMRN (2023), 8478-8494, for every ε > 0 a 3-regular bipartite H with ex(n; H) ≪ n^{4/3 +
ε} (erdosproblems.com/113),
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos113.lean#L4902.
-/
public theorem_wanted bipartiteTuranThreeHalvesIffDegenerate_refuted :
    ¬ bipartiteTuranThreeHalvesIffDegenerate

end MathlibExt.GraphTheory.BipartiteTuranDegenerateErdosProblem113Wanted
