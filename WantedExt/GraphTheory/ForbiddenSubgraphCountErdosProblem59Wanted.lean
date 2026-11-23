/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The number of `H`-free graphs (Erdős Problem 59)

Erdős Problem 59: is it true that the number of graphs on `n` vertices which do not contain `G` is
at most `2^{(1 + o(1)) ex(n; G)}`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

@[expose] public section

namespace MathlibExt.GraphTheory.ForbiddenSubgraphCountErdosProblem59Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #59, https://www.erdosproblems.com/59 (status DISPROVED
(LEAN)). UnsolvedMath record UM-30006705 (`EP-59`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are labelled, on the vertex set `Fin n`; containment is `SimpleGraph.IsContained` (`H.Free G`
for its negation) and `ex(n; H)` is Mathlib's `SimpleGraph.extremalNumber`. The `o(1)` is as `n → ∞`
for each fixed finite `H` (on `Fin k`): for every `ε > 0` the bound `2^{(1 + ε) ex(n; H)}` holds for
all large `n`. `H` ranges over graphs that contain a cycle (`¬ H.IsAcyclic`), as in Morris and
Saxton and in the formal-conjectures statement `ErdosProblems/59.lean` (no code imported): for some
forests the bound fails for a trivial reason, since for the path `P₃` with two edges `ex(n; P₃) =
⌊n/2⌋` while the `P₃`-free graphs include all matchings, about `2^{Θ(n log n)}` of them (as
formal-conjectures notes).
-/

open Classical in
/-- The number of graphs on the vertex set `Fin n` that contain no copy of `H`. -/
noncomputable def freeGraphCount {W : Type*} (H : SimpleGraph W) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun G : SimpleGraph (Fin n) => H.Free G).card

/-- Erdős Problem 59: for every finite graph `H` that contains a cycle, the number of `H`-free
graphs on `n` labelled vertices is at most `2 ^ ((1 + o(1)) ex(n; H))`: for every `ε > 0` it is at
most `2 ^ ((1 + ε) ex(n; H))` for all large `n`. -/
def freeGraphCountExtremalExponent : Prop :=
  ∀ (k : ℕ) (H : SimpleGraph (Fin k)), ¬ H.IsAcyclic → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    (freeGraphCount H n : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * SimpleGraph.extremalNumber n H)

/--
Resolved false: Morris and Saxton proved that for some `c > 0` there are at least `2^{(1 + c) ex(n;
C₆)}` graphs on `n` labelled vertices without a `6`-cycle for infinitely many `n`, so the bound
fails for `H = C₆`, a graph with a cycle (it holds for every non-bipartite `H`, by Erdős, Frankl and
Rödl); erdosproblems.com/59 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems,
Problem #59, https://www.erdosproblems.com/59 (status DISPROVED (LEAN)); resolution: R. Morris and
D. Saxton, The number of C_{2ℓ}-free graphs, Adv. Math. (2016), 534-580, erdosproblems.com/59: the
answer is no for G = C₆: there are at least 2^{(1+c) ex(n; C₆)} C₆-free graphs on n vertices for
infinitely many n, for some c > 0 (the answer is yes for non-bipartite G, Erdős-Frankl-Rödl),
https://arxiv.org/abs/1309.2927.
-/
public theorem_wanted freeGraphCountExtremalExponent_refuted : ¬ freeGraphCountExtremalExponent

end MathlibExt.GraphTheory.ForbiddenSubgraphCountErdosProblem59Wanted
