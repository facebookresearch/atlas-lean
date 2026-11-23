/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linear Ramsey numbers of degenerate graphs (Erdős Problem 163)

Erdős Problem 163 (the Burr-Erdős conjecture): for every `d ≥ 1`, if every subgraph of `H` has a
vertex of degree at most `d`, then `R(H) ≪_d n`, where `n` is the number of vertices.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.Degeneracy
public import MathlibExt.Combinatorics.SimpleGraph.Ramsey

@[expose] public section

namespace MathlibExt.GraphTheory.DegenerateGraphRamseyErdosProblem163Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #163, https://www.erdosproblems.com/163 (status
PROVED). UnsolvedMath record UM-30006745 (`EP-163`), dataset ulamai/UnsolvedMath v1.8.0.

Degeneracy is MathlibExt's `SimpleGraph.IsDegenerate`, checked on vertex subsets (induced
subgraphs), which is equivalent. `R(H)` is MathlibExt's `SimpleGraph.diagonalGraphRamsey H`, the
least `N` such that every graph on `N` vertices or its complement contains a copy of `H` (not
necessarily induced; the set is nonempty by Ramsey's theorem). Compared with the formal-conjectures
statement `ErdosProblems/163.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 163 (Burr-Erdős conjecture): for every `d ≥ 1` there is `C` such that every
`d`-degenerate graph `H` on `n` vertices (`SimpleGraph.IsDegenerate`: every nonempty vertex set has
a vertex with at most `d` neighbours in it) has diagonal Ramsey number
`SimpleGraph.diagonalGraphRamsey H ≤ C n`. -/
def degenerateGraphsLinearRamsey : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, ∀ (n : ℕ) (H : SimpleGraph (Fin n)), H.IsDegenerate d →
    (SimpleGraph.diagonalGraphRamsey H : ℝ) ≤ C * n

/--
Resolved true: Lee proved that every `d`-degenerate graph `H` has `R(H) ≤ 2^{2^{O(d)}} |V(H)|` (more
precisely `2^{d 2^{O(χ(H))}} |V(H)|`, and `χ(H) ≤ d + 1`), solving the Burr-Erdős conjecture;
erdosproblems.com/163 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#163, https://www.erdosproblems.com/163 (status PROVED); resolution: C. Lee, Ramsey numbers of
degenerate graphs, Ann. of Math. (2) 185 (2017), 791-829, abstract (arXiv:1505.04773): R(H) ≤ 2^{d
2^{c r}} |V(H)| for d-degenerate H of chromatic number r; erdosproblems.com/163,
https://arxiv.org/abs/1505.04773.
-/
public theorem_wanted degenerateGraphsLinearRamsey_holds : degenerateGraphsLinearRamsey

end MathlibExt.GraphTheory.DegenerateGraphRamseyErdosProblem163Wanted
