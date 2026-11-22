/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Size Ramsey numbers of bounded-degree graphs (Erdős Problem 559)

Erdős Problem 559 (Beck): let `R̂(G)` be the size Ramsey number, the minimal number of edges `m`
such that there is a graph `H` with `m` edges that is Ramsey for `G`. If `G` has `n` vertices and
maximum degree `d`, is `R̂(G) ≪_d n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace MathlibExt.GraphTheory.SizeRamseyBoundedDegreeErdosProblem559Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #559, https://www.erdosproblems.com/559 (status
DISPROVED). UnsolvedMath record UM-30006933 (`EP-559`), dataset ulamai/UnsolvedMath v1.8.0.

`H` is Ramsey for `G` when every red/blue colouring of its edges (red `R ≤ H`, blue `H \ R`) has a
monochromatic copy of `G` (a subgraph, not necessarily induced); hosts are finite graphs on `Fin N`.
`R̂(G) ≪_d n` is `∀ d, ∃ C, R̂(G) ≤ C n` for every graph `G` on `Fin n` of maximum degree at most
`d`. Compared with the formal-conjectures statement `ErdosProblems/559.lean` (equivalent; no code
imported).
-/

/-- `H` is Ramsey for `G`: for every red/blue colouring of the edges of `H` (red edges `R ≤ H`,
blue edges `H \ R`) the graph `G` is a subgraph of the red graph or of the blue graph. -/
def IsRamseyFor {V W : Type*} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∀ R ≤ H, G.IsContained R ∨ G.IsContained (H \ R)

/-- The size Ramsey number `R̂(G)`: the least number of edges of a finite graph that is Ramsey for
`G` (for finite `G` a large complete graph is Ramsey for `G`, so the set is nonempty). -/
noncomputable def sizeRamsey {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {m | ∃ (N : ℕ) (H : SimpleGraph (Fin N)), H.edgeSet.ncard = m ∧ IsRamseyFor H G}

open Classical in
/-- Erdős Problem 559 (Beck): for every `d` there is `C_d` such that every graph `G` on `n`
vertices with maximum degree at most `d` has `R̂(G) ≤ C_d n`. -/
def sizeRamseyLinearBoundedDegree : Prop :=
  ∀ d : ℕ, ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.maxDegree ≤ d →
    (sizeRamsey G : ℝ) ≤ C * n

/--
Resolved false: Rödl and Szemerédi constructed graphs `G` on `n` vertices with maximum degree `3`
and `R̂(G) ≫ n (log n)^c` for an absolute constant `c > 0`, so no linear bound holds for `d = 3`
(Tikhomirov improved the lower bound to `n exp(c √(log n))`); erdosproblems.com/559 lists the
problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem #559,
https://www.erdosproblems.com/559 (status DISPROVED); resolution: V. Rödl and E. Szemerédi, On size
Ramsey numbers of graphs with bounded degree, Combinatorica (2000), 257-262, erdosproblems.com/559:
disproved for d = 3 by graphs on n vertices with maximum degree 3 and R̂(G) ≫ n (log n)^c for an
absolute c > 0; improved to n exp(c √(log n)) by Tikhomirov (arXiv:2210.05818),
https://www.erdosproblems.com/559.
-/
public theorem_wanted sizeRamseyLinearBoundedDegree_refuted : ¬ sizeRamseyLinearBoundedDegree

end MathlibExt.GraphTheory.SizeRamseyBoundedDegreeErdosProblem559Wanted
