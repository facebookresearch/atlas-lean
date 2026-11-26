/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on partial grid graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET;
B. N. Clark, C. J. Colbourn and D. S. Johnson, "Unit disk graphs", Discrete Mathematics 86
(1990), 165-177, doi:10.1016/0012-365X(90)90358-O (DOMINATING SET on grid graphs);
M. de Berg, H. L. Bodlaender, S. Kisfaludi-Bak, D. Marx and T. C. van der Zanden, "A framework
for exponential-time-hypothesis-tight algorithms and lower bounds in geometric intersection
graphs", SIAM Journal on Computing 49 (2020), 1291-1331, doi:10.1137/20M1320870,
arXiv:1803.10633, Theorem 32 (a reduction from 3-SAT to DOMINATING SET on induced grid graphs);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_440` (partial
grid), problem Domination: NP-complete (on grid graphs, Clark, Colbourn and Johnson 1990).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetPartialGrid

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-!
# DOMINATING SET on partial grid graphs is NP-complete

INSTANCE: a partial grid graph `G = (V, E)`, that is, a graph isomorphic to a (not necessarily
induced) subgraph of a grid, and a positive integer `K ≤ |V|`.
QUESTION: is there a dominating set of size `K` or less for `G`, i.e. a subset `V' ⊆ V` with
`|V'| ≤ K` such that every vertex of `V - V'` is adjacent to a vertex of `V'`?

The instance, its well-formedness and the question are those of
`CSLibExt.Complexity.NPComplete.DominatingSetDefs` ([GT2]: a simple graph on `Fin n` given by
an edge list, and the bound `K`). The restriction adds `0 < K ≤ |V|` ([GT2]'s instance class)
and that the graph is a partial grid: Mathlib's `SimpleGraph.IsContained` (an injective
homomorphism, i.e. a copy as a subgraph that need not be induced) into the infinite grid
`SimpleGraph.hasse ℤ □ SimpleGraph.hasse ℤ` on `ℤ × ℤ`, whose two points are adjacent when they
differ by `1` in one coordinate and agree in the other. The image of a finite graph lies in a
finite grid, so this is the class of subgraphs of grids.

Grid graphs (the subgraphs of the grid induced by a finite set of points) are partial grids;
Clark, Colbourn and Johnson prove DOMINATING SET NP-complete on them, and de Berg et al. give
a polynomial reduction from 3-SAT to it.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed DOMINATING SET instance with `0 < K ≤ |V|`
whose graph is a subgraph of the grid `ℤ × ℤ` (a partial grid). -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧
    (Graph i).IsContained (SimpleGraph.hasse ℤ □ SimpleGraph.hasse ℤ)

open Classical in
/-- DOMINATING SET on partial grid graphs as a decision problem over bitstrings. -/
noncomputable def dominatingSetPartialGridDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

/-- **DOMINATING SET on partial grid graphs is NP-complete.** Source: Clark, Colbourn and
Johnson (1990); de Berg et al. (2020); ISGCI (`gc_440`); Garey and Johnson (1979), [GT2]. -/
public theorem_wanted dominatingSetPartialGrid_npComplete :
    dominatingSetPartialGridDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetPartialGridDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetPartialGrid
