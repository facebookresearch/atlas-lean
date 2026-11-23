/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOTAL COLORING OF REGULAR BIPARTITE GRAPHS is NP-complete for every fixed k ≥ 3

Source:
C. J. H. McDiarmid and A. Sánchez-Arroyo, "Total colouring regular bipartite graphs is
NP-hard", Discrete Mathematics 124 (1994), 155-162, doi:10.1016/0012-365X(92)00058-Y;
A. Sánchez-Arroyo, "Determining the total colouring number is NP-hard", Discrete Mathematics
78 (1989), 315-319, doi:10.1016/0012-365X(89)90187-8.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.TotalColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalColoringRegularBipartite

open MetaMathlibExt.Complexity.NPComplete.TotalColoring (TotalColoringInstance Graph)

/-!
# TOTAL COLORING OF REGULAR BIPARTITE GRAPHS is NP-complete for every fixed k ≥ 3

Fix an integer `k ≥ 3`.
INSTANCE: a finite simple undirected graph `G = (V, E)` with `V` nonempty that is `k`-regular
and bipartite.
QUESTION: is `G` totally `(k + 1)`-colorable, that is, is there a map `V ∪ E → {1, …, k + 1}`
that gives distinct colors to adjacent vertices, to edges sharing an endpoint, and to each edge
and each of its endpoints?

Every graph of maximum degree `k` needs at least `k + 1` colors in a total coloring, so the
question asks whether `G` has the least possible total chromatic number (is of Type 1).
McDiarmid and Sánchez-Arroyo prove that this is NP-complete for every fixed `k ≥ 3`; for
`k = 3` (cubic bipartite graphs) the result is Sánchez-Arroyo's.

This is TOTAL COLORING (`TotalColoringWanted`) restricted to these instances: the instance,
the graph and the question are `TotalColoringWanted`'s, reused unchanged (vertex count, edge
list on `Fin n` and number of colors, with `TotalColoring.WellFormed`, `TotalColoring.Graph`
and `TotalColoring.TotalColoringFeasible`). The restriction adds to well-formedness that the
number of colors is `k + 1`, that the graph has a vertex (Mathlib counts the empty graph as
`k`-regular for every `k`), that it is `k`-regular (Mathlib's
`SimpleGraph.IsRegularOfDegree k`) and that it is bipartite (Mathlib's
`SimpleGraph.IsBipartite`, a proper 2-coloring).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- Well-formedness of an instance for the fixed degree `k`: a well-formed TOTAL COLORING
instance whose number of colors is `k + 1` and whose graph is nonempty, `k`-regular and
bipartite. -/
def WellFormed (k : ℕ) (i : TotalColoringInstance) : Prop :=
  TotalColoring.WellFormed i ∧ i.2.2 = k + 1 ∧ 0 < i.1 ∧ (Graph i).IsRegularOfDegree k ∧
    (Graph i).IsBipartite

open Classical in
/-- TOTAL COLORING OF `k`-REGULAR BIPARTITE GRAPHS with `k + 1` colors, for the fixed degree
`k`, as a decision problem over bitstrings. -/
noncomputable def totalColoringRegularBipartiteDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := TotalColoringInstance) x with
  | some i => decide (WellFormed k i ∧ TotalColoring.TotalColoringFeasible i)
  | none => false

/-- **TOTAL COLORING OF REGULAR BIPARTITE GRAPHS is NP-complete for every fixed `k ≥ 3`.**
Source: McDiarmid and Sánchez-Arroyo (1994); Sánchez-Arroyo (1989). -/
public theorem_wanted totalColoringRegularBipartite_npComplete (k : ℕ) (hk : 3 ≤ k) :
    totalColoringRegularBipartiteDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (totalColoringRegularBipartiteDec k)

end MetaMathlibExt.Complexity.NPComplete.TotalColoringRegularBipartite
