/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BUS ROUTING (minimization, grid) is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3 (1982),
381-395, doi:10.1016/0196-6774(82)90032-3, comment to problem [1] BUS ROUTING (reference: Rock);
H. Rock, "Bus routing problems on acyclic networks", in J. R. Mühlbacher (ed.), Proc. 7th Conf.
on Graph Theoretic Concepts in Computer Science, C. Hanser Verlag, Vienna (1982), 99-113, as
cited by the column (Rock's paper was not available; the column records the result and its
attribution).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.BusRoutingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BusRoutingMinGrid

/-!
# BUS ROUTING (minimization, grid) is NP-complete

INSTANCE: an acyclic directed graph `G = (V, A)` that is a rectangular grid with all arcs directed
either south or east, `s` the northwest corner and `t` the southeast corner, a non-negative
integer weight `w(a)` for each arc `a` in the transitive closure `A*` of `A`, and a bound `B > 0`.
QUESTION: is there a path `P` in `G` from `s` to `t` such that, if `P*` is the transitive
closure of the arcs in `P`, `∑_{a ∈ P*} w(a) ≤ B`?

Johnson's column, comment to problem [1] BUS ROUTING: "Remains NP-complete even if `G` consists
of a rectangular grid, with `s` the northwest corner, `t` the southeast corner, and all arcs
directed either south or east. [...] If we want to minimize the number of passengers
accommodated we get a quite different problem, but it is still NP-complete for the grid", citing
Rock (1982), which was not available. The instance is BUS ROUTING's, restricted to the grid; the
question asks for total weight at most `B` instead of at least `B`. Membership in NP: the path is
a certificate, as for BUS ROUTING.

The instance, its well-formedness (`BusRouting.WellFormed`: an acyclic digraph, one weight for
each arc of `A*`, `0 < B`), paths (`DirectedTwoDisjointConnectingPaths.IsDirectedPath`) and the
weight `BusRouting.closureWeight` of `P*` are those of `BusRoutingWanted`. The grid has `h ≥ 1`
rows and `w ≥ 1` columns; the vertex in row `r` and column `c` (row `0` north, column `0` west)
is `r * w + c`, so `n = h * w`, `s = 0` and `t = h * w - 1`. The arcs are exactly the eastward
arcs `r * w + c → r * w + c + 1` (`c + 1 < w`) and the southward arcs
`r * w + c → (r + 1) * w + c` (`r + 1 < h`). The weights list one entry per pair of `A*`, so the
input size is at least `|A*|` and the grid is not succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `a` is an arc of the `h × w` grid directed south or east: from the vertex `r * w + c` (row
`r < h`, column `c < w`) to its eastern neighbor `r * w + c + 1` or its southern neighbor
`(r + 1) * w + c`. -/
def IsGridArc (h w : ℕ) (a : ℕ × ℕ) : Prop :=
  ∃ r < h, ∃ c < w, (c + 1 < w ∧ a = (r * w + c, r * w + c + 1)) ∨
    (r + 1 < h ∧ a = (r * w + c, (r + 1) * w + c))

/-- Well-formedness of an instance: a well-formed BUS ROUTING instance (`BusRouting.WellFormed`)
whose digraph is an `h × w` grid (`h, w ≥ 1`, `n = h * w`, the arcs exactly the south and east
grid arcs), with `s` the northwest corner `0` and `t` the southeast corner `h * w - 1`. -/
def WellFormed (i : BusRouting.BusRoutingInstance) : Prop :=
  BusRouting.WellFormed i ∧
    ∃ h w, 0 < h ∧ 0 < w ∧ i.1 = h * w ∧ (∀ a, a ∈ i.2.1 ↔ IsGridArc h w a) ∧
      i.2.2.1 = 0 ∧ i.2.2.2.1 = h * w - 1

/-- Some path `P` from `s` to `t` has `∑_{a ∈ P*} w(a) ≤ B`. -/
def BusRoutingMinGridFeasible (i : BusRouting.BusRoutingInstance) : Prop :=
  ∃ p : List ℕ, DirectedTwoDisjointConnectingPaths.IsDirectedPath i.2.1 i.2.2.1 i.2.2.2.1 p ∧
    BusRouting.closureWeight i.2.2.2.2.1 p ≤ i.2.2.2.2.2

open Classical in
/-- BUS ROUTING (minimization, grid) as a decision problem over bitstrings. -/
noncomputable def busRoutingMinGridDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BusRouting.BusRoutingInstance) x with
  | some i => decide (WellFormed i ∧ BusRoutingMinGridFeasible i)
  | none => false

/-- **BUS ROUTING (minimization, grid) is NP-complete.** Source: Johnson, NP-completeness column
(1982), comment to problem [1]; Rock (1982). -/
public theorem_wanted busRoutingMinGrid_npComplete :
    busRoutingMinGridDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L busRoutingMinGridDec

end MetaMathlibExt.Complexity.NPComplete.BusRoutingMinGrid
