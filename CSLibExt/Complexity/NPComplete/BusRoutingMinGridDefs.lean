/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BUS ROUTING (minimization, grid): definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3 (1982),
381-395, doi:10.1016/0196-6774(82)90032-3, comment to problem [1] BUS ROUTING (reference: Rock);
H. Rock, "Bus routing problems on acyclic networks", in J. R. Mühlbacher (ed.), Proc. 7th Conf.
on Graph Theoretic Concepts in Computer Science, C. Hanser Verlag, Vienna (1982), 99-113, as
cited by the column (Rock's paper was not available; the column records the result and its
attribution).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BusRoutingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BusRoutingMinGrid

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

end MetaMathlibExt.Complexity.NPComplete.BusRoutingMinGrid
