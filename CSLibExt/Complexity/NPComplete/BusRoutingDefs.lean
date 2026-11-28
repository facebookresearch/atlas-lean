/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BUS ROUTING: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide" (fifth edition), Journal of
Algorithms 3 (1982), 381-395, doi:10.1016/0196-6774(82)90032-3, problem [1] BUS ROUTING
(reference: Rock; transformation from HAMILTONIAN PATH);
H. Rock, "Bus routing problems on acyclic networks", in J. R. Mühlbacher (ed.), Proc. 7th Conf.
on Graph Theoretic Concepts in Computer Science, C. Hanser Verlag, Vienna (1982), 99-113, as
cited by the column (Rock's paper was not available; the column records the result and its
attribution).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation
public import CSLibExt.Complexity.NPComplete.DirectedTwoDisjointConnectingPathsDefs
public import CSLibExt.Complexity.NPComplete.PathWithForbiddenPairsDefs
public import CSLibExt.Complexity.NPComplete.RoutingWithMustPairsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BusRouting

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), arc list `A`, `s`, `t`, the
weights as a list of entries `((u, v), w(u, v))`, and the bound `B`. -/
abbrev BusRoutingInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ × List ((ℕ × ℕ) × ℕ) × ℕ

/-- The ROUTING WITH MUST PAIRS instance with the same vertex count, arcs, `s` and `t`, whose
pairs are the weighted pairs. -/
def toMustPairs (i : BusRoutingInstance) :
    PathWithForbiddenPairs.PathWithForbiddenPairsInstance :=
  (i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2.1.map Prod.fst)

/-- Well-formedness of an instance: `RoutingWithMustPairs.WellFormed` of `toMustPairs i` (arcs,
`s`, `t` and weighted pairs use vertices below `n`, the digraph is acyclic, every weighted pair
is in `A*`), the weighted pairs are distinct, every pair of `A*` is weighted, and `0 < B`. -/
def WellFormed (i : BusRoutingInstance) : Prop :=
  RoutingWithMustPairs.WellFormed (toMustPairs i) ∧ (i.2.2.2.2.1.map Prod.fst).Nodup ∧
    (∀ u v, Relation.TransGen (fun a b => (a, b) ∈ i.2.1) u v →
      (u, v) ∈ i.2.2.2.2.1.map Prod.fst) ∧
    0 < i.2.2.2.2.2

/-- `(u, v)` is in the transitive closure `P*` of the arcs of the path `p`: `v` is reached from
`u` by passing to the next vertex of `p` one or more times. -/
def InPathClosure (p : List ℕ) (u v : ℕ) : Prop :=
  Relation.TransGen (fun a b => [a, b] <:+: p) u v

open Classical in
/-- The total weight `∑_{a ∈ P*} w(a)` of the weighted pairs in the transitive closure of the
arcs of `p`. -/
noncomputable def closureWeight (W : List ((ℕ × ℕ) × ℕ)) (p : List ℕ) : ℕ :=
  ((W.filter fun e => decide (InPathClosure p e.1.1 e.1.2)).map Prod.snd).sum

/-- Some path `P` from `s` to `t` has `∑_{a ∈ P*} w(a) ≥ B`. -/
def BusRoutingFeasible (i : BusRoutingInstance) : Prop :=
  ∃ p : List ℕ, DirectedTwoDisjointConnectingPaths.IsDirectedPath i.2.1 i.2.2.1 i.2.2.2.1 p ∧
    i.2.2.2.2.2 ≤ closureWeight i.2.2.2.2.1 p

open Classical in
/-- BUS ROUTING as a decision problem over bitstrings. -/
noncomputable def busRoutingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BusRoutingInstance) x with
  | some i => decide (WellFormed i ∧ BusRoutingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BusRouting
