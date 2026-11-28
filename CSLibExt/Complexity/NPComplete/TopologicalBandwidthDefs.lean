/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOPOLOGICAL BANDWIDTH: definitions

Source:
F. S. Makedon, C. H. Papadimitriou and I. H. Sudborough, "Topological bandwidth", SIAM Journal
on Algebraic and Discrete Methods 6 (1985), 418-444, doi:10.1137/0606044 (conference version:
CAAP '83, Lecture Notes in Computer Science (1983), 317-331, doi:10.1007/3-540-12727-5_19);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT40] BANDWIDTH (the underlying measure).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BandwidthDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TopologicalBandwidth

open MetaMathlibExt.Complexity.NPComplete.Bandwidth (BandwidthInstance)

/-- The edges of the subdivided graph: starting with fresh vertex `next`, the edge `(a, b)` with
subdivision count `m` becomes the path `a, next, …, next + m - 1, b` (its consecutive pairs);
the remaining edges continue with fresh vertex `next + m`. -/
def subdivideEdges : ℕ → List (ℕ × ℕ) → List ℕ → List (ℕ × ℕ)
  | next, e :: es, m :: ms =>
      List.zip (e.1 :: List.range' next m) (List.range' next m ++ [e.2]) ++
        subdivideEdges (next + m) es ms
  | _, _, _ => []

/-- The graph obtained by subdividing the `k`-th edge with `s[k]` new degree-two vertices,
as a BANDWIDTH instance with the same bound `K`: `n + Σ s` vertices, the fresh vertices
numbered from `n` on. -/
def subdivide (i : BandwidthInstance) (s : List ℕ) : BandwidthInstance :=
  (i.1 + s.sum, subdivideEdges i.1 i.2.1 s, i.2.2)

/-- Well-formedness of an instance: a well-formed BANDWIDTH instance (a simple graph given by
an edge list on `Fin n`) with `0 < K`. -/
def WellFormed (i : BandwidthInstance) : Prop :=
  Bandwidth.WellFormed i ∧ 0 < i.2.2

/-- Some subdivision of the graph (one count per edge) has bandwidth at most `K`. -/
def TopologicalBandwidthFeasible (i : BandwidthInstance) : Prop :=
  ∃ s : List ℕ, s.length = i.2.1.length ∧ Bandwidth.BandwidthFeasible (subdivide i s)

open Classical in
/-- TOPOLOGICAL BANDWIDTH as a decision problem over bitstrings. -/
noncomputable def topologicalBandwidthDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := BandwidthInstance) x with
  | some i => decide (WellFormed i ∧ TopologicalBandwidthFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TopologicalBandwidth
