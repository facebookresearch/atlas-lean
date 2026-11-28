/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on K_1,4-free graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 195, problem [GT20] INDEPENDENT SET,
comment: "Remains NP-complete for cubic planar graphs [Garey, Johnson, and Stockmeyer, 1976],
[Garey and Johnson, 1977a], [Maier and Storer, 1977]";
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1(3) (1976), 237-267, doi:10.1016/0304-3975(76)90059-1;
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_388` (K_1,4-free),
problem Independent set: NP-complete (with the subclasses "cubic ∩ hamiltonian ∩ planar" and
"2-connected ∩ cubic ∩ planar" also recorded as NP-complete).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import CSLibExt.Complexity.NPComplete.TriangleFreeIndependentSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetK14Free

open TriangleFreeIndependentSet (TriangleFreeIndependentSetInstance Graph
  TriangleFreeIndependentSetFeasible)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range) with no induced
`K_1,4`, and `0 < K ≤ |V|`. -/
def WellFormed (i : TriangleFreeIndependentSetInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    ¬ (completeBipartiteGraph (Fin 1) (Fin 4)).IsIndContained (Graph i) ∧
      0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- INDEPENDENT SET on `K_1,4`-free graphs as a decision problem over bitstrings. -/
noncomputable def independentSetK14FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TriangleFreeIndependentSetInstance) x with
  | some i => decide (WellFormed i ∧ TriangleFreeIndependentSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IndependentSetK14Free
