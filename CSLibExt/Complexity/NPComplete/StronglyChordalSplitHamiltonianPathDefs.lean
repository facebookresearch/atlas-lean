/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH on strongly chordal split graphs: definitions

Source:
H. Müller, "Hamiltonian circuits in chordal bipartite graphs", Discrete Mathematics 156 (1996),
291-298, doi:10.1016/0012-365X(95)00057-4;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import CSLibExt.Complexity.NPComplete.DominatingSetSplitGraphsDefs
public import CSLibExt.Complexity.NPComplete.HamiltonianPathUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StronglyChordalSplitHamiltonianPath

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected

/-- The closed walk `c` (a cycle of length `ℓ`) has an odd chord: positions `i < j < ℓ` with
`j - i` odd, `3 ≤ j - i` and `j - i + 3 ≤ ℓ`, whose vertices are adjacent. -/
def HasOddChord {V : Type*} {G : SimpleGraph V} {v : V} (c : G.Walk v v) : Prop :=
  ∃ i j : ℕ, i < j ∧ j < c.length ∧ Odd (j - i) ∧ 3 ≤ j - i ∧ j - i + 3 ≤ c.length ∧
    G.Adj (c.getVert i) (c.getVert j)

/-- `G` is strongly chordal: it has no induced cycle of length at least `4` (chordal), and every
cycle of even length at least `6` has an odd chord. -/
def IsStronglyChordal {V : Type*} (G : SimpleGraph V) : Prop :=
  (∀ k, 4 ≤ k → ¬ (SimpleGraph.cycleGraph k).IsIndContained G) ∧
    ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length → 6 ≤ c.length → HasOddChord c

/-- Well-formedness of an instance: a well-formed HAMILTONIAN PATH instance whose graph is a
split graph and strongly chordal. -/
def WellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  HamiltonianPathUndirected.WellFormed i ∧ DominatingSetSplitGraphs.IsSplitGraph (Graph i) ∧
    IsStronglyChordal (Graph i)

open Classical in
/-- HAMILTONIAN PATH on strongly chordal split graphs as a decision problem over bitstrings. -/
noncomputable def stronglyChordalSplitHamiltonianPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.StronglyChordalSplitHamiltonianPath
