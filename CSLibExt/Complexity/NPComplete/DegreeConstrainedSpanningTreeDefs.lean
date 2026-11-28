/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEGREE-CONSTRAINED SPANNING TREE: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), DEGREE-CONSTRAINED
SPANNING TREE (the `K = 2` slice is Hamiltonian path).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DegreeConstrainedSpanningTree

/-- **Instances of DEGREE-CONSTRAINED SPANNING TREE.** An instance of DEGREE-CONSTRAINED SPANNING
TREE is a triple $(n, E, K)$ consisting of a natural number $n$ (the number of vertices), a list
$E$ of pairs of natural numbers (the edges) and a natural number $K$ (the degree bound). -/
abbrev DegreeConstrainedSpanningTreeInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Well-formed DEGREE-CONSTRAINED SPANNING TREE instances.** An instance $(n, E, K)$ of
DEGREE-CONSTRAINED SPANNING TREE is well formed when $n > 0$, the list $E$ has no repeated
entries, and every pair $(u, v)$ in $E$ satisfies $u < n$, $v < n$ and $u \ne v$, with the
reversed pair $(v, u)$ not in $E$. -/
def WellFormed (i : DegreeConstrainedSpanningTreeInstance) : Prop :=
  0 < i.1 ∧ i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasibility for DEGREE-CONSTRAINED SPANNING TREE.** An instance $(n, E, K)$ of
DEGREE-CONSTRAINED SPANNING TREE is feasible when there is a list $T$ of pairs of natural numbers
such that $T$ is a sublist of $E$ (obtained by deleting entries and keeping the order), $T$ has no
repeated entries, $T$ has exactly $n - 1$ entries, the graph of $T$ on $n$ vertices is connected,
and for every vertex $v < n$ there is no sublist of $T$ with $K + 1$ entries each of which has $v$
as one of its two components.

For a well-formed instance this says that the graph of $E$ on $n$ vertices has a spanning tree in
which every vertex has degree at most $K$. -/
def DegreeConstrainedSpanningTreeFeasible
    (i : DegreeConstrainedSpanningTreeInstance) : Prop :=
  ∃ T : List (ℕ × ℕ), T.Sublist i.2.1 ∧ T.Nodup ∧ T.length = i.1 - 1 ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 T).Connected ∧
    ∀ v < i.1, ¬ ∃ D : List (ℕ × ℕ), D.Sublist T ∧ D.length = i.2.2 + 1 ∧
      ∀ e ∈ D, e.1 = v ∨ e.2 = v

open Classical in
/-- **DEGREE-CONSTRAINED SPANNING TREE as a decision problem.** The decision problem
DEGREE-CONSTRAINED SPANNING TREE accepts a bitstring $x$ exactly when bitstring decoding of $x$ as
a triple $(n, E, K)$ succeeds and returns an instance of DEGREE-CONSTRAINED SPANNING TREE that is
both well formed and feasible; every bitstring that does not decode is rejected. -/
noncomputable def degreeConstrainedSpanningTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DegreeConstrainedSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ DegreeConstrainedSpanningTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DegreeConstrainedSpanningTree
