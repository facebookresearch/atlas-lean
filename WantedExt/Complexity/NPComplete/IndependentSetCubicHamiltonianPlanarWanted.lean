/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on cubic Hamiltonian planar graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET, the problem
restricted here;
H. Fleischner, G. Sabidussi and V. I. Sarvanov, "Maximum independent sets in 3- and 4-regular
Hamiltonian graphs", Discrete Mathematics 310(20) (2010), 2742-2749,
doi:10.1016/j.disc.2010.05.028.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetCubicHamiltonianPlanar

/-!
# INDEPENDENT SET on cubic Hamiltonian planar graphs is NP-complete

INSTANCE: a cubic Hamiltonian planar graph `G = (V, E)`, and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain an independent set of size `K` or more, that is, a subset `V' ⊆ V`
with `|V'| ≥ K` such that no two vertices of `V'` are joined by an edge in `E`?

This is INDEPENDENT SET ([GT20]) restricted to the ISGCI class `cubic ∩ hamiltonian ∩ planar`
(`gc_1319`). Cubic is Mathlib's `SimpleGraph.IsRegularOfDegree 3`, Hamiltonian is Mathlib's
`SimpleGraph.IsHamiltonian` (a closed walk visiting every vertex exactly once, required unless
the graph has a single vertex), and planar is MathlibExt's `SimpleGraph.IsPlanar` (a
crossing-free straight-line drawing, which by Fáry's theorem exists exactly for the planar
graphs).

Fleischner, Sabidussi and Sarvanov (abstract): "we first show that the independent set problem
for 3-regular Hamiltonian planar graphs is NP-complete"; the graphs their reduction outputs lie
in the class, so it is a reduction to this problem. Membership in NP: the certificate is `V'`
together with a Hamiltonian cycle; cubicity is checked in polynomial time, and planarity in
linear time (Hopcroft and Tarjan, "Efficient planarity testing", Journal of the ACM 21 (1974),
549-568).

The instance, the graph and the question follow
`WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted`: a vertex count `n`
(vertices `Fin n`), an edge list and the bound `K`; the independent set is a `Finset` whose
coercion is Mathlib's `SimpleGraph.IsIndepSet`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev IndependentSetCubicHamiltonianPlanarInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IndependentSetCubicHamiltonianPlanarInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

open Classical in
/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`, the graph
is cubic, Hamiltonian and planar, and `0 < K ≤ |V|`. -/
def WellFormed (i : IndependentSetCubicHamiltonianPlanarInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).IsRegularOfDegree 3 ∧ (Graph i).IsHamiltonian ∧ (Graph i).IsPlanar ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set of at least `K` vertices contains no two adjacent vertices. -/
def IndependentSetCubicHamiltonianPlanarFeasible
    (i : IndependentSetCubicHamiltonianPlanarInstance) : Prop :=
  ∃ s : Finset (Fin i.1), i.2.2 ≤ s.card ∧ (Graph i).IsIndepSet (s : Set (Fin i.1))

open Classical in
/-- INDEPENDENT SET on cubic Hamiltonian planar graphs as a decision problem over bitstrings. -/
noncomputable def independentSetCubicHamiltonianPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IndependentSetCubicHamiltonianPlanarInstance) x with
  | some i => decide (WellFormed i ∧ IndependentSetCubicHamiltonianPlanarFeasible i)
  | none => false

/-- **INDEPENDENT SET on cubic Hamiltonian planar graphs is NP-complete.**
Source: Garey and Johnson (1979), [GT20];
Fleischner, Sabidussi and Sarvanov (2010). -/
public theorem_wanted independentSetCubicHamiltonianPlanar_npComplete :
    independentSetCubicHamiltonianPlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentSetCubicHamiltonianPlanarDec

end MetaMathlibExt.Complexity.NPComplete.IndependentSetCubicHamiltonianPlanar
