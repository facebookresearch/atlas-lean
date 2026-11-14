/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR 3SAT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO1] SATISFIABILITY, comment
(PLANAR 3SAT, attributed to Lichtenstein, 1977);
D. Lichtenstein, "Planar formulae and their uses", SIAM Journal on Computing 11(2) (1982),
329-343, doi:10.1137/0211025.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Logics.Propositional.CNF.Semantics
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarThreeSat

/-!
# PLANAR 3SAT is NP-complete

INSTANCE: a set `U` of variables and a collection `C` of clauses over `U` such that each
`c ∈ C` has `|c| ≤ 3` and the bipartite graph `G = (V, E)`, where `V = U ∪ C` and `E` contains
exactly those pairs `{u, c}` such that either `u` or `ū` belongs to the clause `c`, is planar.
QUESTION: is there a satisfying truth assignment for `C`?

This is SATISFIABILITY restricted as in Garey and Johnson's comment to [LO1] (Lichtenstein
1977; published as Lichtenstein 1982). The formula uses the repository's CNF representation
(`Cslib.Logic.PL.CNF`): a list of clauses, each a list of literals `(variable, polarity)`, with
variables `0, …, n - 1`; `|c| ≤ 3` is `c.length ≤ 3`, as in the repository's 3SAT
(`Cslib.Complexity.Karp.is3`). The graph `G` has one vertex `Sum.inl u` for each variable
`u` and one vertex `Sum.inr c` for each clause `c` of the list, and `Sum.inl u` is adjacent to
`Sum.inr c` exactly when some literal of `c` has variable `u`. Planarity is the shared
MathlibExt predicate `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing; by Fáry's
theorem this is planarity for finite simple graphs).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of variables (variables `0, …, n - 1`) and the CNF formula, a
list of clauses, each a list of literals `(variable, polarity)`. -/
abbrev PlanarThreeSatInstance := ℕ × Cslib.Logic.PL.CNF

/-- The variable-clause incidence graph `G` of the instance: its vertices are the variables
`Sum.inl u` and the clauses `Sum.inr c`, and `{u, c}` is an edge exactly when `u` or `ū`
belongs to the clause `c`. -/
def IncidenceGraph (i : PlanarThreeSatInstance) : SimpleGraph (Fin i.1 ⊕ Fin i.2.length) :=
  SimpleGraph.fromRel fun a b =>
    ∃ (u : Fin i.1) (c : Fin i.2.length), a = Sum.inl u ∧ b = Sum.inr c ∧
      ∃ l ∈ i.2[c], l.1 = (u : ℕ)

/-- Well-formedness of an instance: every clause has at most three literals, all over the
variables `0, …, n - 1`, and the incidence graph is planar. -/
def WellFormed (i : PlanarThreeSatInstance) : Prop :=
  (∀ clause ∈ i.2, clause.length ≤ 3 ∧ ∀ l ∈ clause, l.1 < i.1) ∧
    (IncidenceGraph i).IsPlanar

/-- Some truth assignment to the `n` variables satisfies every clause. -/
def PlanarThreeSatFeasible (i : PlanarThreeSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    Cslib.Logic.PL.CNF.Satisfies (fun x => assign.getD x false) i.2

open Classical in
/-- PLANAR 3SAT as a decision problem over bitstrings. -/
noncomputable def planarThreeSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PlanarThreeSatInstance) x with
  | some i => decide (WellFormed i ∧ PlanarThreeSatFeasible i)
  | none => false

/-- **PLANAR 3SAT is NP-complete.** Source: Garey and Johnson (1979), [LO1], comment;
Lichtenstein (1982). -/
public theorem_wanted planarThreeSat_npComplete :
    planarThreeSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarThreeSatDec

end MetaMathlibExt.Complexity.NPComplete.PlanarThreeSat
