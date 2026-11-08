/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH HOMOMORPHISM is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), GRAPH HOMOMORPHISM; P.
Hell and J. Nesetril, "On the complexity of H-coloring" (1990).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphHomomorphism

/-!
# GRAPH HOMOMORPHISM is NP-complete

Two undirected graphs `G` and `H`. The question is whether there is a homomorphism `G → H`: a
map from the vertices of `G` to those of `H` sending every edge of `G` to an edge of `H`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A graph-homomorphism instance: source vertex count, source edges, target vertex count,
target edges. -/
abbrev GraphHomomorphismInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ)


/-- The target graph. -/
def GraphTarget (i : GraphHomomorphismInstance) : SimpleGraph (Fin i.2.2.1) :=
  Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2


/-- Well-formedness of an instance. -/
def WellFormed (i : GraphHomomorphismInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.2.Nodup ∧ ∀ e ∈ i.2.2.2, e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2

/-- A homomorphism from the source to the target. -/
def GraphHomomorphismFeasible
    (i : GraphHomomorphismInstance) : Prop :=
  ∃ f : Fin i.1 → Fin i.2.2.1,
    ∀ e ∈ i.2.1, ∀ (h1 : e.1 < i.1) (h2 : e.2 < i.1),
      (GraphTarget i).Adj (f ⟨e.1, h1⟩) (f ⟨e.2, h2⟩)

open Classical in
/-- GRAPH HOMOMORPHISM as a decision problem over bitstrings. -/
noncomputable def graphHomomorphismDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphHomomorphismInstance) x with
  | some i => decide (WellFormed i ∧ GraphHomomorphismFeasible i)
  | none => false

/-- **GRAPH HOMOMORPHISM is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), GRAPH HOMOMORPHISM; P. Hell and J. Nesetril, "On the
complexity of H-coloring" (1990). -/
public theorem_wanted graphHomomorphism_npComplete :
    graphHomomorphismDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphHomomorphismDec

end MetaMathlibExt.Complexity.NPComplete.GraphHomomorphism
