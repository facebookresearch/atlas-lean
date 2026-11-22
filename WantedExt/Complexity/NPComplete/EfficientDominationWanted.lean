/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EFFICIENT DOMINATION (PERFECT CODE) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), EFFICIENT DOMINATION; D.
G. Corneil and Y. Perl, "Clustering and domination in perfect graphs" (1984) and the perfect-
code literature.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EfficientDomination

/-!
# EFFICIENT DOMINATION (PERFECT CODE) is NP-complete

An undirected graph. The question is whether the graph has an efficient dominating set (a
perfect code): a set `S` such that every vertex has exactly one closed neighbor in `S`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count, edge list. -/
abbrev EfficientDominationInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : EfficientDominationInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2


/-- Well-formedness of an instance. -/
def WellFormed (i : EfficientDominationInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- An efficient dominating set. -/
def EfficientDominationFeasible
    (i : EfficientDominationInstance) : Prop :=
  ∃ S : Finset (Fin i.1),
    ∀ v : Fin i.1, ∃! u ∈ S, u = v ∨ (Graph i).Adj u v

open Classical in
/-- EFFICIENT DOMINATION (PERFECT CODE) as a decision problem over bitstrings. -/
noncomputable def efficientDominationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EfficientDominationInstance) x with
  | some i => decide (WellFormed i ∧ EfficientDominationFeasible i)
  | none => false

/-- **EFFICIENT DOMINATION (PERFECT CODE) is NP-complete.** Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), EFFICIENT DOMINATION; D. G. Corneil and Y.
Perl, "Clustering and domination in perfect graphs" (1984) and the perfect-code
literature. -/
public theorem_wanted efficientDomination_npComplete :
    efficientDominationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L efficientDominationDec

end MetaMathlibExt.Complexity.NPComplete.EfficientDomination
