/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROMAN DOMINATION is NP-complete

Source:
E. J. Cockayne, P. A. Dreyer Jr., S. M. Hedetniemi, and S. T. Hedetniemi, "Roman domination in
graphs", Discrete Mathematics 278 (2004), 11-22.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RomanDomination

/-!
# ROMAN DOMINATION is NP-complete

An undirected graph and a bound `K`. The question is whether there is a Roman dominating
function: a labeling with values `0, 1, 2` such that every `0`-vertex has a `2`-neighbor, and
the total label weight is at most `K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count, edge list, bound. -/
abbrev RomanDominationInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : RomanDominationInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1


/-- Well-formedness of an instance. -/
def WellFormed (i : RomanDominationInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- A Roman dominating function of total weight at most `K`. -/
def RomanDominationFeasible
    (i : RomanDominationInstance) : Prop :=
  ∃ labeling : Fin i.1 → ℕ, (∀ v, labeling v ≤ 2) ∧
    (∀ v, labeling v = 0 → ∃ u, (Graph i).Adj u v ∧ labeling u = 2) ∧
    (Finset.univ.sum labeling) ≤ i.2.2

open Classical in
/-- ROMAN DOMINATION as a decision problem over bitstrings. -/
noncomputable def romanDominationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RomanDominationInstance) x with
  | some i => decide (WellFormed i ∧ RomanDominationFeasible i)
  | none => false

/-- **ROMAN DOMINATION is NP-complete.** Source: E. J. Cockayne, P. A. Dreyer Jr., S. M.
Hedetniemi, and S. T. Hedetniemi, "Roman domination in graphs", Discrete Mathematics 278
(2004), 11-22. -/
public theorem_wanted romanDomination_npComplete :
    romanDominationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L romanDominationDec

end MetaMathlibExt.Complexity.NPComplete.RomanDomination
