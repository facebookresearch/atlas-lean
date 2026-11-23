/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THRESHOLD EDITING is NP-complete

Source:
P. G. Drange, M. S. Dregi, D. Lokshtanov and B. D. Sullivan, "On the threshold of
intractability", Journal of Computer and System Sciences 124 (2022), 1-25,
doi:10.1016/j.jcss.2021.09.003 (conference version: ESA 2015, LNCS 9294, 411-423).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import WantedExt.Complexity.NPComplete.ThresholdNumberWanted
public import Mathlib.Data.Set.Card
public import Mathlib.Order.SymmDiff

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThresholdEditing

/-!
# THRESHOLD EDITING is NP-complete

INSTANCE: a graph `G = (V, E)` and a nonnegative integer `K`. QUESTION: can `G` be transformed
into a threshold graph by adding and deleting at most `K` edges?

The edited graph is a graph `H` on the same vertex set `V`; the edits are the edges in exactly
one of `G` and `H`, the symmetric difference of the edge sets, so the question is whether some
threshold graph `H` on `V` has `|E(G) ∆ E(H)| ≤ K`. "Threshold graph" is the Chvátal-Hammer
definition shared with `WantedExt.Complexity.NPComplete.ThresholdNumberWanted`
(`ThresholdNumber.IsThresholdGraph`: real weights `a` and a bound `b` such that a vertex set is a
clique exactly when its weight is at most `b`).

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
abbrev ThresholdEditingInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : ThresholdEditingInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). Every `K` is
allowed. -/
def WellFormed (i : ThresholdEditingInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- Some threshold graph `H` on the same vertices differs from `G` in at most `K` edges (added
or deleted). -/
def ThresholdEditingFeasible (i : ThresholdEditingInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), ThresholdNumber.IsThresholdGraph H ∧
    (symmDiff (Graph i).edgeSet H.edgeSet).ncard ≤ i.2.2

open Classical in
/-- THRESHOLD EDITING as a decision problem over bitstrings. -/
noncomputable def thresholdEditingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThresholdEditingInstance) x with
  | some i => decide (WellFormed i ∧ ThresholdEditingFeasible i)
  | none => false

/-- **THRESHOLD EDITING is NP-complete.** Source: Drange, Dregi, Lokshtanov and Sullivan
(2022). -/
public theorem_wanted thresholdEditing_npComplete :
    thresholdEditingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L thresholdEditingDec

end MetaMathlibExt.Complexity.NPComplete.ThresholdEditing
