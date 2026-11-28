/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POSITIONAL SEQUENCING BY HYBRIDIZATION: definitions

Source:
A. Ben-Dor, I. Pe'er, R. Shamir and R. Sharan, "On the complexity of positional sequencing by
hybridization", Journal of Computational Biology 8 (2001), 361-371,
doi:10.1089/106652701752236188 (abstract: PSBH is NP-complete if each substring has at most
three possible positions); the authors' version (www.cs.tau.ac.il/~roded/articles/positional.pdf)
defines PSBH as Problem 3 and proves, as Theorem 3, that 3-PSBH is NP-complete, even if all
spectrum elements have multiplicity one.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Bioinformatics.Assembly.DeBruijn

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PositionalSequencingByHybridization

open Cslib.Bioinformatics.Assembly.DeBruijn (kmers)

/-- An instance: the length `p` and the spectrum as a list of pairs `(s, P(s))` of a string and
its allowed positions. -/
abbrev PositionalSequencingByHybridizationInstance := ℕ × List (List ℕ × List ℕ)

/-- Well-formedness of an instance: `p` is positive; every string of the spectrum has length `p`
and letters among `0, 1, 2, 3`, and its allowed positions are below `|S|`; and copies of the same
string have the same allowed positions (each copy's positions are allowed for every other copy,
so the sets are equal). -/
def WellFormed (i : PositionalSequencingByHybridizationInstance) : Prop :=
  0 < i.1 ∧
    (∀ e ∈ i.2, e.1.length = i.1 ∧ (∀ c ∈ e.1, c < 4) ∧ ∀ j ∈ e.2, j < i.2.length) ∧
    ∀ e ∈ i.2, ∀ e' ∈ i.2, e.1 = e'.1 → ∀ j ∈ e.2, j ∈ e'.2

/-- Some string `X` over `{A, C, G, T}` has `S` as its `p`-spectrum, and the substring starting
at each position `j` has `j` among its allowed positions. -/
def PositionalSequencingByHybridizationFeasible
    (i : PositionalSequencingByHybridizationInstance) : Prop :=
  ∃ X : List ℕ, (∀ c ∈ X, c < 4) ∧ (kmers i.1 X).Perm (i.2.map Prod.fst) ∧
    ∀ j < X.length + 1 - i.1, ∀ e ∈ i.2, e.1 = (X.drop j).take i.1 → j ∈ e.2

open Classical in
/-- POSITIONAL SEQUENCING BY HYBRIDIZATION as a decision problem over bitstrings. -/
noncomputable def positionalSequencingByHybridizationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PositionalSequencingByHybridizationInstance) x with
  | some i => decide (WellFormed i ∧ PositionalSequencingByHybridizationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PositionalSequencingByHybridization
