/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POSITIONAL SEQUENCING BY HYBRIDIZATION is NP-complete

Source:
A. Ben-Dor, I. Pe'er, R. Shamir and R. Sharan, "On the complexity of positional sequencing by
hybridization", Journal of Computational Biology 8 (2001), 361-371,
doi:10.1089/106652701752236188 (abstract: PSBH is NP-complete if each substring has at most
three possible positions); the authors' version (www.cs.tau.ac.il/~roded/articles/positional.pdf)
defines PSBH as Problem 3 and proves, as Theorem 3, that 3-PSBH is NP-complete, even if all
spectrum elements have multiplicity one.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Bioinformatics.Assembly.DeBruijn

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PositionalSequencingByHybridization

open Cslib.Bioinformatics.Assembly.DeBruijn (kmers)

/-!
# POSITIONAL SEQUENCING BY HYBRIDIZATION is NP-complete

INSTANCE: a multi-set `S` of `p`-long strings over `Σ = {A, C, G, T}` and, for each `s ∈ S`, a
set `P(s) ⊆ {0, …, |S| - 1}` of allowed positions.
QUESTION: is `S` the `p`-spectrum of some string `X`, the multi-set of all `p`-long substrings
of `X`, such that for each `s ∈ S` its position along `X` is in `P(s)`?

The letters `A, C, G, T` are `0, 1, 2, 3`. The instance lists the spectrum as pairs `(s, P(s))`;
a string listed `k` times has multiplicity `k`, and all its copies carry the same position set
(`WellFormed`), since `P` is a function of `s`. The `p`-long substrings of `X` start at the
positions `0, …, |X| - p` (`Cslib.Bioinformatics.Assembly.DeBruijn.kmers p X`, whose entry `j`
is `(X.drop j).take p`); `S` is the `p`-spectrum of `X` when these substrings,
counted with multiplicity, are a permutation (`List.Perm`) of the strings of `S`. The position
condition requires the substring starting at position `j` to have `j` among its allowed
positions. The source states the result for at most three allowed positions per string
(`3-PSBH`), a special case of this problem; it also notes that membership in `NP` is easy.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **POSITIONAL SEQUENCING BY HYBRIDIZATION is NP-complete.** Source: Ben-Dor, Pe'er, Shamir and
Sharan (2001). -/
public theorem_wanted positionalSequencingByHybridization_npComplete :
    positionalSequencingByHybridizationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L positionalSequencingByHybridizationDec

end MetaMathlibExt.Complexity.NPComplete.PositionalSequencingByHybridization
