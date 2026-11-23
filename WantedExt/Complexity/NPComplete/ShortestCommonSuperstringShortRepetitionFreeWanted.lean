/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST COMMON SUPERSTRING with short repetition-free strings is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR9] SHORTEST COMMON SUPERSTRING,
p. 228, comment: "Remains NP-complete even if ... all x ∈ R have |x| ≤ 8 and contain no
repeated symbols", reference [Maier and Storer, 1977], Report No. 233, Princeton University;
J. Gallant, D. Maier and J. A. Storer, "On finding minimal length superstrings", Journal of
Computer and System Sciences 20 (1980), 50-58, doi:10.1016/0022-0000(80)90004-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ShortestCommonSuperstringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstringShortRepetitionFree

open MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstring
  (ShortestCommonSuperstringInstance ShortestCommonSuperstringFeasible)

/-!
# SHORTEST COMMON SUPERSTRING with short repetition-free strings is NP-complete

The problem SHORTEST COMMON SUPERSTRING
(`MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstring`), restricted to instances in
which all `x ∈ R` have `|x| ≤ 8` and contain no repeated symbols. INSTANCE: a finite alphabet
`Σ`, a finite set `R` of strings from `Σ*`, each of length at most `8` and with no repeated
symbol, and a positive integer `K`. QUESTION: is there a string `w ∈ Σ*` with `|w| ≤ K` such that
each string `x ∈ R` is a substring of `w`, i.e., `w = w₀ x w₁` where each `wᵢ ∈ Σ*`?

The instance encoding (the alphabet size `k`, the alphabet being `{0, …, k - 1}`, the strings
of `R` as lists of symbols, and `K`), the well-formedness conditions of SHORTEST COMMON
SUPERSTRING and the question are those of `ShortestCommonSuperstring`; here additionally every
string of `R` has length at most `8` and no repeated symbol (`List.Nodup`). Numbers use the
binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the instance is well-formed for SHORTEST COMMON
SUPERSTRING, and every string of `R` has length at most `8` and no repeated symbol. -/
def WellFormed (i : ShortestCommonSuperstringInstance) : Prop :=
  ShortestCommonSuperstring.WellFormed i ∧ ∀ x ∈ i.2.1, x.length ≤ 8 ∧ x.Nodup

open Classical in
/-- SHORTEST COMMON SUPERSTRING with short repetition-free strings as a decision problem over
bitstrings. -/
noncomputable def shortestCommonSuperstringShortRepetitionFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShortestCommonSuperstringInstance) x with
  | some i => decide (WellFormed i ∧ ShortestCommonSuperstringFeasible i)
  | none => false

/-- **SHORTEST COMMON SUPERSTRING with strings of length at most `8` and no repeated symbols is
NP-complete.** Source: Garey and Johnson (1979), [SR9], comment (Maier and Storer, 1977);
Gallant, Maier and Storer (1980). -/
public theorem_wanted shortestCommonSuperstringShortRepetitionFree_npComplete :
    shortestCommonSuperstringShortRepetitionFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shortestCommonSuperstringShortRepetitionFreeDec

end MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstringShortRepetitionFree
