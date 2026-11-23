/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST COMMON SUPERSTRING over a binary alphabet is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR9] SHORTEST COMMON SUPERSTRING,
p. 228, comment: "Remains NP-complete even if |Σ| = 2";
J. Gallant, D. Maier, and J. A. Storer, "On finding minimal length superstrings", Journal of
Computer and System Sciences 20 (1980), 50-58, doi:10.1016/0022-0000(80)90004-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ShortestCommonSuperstringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstringBinary

/-!
# SHORTEST COMMON SUPERSTRING over a binary alphabet is NP-complete

The problem SHORTEST COMMON SUPERSTRING
(`MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstring`), restricted to instances
with `|Σ| = 2`. INSTANCE: a finite alphabet `Σ` with `|Σ| = 2`, a finite set `R` of strings from
`Σ*`, and a positive integer `K`. QUESTION: is there a string `w ∈ Σ*` with `|w| ≤ K` such that
each string `x ∈ R` is a substring of `w`, i.e., `w = w₀xw₁` where each `wᵢ ∈ Σ*`?

The instance encoding (the alphabet size `k`, the alphabet being `{0, …, k - 1}`, the strings
of `R`, and `K`), the well-formedness conditions of SHORTEST COMMON SUPERSTRING and the question
are those of `ShortestCommonSuperstring`; here additionally `k = 2`.

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
SUPERSTRING, and the alphabet has two symbols. -/
def WellFormed (i : ShortestCommonSuperstring.ShortestCommonSuperstringInstance) : Prop :=
  ShortestCommonSuperstring.WellFormed i ∧ i.1 = 2

open Classical in
/-- SHORTEST COMMON SUPERSTRING over a binary alphabet as a decision problem over bitstrings. -/
noncomputable def shortestCommonSuperstringBinaryDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShortestCommonSuperstring.ShortestCommonSuperstringInstance) x with
  | some i =>
      decide (WellFormed i ∧ ShortestCommonSuperstring.ShortestCommonSuperstringFeasible i)
  | none => false

/-- **SHORTEST COMMON SUPERSTRING over a binary alphabet is NP-complete.** Source: Garey and
Johnson (1979), [SR9], comment; Gallant, Maier, and Storer (1980). -/
public theorem_wanted shortestCommonSuperstringBinary_npComplete :
    shortestCommonSuperstringBinaryDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shortestCommonSuperstringBinaryDec

end MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstringBinary
