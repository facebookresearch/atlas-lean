/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMPARATIVE DIVISIBILITY with distinct elements is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN4] COMPARATIVE DIVISIBILITY,
p. 249, comment: "Remains NP-complete even if all `aᵢ` are different and all `bⱼ` are
different", credited there to Garey and Johnson (unpublished; no published proof was
available). The general problem is due to D. A. Plaisted, "Some polynomial and integer
divisibility problems are NP-hard", SIAM Journal on Computing 7 (1978), 458-464,
doi:10.1137/0207036.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ComparativeDivisibilityWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ComparativeDivisibilityDistinct

open MetaMathlibExt.Complexity.NPComplete.ComparativeDivisibility

/-!
# COMPARATIVE DIVISIBILITY with distinct elements is NP-complete

INSTANCE: sequences `a₁, …, aₙ` and `b₁, …, bₘ` of positive integers, with all `aᵢ`
different and all `bⱼ` different (the comment's restriction). QUESTION: is there a positive
integer `c` such that the number of `i` for which `c` divides `aᵢ` is more than the number of
`j` for which `c` divides `bⱼ`?

The instance and the question are those of `ComparativeDivisibilityWanted`
(`ComparativeDivisibility.ComparativeDivisibilityInstance` and
`ComparativeDivisibility.ComparativeDivisibilityFeasible`); `WellFormed` adds that each
sequence has no repeated entry (`List.Nodup`). Numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: every entry is positive (`ComparativeDivisibility`), the
`aᵢ` are pairwise different, and the `bⱼ` are pairwise different. -/
def WellFormed (i : ComparativeDivisibilityInstance) : Prop :=
  ComparativeDivisibility.WellFormed i ∧ i.1.Nodup ∧ i.2.Nodup

open Classical in
/-- COMPARATIVE DIVISIBILITY with distinct elements as a decision problem over bitstrings. -/
noncomputable def comparativeDivisibilityDistinctDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ComparativeDivisibilityInstance) x with
  | some i => decide (WellFormed i ∧ ComparativeDivisibilityFeasible i)
  | none => false

/-- **COMPARATIVE DIVISIBILITY with distinct elements is NP-complete.** Source: Garey and
Johnson (1979), [AN4], comment (Garey and Johnson, unpublished). -/
public theorem_wanted comparativeDivisibilityDistinct_npComplete :
    comparativeDivisibilityDistinctDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L comparativeDivisibilityDistinctDec

end MetaMathlibExt.Complexity.NPComplete.ComparativeDivisibilityDistinct
