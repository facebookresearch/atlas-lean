/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMPARATIVE DIVISIBILITY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN4] COMPARATIVE DIVISIBILITY;
D. A. Plaisted, "Some polynomial and integer divisibility problems are NP-hard",
Proc. 17th Annual Symposium on Foundations of Computer Science (1976), 264-267,
doi:10.1109/SFCS.1976.29; journal version SIAM Journal on Computing 7 (1978), 458-464,
doi:10.1137/0207036.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ComparativeDivisibility

/-!
# COMPARATIVE DIVISIBILITY is NP-complete

Given sequences `a₁, …, aₙ` and `b₁, …, bₘ` of positive integers, is there a positive integer
`c` such that the number of `i` for which `c` divides `aᵢ` is more than the number of `j` for
which `c` divides `bⱼ`? The sequences may repeat entries; each occurrence is counted.

Numbers use the canonical binary encoding (the problem is NP-complete in the weak sense:
trying every `c ≤ max aᵢ` is pseudo-polynomial).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the sequence `a₁, …, aₙ` and the sequence `b₁, …, bₘ`. -/
abbrev ComparativeDivisibilityInstance := List ℕ × List ℕ

/-- Well-formedness of an instance: every entry of both sequences is positive. -/
def WellFormed (i : ComparativeDivisibilityInstance) : Prop :=
  (∀ a ∈ i.1, 0 < a) ∧ ∀ b ∈ i.2, 0 < b

/-- Some positive integer `c` divides more entries of the first sequence than of the second,
counting entries with multiplicity. -/
def ComparativeDivisibilityFeasible (i : ComparativeDivisibilityInstance) : Prop :=
  ∃ c : ℕ, 0 < c ∧ i.2.countP (fun b => c ∣ b) < i.1.countP (fun a => c ∣ a)

open Classical in
/-- COMPARATIVE DIVISIBILITY as a decision problem over bitstrings. -/
noncomputable def comparativeDivisibilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ComparativeDivisibilityInstance) x with
  | some i => decide (WellFormed i ∧ ComparativeDivisibilityFeasible i)
  | none => false

/-- **COMPARATIVE DIVISIBILITY is NP-complete.** Source: Garey and Johnson (1979), [AN4];
Plaisted (1976, 1978). -/
public theorem_wanted comparativeDivisibility_npComplete :
    comparativeDivisibilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L comparativeDivisibilityDec

end MetaMathlibExt.Complexity.NPComplete.ComparativeDivisibility
