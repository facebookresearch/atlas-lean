/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HITTING SET with subsets of size at most 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP8] HITTING SET, p. 222, comment:
"Remains NP-complete even if |c| ≤ 2 for all c ∈ C";
R. M. Karp, "Reducibility among combinatorial problems", in Complexity of Computer
Computations (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (VERTEX COVER).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.HittingSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HittingSetSizeTwo

/-!
# HITTING SET with subsets of size at most 2 is NP-complete

The problem HITTING SET (`MetaMathlibExt.Complexity.NPComplete.HittingSet`), restricted to
instances in which every subset in the collection has at most two elements. INSTANCE: a
collection `C` of subsets of a finite set `S`, with `|c| ≤ 2` for all `c ∈ C`, and a positive
integer `K ≤ |S|`. QUESTION: is there a subset `S' ⊆ S` with `|S'| ≤ K` such that `S'` contains
at least one element from each subset in `C`?

The instance encoding, the well-formedness conditions of HITTING SET and the question are
those of `HittingSet`; each subset is listed without repetition there, so its list length is
its size. The instances in which every subset has exactly two elements are the VERTEX COVER
instances (Karp 1972).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the instance is well-formed for HITTING SET, and every
subset in `C` has at most two elements. -/
def WellFormed (i : HittingSet.HittingSetInstance) : Prop :=
  HittingSet.WellFormed i ∧ ∀ c ∈ i.2.1, c.length ≤ 2

open Classical in
/-- HITTING SET with subsets of size at most 2 as a decision problem over bitstrings. -/
noncomputable def hittingSetSizeTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := HittingSet.HittingSetInstance) x with
  | some i => decide (WellFormed i ∧ HittingSet.HittingSetFeasible i)
  | none => false

/-- **HITTING SET with subsets of size at most 2 is NP-complete.** Source: Garey and Johnson
(1979), [SP8], comment; Karp (1972), VERTEX COVER. -/
public theorem_wanted hittingSetSizeTwo_npComplete :
    hittingSetSizeTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hittingSetSizeTwoDec

end MetaMathlibExt.Complexity.NPComplete.HittingSetSizeTwo
