/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM SUM OF SQUARES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP19] MINIMUM SUM OF SQUARES,
p. 225 ("Reference: Transformation from PARTITION or 3-PARTITION. Comment: NP-complete in the
strong sense.").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumSumOfSquaresDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumSumOfSquares

/-!
# MINIMUM SUM OF SQUARES is NP-complete

INSTANCE: a finite set `A`, a size `s(a) ∈ ℤ⁺` for each `a ∈ A`, positive integers `K ≤ |A|`
and `J`. QUESTION: can `A` be partitioned into `K` disjoint sets `A₁, A₂, …, A_K` such that
`∑_{i=1}^{K} (∑_{a ∈ A_i} s(a))² ≤ J`?

The elements of `A` are `Fin |A|`, one per listed size. A partition into `A₁, …, A_K` is a map
`f : Fin |A| → Fin K` with `A_k = f⁻¹(k)`; the source does not require the parts to be
non-empty. Since `K ≤ |A|` and sizes are positive, requiring non-empty parts gives the same
answers: an empty part next to a part with two or more elements can take one of them without
increasing the sum of squares. NP-complete in the strong sense; all numbers use the binary
encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM SUM OF SQUARES is NP-complete.** Source: Garey and Johnson (1979), [SP19]. -/
public theorem_wanted minimumSumOfSquares_npComplete :
    minimumSumOfSquaresDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumSumOfSquaresDec

end MetaMathlibExt.Complexity.NPComplete.MinimumSumOfSquares
