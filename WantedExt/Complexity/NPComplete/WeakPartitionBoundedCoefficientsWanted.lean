/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEAK PARTITION with coefficients bounded by a fixed K is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982),
182-195, doi:10.1016/0196-6774(82)90018-9, problem [9] WEAK PARTITION, comment ("This problem
remains NP-complete even if we allow solutions with |xᵢ| as large as K, for any fixed K");
P. van Emde Boas, "Another NP-complete partition problem and the complexity of computing short
vectors in a lattice", Report 81-04, Department of Mathematics, University of Amsterdam (1981),
Theorem 1 (BOUNDED HOMOGENEOUS LINEAR EQUATION).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.WeakPartitionBoundedCoefficientsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeakPartitionBoundedCoefficients

open MetaMathlibExt.Complexity.NPComplete.Partition (PartitionInstance)
open MetaMathlibExt.Complexity.NPComplete.WeakPartition (WellFormed)

/-!
# WEAK PARTITION with coefficients bounded by a fixed K is NP-complete

Fix a positive integer `K`.
INSTANCE: a finite set `A = {a₁, …, aₙ}` and a size `s(a) ∈ ℤ⁺` for each `a ∈ A`.
QUESTION: is there an integer vector `(x₁, …, xₙ)`, not all `xᵢ = 0`, with `|xᵢ| ≤ K` for all
`i` and `∑ᵢ xᵢ · s(aᵢ) = 0`?

Johnson's column restates WEAK PARTITION (problem [9]) as this equation with `|xᵢ| ≤ 1` and
records that it remains NP-complete when the `|xᵢ|` may be as large as `K`, for any fixed `K`,
citing van Emde Boas. Van Emde Boas proves Theorem 1 (BOUNDED HOMOGENEOUS LINEAR EQUATION is
NP-complete) by a reduction from PARTITION that takes the bound `K` as a parameter, so it gives
a reduction for each fixed `K`; the sizes it constructs are positive. For `K = 1` the question
is WEAK PARTITION (`A₁ = {aᵢ : xᵢ = 1}`, `A₂ = {aᵢ : xᵢ = -1}`). The problem is in NP because a
vector with `|xᵢ| ≤ K` is a certificate of polynomial size.

The instance type and the well-formedness condition (every size is positive) are those of
`WantedExt.Complexity.NPComplete.WeakPartitionWanted`: the elements of `A` are the positions
`Fin n` of the list of sizes. The parameter `K` is fixed, as in the source, so there is one
decision problem for each `K`. Sizes are encoded in binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **WEAK PARTITION with coefficients bounded by `K` is NP-complete for every fixed positive
integer `K`.** Source: Johnson, NP-completeness column (1982), problem [9], comment; van Emde
Boas (1981), Theorem 1. -/
public theorem_wanted weakPartitionBoundedCoefficients_npComplete (K : ℕ) (hK : 1 ≤ K) :
    weakPartitionBoundedCoefficientsDec K ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (weakPartitionBoundedCoefficientsDec K)

end MetaMathlibExt.Complexity.NPComplete.WeakPartitionBoundedCoefficients
