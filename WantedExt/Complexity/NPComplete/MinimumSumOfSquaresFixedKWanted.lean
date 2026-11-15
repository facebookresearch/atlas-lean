/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM SUM OF SQUARES with a fixed number K ≥ 2 of sets is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP19] MINIMUM SUM OF SQUARES,
p. 225 ("Reference: Transformation from PARTITION or 3-PARTITION. Comment: [...] NP-complete in
the ordinary sense and solvable in pseudo-polynomial time for any fixed K.").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MinimumSumOfSquaresWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumSumOfSquaresFixedK

open MetaMathlibExt.Complexity.NPComplete.MinimumSumOfSquares (MinimumSumOfSquaresFeasible)

/-!
# MINIMUM SUM OF SQUARES with a fixed number K ≥ 2 of sets is NP-complete

For a fixed integer `K ≥ 2`: INSTANCE: a finite set `A`, a size `s(a) ∈ ℤ⁺` for each `a ∈ A`,
and a positive integer `J`, where `K ≤ |A|`. QUESTION: can `A` be partitioned into `K` disjoint
sets `A₁, A₂, …, A_K` such that `∑_{i=1}^{K} (∑_{a ∈ A_i} s(a))² ≤ J`?

This is [SP19] (`WantedExt.Complexity.NPComplete.MinimumSumOfSquaresWanted`) with `K` no longer
part of the instance but a parameter of the problem, one problem for each `K`; the theorem
states NP-completeness for every fixed `K ≥ 2`. The sizes, `J`, well-formedness (positive sizes,
`K ≤ |A|`, positive `J`) and the question are those of that module, applied to `(s, K, J)`.
NP-complete in the ordinary sense (the [SP19] comment: pseudo-polynomial for fixed `K`); all
numbers use the binary encoding. For `K = 1` the question is a single comparison.

Hardness for fixed `K ≥ 2`, from PARTITION (the [SP19] reference; the repository's PARTITION takes a
list of natural numbers, possibly empty or with zeros): zero sizes do not affect a PARTITION
instance, so drop them. If no size remains, the PARTITION instance is a yes-instance; output `K`
elements of size 1 with `J = K` (one element per part). If one size remains or the remaining sum `S`
is odd, it is a no-instance; output `K` elements of size 1 with `J = K - 1` (every partition has sum
of squares at least `K`). Otherwise there are positive sizes `a₁, …, a_m` with `m ≥ 2` and even sum
`S`; add `K - 2` elements of size `S / 2` and set `J = K (S / 2)²`. The `K` part sums add up to
`K S / 2`, so by convexity the sum of squares is at least `K (S / 2)²`, with equality iff every part
sums to `S / 2`. Since sizes are positive, an added element fills its part alone, so equality holds
iff the original elements split into two parts of sum `S / 2` each, that is, iff the PARTITION
instance is a yes-instance; and `K ≤ m + K - 2`. Membership in NP is inherited from [SP19]: the
partition is a certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance for a fixed `K`: the sizes `s(a)` of the elements of `A` (element `a` is the
`a`-th entry) and the bound `J`. -/
abbrev MinimumSumOfSquaresFixedKInstance := List ℕ × ℕ

/-- The [SP19] instance with `K` sets. -/
def withK (K : ℕ) (i : MinimumSumOfSquaresFixedKInstance) :
    MinimumSumOfSquares.MinimumSumOfSquaresInstance :=
  (i.1, K, i.2)

/-- Well-formedness of an instance for `K`: the [SP19] instance with `K` sets is well formed
(every size positive, `0 < K ≤ |A|`, `J` positive). -/
def WellFormed (K : ℕ) (i : MinimumSumOfSquaresFixedKInstance) : Prop :=
  MinimumSumOfSquares.WellFormed (withK K i)

/-- Some partition of `A` into `K` disjoint sets has sum of squares at most `J` (the [SP19]
question). -/
def MinimumSumOfSquaresFixedKFeasible (K : ℕ) (i : MinimumSumOfSquaresFixedKInstance) : Prop :=
  MinimumSumOfSquaresFeasible (withK K i)

open Classical in
/-- MINIMUM SUM OF SQUARES with `K` sets as a decision problem over bitstrings. -/
noncomputable def minimumSumOfSquaresFixedKDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumSumOfSquaresFixedKInstance) x with
  | some i => decide (WellFormed K i ∧ MinimumSumOfSquaresFixedKFeasible K i)
  | none => false

/-- **MINIMUM SUM OF SQUARES with a fixed number `K ≥ 2` of sets is NP-complete.** Source:
Garey and Johnson (1979), [SP19], comment. -/
public theorem_wanted minimumSumOfSquaresFixedK_npComplete (K : ℕ) (hK : 2 ≤ K) :
    minimumSumOfSquaresFixedKDec K ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (minimumSumOfSquaresFixedKDec K)

end MetaMathlibExt.Complexity.NPComplete.MinimumSumOfSquaresFixedK
