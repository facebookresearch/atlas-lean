/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM SUM OF `α`-TH POWERS is NP-complete for every fixed integer `α ≥ 2`

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP19] MINIMUM SUM OF SQUARES, p. 225,
comment: NP-completeness is preserved if the exponent `2` is replaced by any fixed rational
`α > 1` (stated here for the integer exponents `α ≥ 2`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumSumOfAlphaPowersDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumSumOfAlphaPowers

/-!
# MINIMUM SUM OF `α`-TH POWERS is NP-complete for every fixed integer `α ≥ 2`

Fix an integer `α ≥ 2`. INSTANCE: a finite set `A`, a size `s(a) ∈ ℤ⁺` for each `a ∈ A`, and
positive integers `K ≤ |A|` and `J`. QUESTION: can `A` be partitioned into `K` disjoint sets
`A₁, A₂, …, A_K` such that `∑ᵢ (∑_{a ∈ Aᵢ} s(a))^α ≤ J`?

This is Garey and Johnson's MINIMUM SUM OF SQUARES with the exponent `2` replaced by `α`, which
their comment records as preserving NP-completeness for every fixed rational `α > 1`. The module
states the integer exponents: for a non-integral `α` a certificate check must compare a sum of
radicals with `J` exactly, whose complexity in the bit model is open (as for the sum of square
roots), so membership in `NP` of the bitstring problem is not established for those `α`. `A` is
the index set of the list of sizes, the partition is a map `f : A → Fin K` (`Aⱼ = f⁻¹(j)`), and
the sum of `α`-th powers is computed in `ℕ`. A set `Aⱼ` may be empty,
following Garey and Johnson's convention (their [SP18] comment says "`K` non-empty sets" when it
means it); since `K ≤ |A|`, every size is positive and `x ↦ x^α` is superadditive, splitting a
set never increases the sum, so requiring non-empty sets gives the same answer. The theorem is
stated for each fixed `α`, as a binder with `2 ≤ α`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances. Numbers use the canonical binary
encoding.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM SUM OF `α`-TH POWERS is NP-complete for every fixed integer `α ≥ 2`.** Source:
Garey and Johnson (1979), [SP19], comment. -/
public theorem_wanted minimumSumOfAlphaPowers_npComplete (α : ℕ) (hα : 2 ≤ α) :
    minimumSumOfAlphaPowersDec α ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (minimumSumOfAlphaPowersDec α)

end MetaMathlibExt.Complexity.NPComplete.MinimumSumOfAlphaPowers
