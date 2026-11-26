/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE WEIGHTED TARDINESS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS5] SEQUENCING TO MINIMIZE
WEIGHTED TARDINESS;
E. L. Lawler, "A "pseudopolynomial" algorithm for sequencing jobs to minimize total
tardiness", Annals of Discrete Mathematics 1 (1977), 331-342,
doi:10.1016/S0167-5060(08)70742-8;
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X, Theorem 4(d).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Defs
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardiness

/-!
# SEQUENCING TO MINIMIZE WEIGHTED TARDINESS is NP-complete

INSTANCE: a set `T` of tasks, for each task `t ∈ T` a length `l(t) ∈ ℤ⁺`, a weight
`w(t) ∈ ℤ⁺` and a deadline `d(t) ∈ ℤ⁺`, and a positive integer `K`. QUESTION: is there a
one-processor schedule `σ` for `T` such that the sum, taken over all `t ∈ T` satisfying
`σ(t) + l(t) > d(t)`, of `(σ(t) + l(t) - d(t)) · w(t)` is `K` or less?

A one-processor schedule (Garey and Johnson, [SS1]) is a one-to-one function `σ : T → ℤ₀⁺`
with `σ(t) > σ(t')` implying `σ(t) ≥ σ(t') + l(t')`. The tasks are `Fin n`, one per listed
triple `(l(t), w(t), d(t))`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SEQUENCING TO MINIMIZE WEIGHTED TARDINESS is NP-complete.** Source: Garey and Johnson
(1979), [SS5]; Lawler (1977); Lenstra, Rinnooy Kan, and Brucker (1977), Theorem 4(d). -/
public theorem_wanted sequencingToMinimizeWeightedTardiness_npComplete :
    sequencingToMinimizeWeightedTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sequencingToMinimizeWeightedTardinessDec

end MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardiness
