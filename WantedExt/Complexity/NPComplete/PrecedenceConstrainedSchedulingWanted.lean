/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE CONSTRAINED SCHEDULING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS9] PRECEDENCE CONSTRAINED
SCHEDULING;
J. D. Ullman, "NP-complete scheduling problems", Journal of Computer and System Sciences 10
(1975), 384-393, doi:10.1016/S0022-0000(75)80008-0.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling

/-!
# PRECEDENCE CONSTRAINED SCHEDULING is NP-complete

INSTANCE: a set `T` of tasks, each having length `l(t) = 1`, a number `m ∈ ℤ⁺` of processors,
a partial order `<` on `T`, and a deadline `D ∈ ℤ⁺`. QUESTION: is there an `m`-processor
schedule `σ` for `T` that meets the overall deadline `D` and obeys the precedence constraints,
i.e., such that `t < t'` implies `σ(t') ≥ σ(t) + l(t) = σ(t) + 1`?

An `m`-processor schedule meeting the overall deadline `D` (Garey and Johnson, [SS8]) is a
function `σ : T → ℤ₀⁺` such that, for all `u ≥ 0`, at most `m` tasks `t` have
`σ(t) ≤ u < σ(t) + l(t)`, and `σ(t) + l(t) ≤ D` for all `t ∈ T`. The tasks are `Fin n`, one
per listed length (every listed length must be `1`). The partial order is given by the list of
its pairs `(t, t')` with `t < t'`, required to be a strict order (Mathlib's `IsStrictOrder`:
irreflexive and transitive). Binary encoding of all numbers (the problem is NP-complete in the
strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PRECEDENCE CONSTRAINED SCHEDULING is NP-complete.** Source: Garey and Johnson (1979),
[SS9]; Ullman (1975). -/
public theorem_wanted precedenceConstrainedScheduling_npComplete :
    precedenceConstrainedSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precedenceConstrainedSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling
