/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE WEIGHTED TARDINESS with precedence constraints and unit tasks is
# NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS5] SEQUENCING TO MINIMIZE
WEIGHTED TARDINESS (comment: if precedence constraints are added, the problem is NP-complete
even with equal lengths and equal weights, credited to Lenstra and Rinnooy Kan 1978);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity of scheduling under precedence
constraints", Operations Research 26 (1978), 22-35, doi:10.1287/opre.26.1.22
(`1|prec, pⱼ = 1|∑ Tⱼ`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PrecedenceUnitTaskTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceUnitTaskTardiness

open SequencingToMinimizeWeightedTardiness (Task taskLength weight deadline
  IsOneProcessorSchedule)

/-!
# SEQUENCING TO MINIMIZE WEIGHTED TARDINESS with precedence constraints and unit tasks is
# NP-complete

INSTANCE: a set `T` of tasks, a partial order `<` on `T`, for each task `t ∈ T` a length
`l(t) = 1`, a weight `w(t) = 1` and a deadline `d(t) ∈ ℤ⁺`, and a positive integer `K`.
QUESTION: is there a one-processor schedule `σ` for `T` that obeys the precedence constraints
(`t < t'` implies `σ(t) + l(t) ≤ σ(t')`) such that the sum, taken over all `t ∈ T` satisfying
`σ(t) + l(t) > d(t)`, of `(σ(t) + l(t) - d(t)) · w(t)` is `K` or less?

This is SEQUENCING TO MINIMIZE WEIGHTED TARDINESS ([SS5]) with precedence constraints added and
all lengths and weights equal to `1` (`1|prec, pⱼ = 1|∑ Tⱼ`, the case Lenstra and Rinnooy Kan
prove). The [SS5] instance (tasks as `(l(t), w(t), d(t))` triples and the bound `K`), its
well-formedness, the task accessors and the one-processor schedule predicate are reused from
`SequencingToMinimizeWeightedTardinessDefs`. The partial order is given by the list of its
pairs `(t, t')` with `t < t'`, required to be a strict order (Mathlib's `IsStrictOrder`:
irreflexive and transitive). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SEQUENCING TO MINIMIZE WEIGHTED TARDINESS with precedence constraints and unit tasks is
NP-complete.** Source: Garey and Johnson (1979), [SS5]; Lenstra and Rinnooy Kan (1978). -/
public theorem_wanted precedenceUnitTaskTardiness_npComplete :
    precedenceUnitTaskTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precedenceUnitTaskTardinessDec

end MetaMathlibExt.Complexity.NPComplete.PrecedenceUnitTaskTardiness
