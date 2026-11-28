/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR SCHEDULING WITH SPEED FACTORS is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM MULTIPROCESSOR SCHEDULING WITH SPEED FACTORS;
M. R. Garey and D. S. Johnson, ""Strong" NP-completeness results: motivation, examples, and
implications", Journal of the ACM 25 (1978), 499-508, doi:10.1145/322077.322090
(MULTIPROCESSOR SCHEDULING is NP-complete in the strong sense);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS8] MULTIPROCESSOR SCHEDULING.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultiprocessorSchedulingSpeedFactorsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorSchedulingSpeedFactors

open MetaMathlibExt.Complexity.NPComplete.MultiprocessorScheduling
  (MultiprocessorSchedulingInstance Task taskLength)

/-!
# MULTIPROCESSOR SCHEDULING WITH SPEED FACTORS is NP-complete

INSTANCE: a set `T` of tasks, a number `m` of processors, a length `l(t) ∈ ℤ⁺` for each task
`t ∈ T`, a speed factor `s(i) ∈ ℚ` for each processor `i ∈ [1..m]` with `s(1) = 1` and
`s(i) ≥ 1` for every `i`, and a positive integer `K`.
QUESTION: is there an `m`-processor schedule for `T`, a function `f : T → [1..m]`, whose finish
time `max_{i ∈ [1..m]} ∑_{t ∈ T, f(t) = i} l(t) / s(i)` is at most `K`?

This is the decision version of MINIMUM MULTIPROCESSOR SCHEDULING WITH SPEED FACTORS in the
Crescenzi-Kann compendium (scheduling on uniform processors). With every speed factor `1` the
finish time of `f` is the largest total length assigned to one processor, so the problem
contains MULTIPROCESSOR SCHEDULING ([SS8], `MultiprocessorSchedulingWanted`: the tasks assigned
to a processor run back to back), which Garey and Johnson proved NP-complete in the strong
sense. A certificate is `f`.

The tasks, their lengths, the number `m` of processors and the bound `K` are a
`MultiprocessorScheduling` instance (`m` is the number of listed speed factors), with that
problem's tasks `Fin n`, lengths and well-formedness (positive lengths, `m` and `K`). Processor
`i` is `Fin m`, and its speed factor is a pair `(a, b)` standing for `a / b`. All numbers are in
binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MULTIPROCESSOR SCHEDULING WITH SPEED FACTORS is NP-complete.** Source: Crescenzi and
Kann, MINIMUM MULTIPROCESSOR SCHEDULING WITH SPEED FACTORS; Garey and Johnson (1978); Garey and
Johnson (1979), [SS8]. -/
public theorem_wanted multiprocessorSchedulingSpeedFactors_npComplete :
    multiprocessorSchedulingSpeedFactorsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorSchedulingSpeedFactorsDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorSchedulingSpeedFactors
