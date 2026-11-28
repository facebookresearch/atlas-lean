/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE WEIGHTED COMPLETION WITH PRECEDENCE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), 1|prec|sum w_j C_j; E. L.
Lawler, "Sequencing jobs to minimize total weighted completion time subject to precedence
constraints", Annals of Discrete Mathematics 2 (1978), 75-90; J. K. Lenstra and A. H. G.
Rinnooy Kan, "Complexity of scheduling under precedence constraints", Operations Research 26
(1978), 22-35.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PrecedenceWeightedCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceWeightedCompletion

/-!
# SINGLE-MACHINE WEIGHTED COMPLETION WITH PRECEDENCE is NP-complete

Jobs with processing times and weights, precedence constraints, and a bound `K`. The question
is whether some ordering respecting the precedence constraints has weighted sum of completion
times at most `K`, computed by a fold over the ordering.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SINGLE-MACHINE WEIGHTED COMPLETION WITH PRECEDENCE is NP-complete.** The decision problem
SINGLE-MACHINE WEIGHTED COMPLETION WITH PRECEDENCE on bitstrings belongs to NP, and every
decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey
and D. S. Johnson, *Computers and Intractability* (1979), 1|prec|sum w_j C_j; E. L.
Lawler, "Sequencing jobs to minimize total weighted completion time subject to precedence
constraints", Annals of Discrete Mathematics 2 (1978), 75-90; J. K. Lenstra and A. H. G.
Rinnooy Kan, "Complexity of scheduling under precedence constraints", Operations Research
26 (1978), 22-35. -/
public theorem_wanted precedenceWeightedCompletion_npComplete :
    precedenceWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precedenceWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.PrecedenceWeightedCompletion
