/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INEQUIVALENCE OF LOOP PROGRAMS WITHOUT NESTING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO14] INEQUIVALENCE OF LOOP
PROGRAMS WITHOUT NESTING;
R. L. Constable, H. B. Hunt III, and S. Sahni, "On the computational complexity of program
scheme equivalence", SIAM Journal on Computing 9 (1980), 396-416, doi:10.1137/0209031
(journal version of Cornell report TR 74-201 (1974), which Garey and Johnson cite; NP-hardness
of equivalence for the Loop 1 language);
D. Tsichritzis, "The equivalence problem of simple programs", Journal of the ACM 17 (1970),
729-738, doi:10.1145/321607.321621 (membership in NP).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.InequivalenceLoopProgramsWithoutNestingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InequivalenceLoopProgramsWithoutNesting

/-!
# INEQUIVALENCE OF LOOP PROGRAMS WITHOUT NESTING is NP-complete

Given a finite set `X` of variables, a subset `Y ⊆ X` of input variables, a specified output
variable `x₀ ∈ X`, and two programs `P₁` and `P₂`, each a sequence of instructions of the form
`x ← y`, `x ← x + 1`, `x ← 0`, `loop x`, and `end` with `x, y ∈ X`, where each `loop`
instruction is followed by a corresponding `end` instruction before any further `loop`
instruction occurs, is there an initial assignment `f : Y → ℤ⁺` such that the two programs halt
with different values for the output variable `x₀`?

Semantics (the Loop language of Meyer and Ritchie, restricted to loop depth `1`, the language
`L₁` of Tsichritzis and the Loop 1 language of Constable, Hunt and Sahni): variables hold
natural numbers; an input variable `y ∈ Y` starts at `f y ≥ 1` and every other variable starts
at `0`; `loop x … end` runs its body as many times as the value of `x` on entering the loop
(changes to `x` inside the body do not change that count). Every such program halts.

The variables are `0, …, n - 1`. An instruction is a triple `(op, x, y)`: `op = 0` is `x ← y`,
`1` is `x ← x + 1`, `2` is `x ← 0`, `3` is `loop x`, and `4` is `end`; operands an instruction
does not use are ignored. `WellFormed` requires opcodes `< 5`, operands `< n`, `Y` a set of
variables, `x₀` a variable, and, in each program, `loop` and `end` alternating, starting with a
`loop` and ending with an `end` (no nesting, no unmatched `loop` or `end`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INEQUIVALENCE OF LOOP PROGRAMS WITHOUT NESTING is NP-complete.** Source: Garey and
Johnson (1979), [PO14]; Constable, Hunt and Sahni (1974, 1980); Tsichritzis (1970). -/
public theorem_wanted inequivalenceLoopPrograms_npComplete :
    inequivalenceLoopProgramsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inequivalenceLoopProgramsDec

end MetaMathlibExt.Complexity.NPComplete.InequivalenceLoopProgramsWithoutNesting
