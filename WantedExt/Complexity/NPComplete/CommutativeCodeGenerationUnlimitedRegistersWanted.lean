/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMMUTATIVE CODE GENERATION WITH UNLIMITED REGISTERS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO5] CODE GENERATION WITH UNLIMITED
REGISTERS, p. 273 (comment: the "commutative" variant in which instructions of the form
`rᵢ ← rⱼ op rᵢ` are also allowed is NP-complete [Aho, Johnson, and Ullman, 1977b]; Garey and
Johnson list [Aho, Johnson, and Ullman, 1977b] as a private communication, which was not
available);
A. V. Aho, S. C. Johnson, and J. D. Ullman, "Code generation for expressions with common
subexpressions", Journal of the ACM 24 (1977), 146-160, doi:10.1145/321992.322001 (the
non-commutative problem [PO5]).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CommutativeCodeGenerationUnlimitedRegistersDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CommutativeCodeGenerationUnlimitedRegisters

open CodeGenerationWithUnlimitedRegisters (Graph IsLeaf Instruction Registers Step)

/-!
# COMMUTATIVE CODE GENERATION WITH UNLIMITED REGISTERS is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)` in which no vertex has out-degree larger than
`2`, a partition of `A` into disjoint sets `L` and `R` such that two arcs leaving the same
vertex always belong to different sets, and a positive integer `K`. QUESTION: is there a
program with `K` or fewer instructions for computing all the root vertices of `G`, starting
with all the leaves of `G` stored in registers and using only instructions of the form
`rᵢ ← rⱼ`, `rᵢ ← rᵢ op rⱼ` or `rᵢ ← rⱼ op rᵢ`, where a vertex `v` with out-degree `2` and
outgoing arcs `(v, u) ∈ L` and `(v, w) ∈ R` can be computed by `rᵢ ← rᵢ op rⱼ` when `rᵢ`
contains `u` and `rⱼ` contains `w`, and by `rᵢ ← rⱼ op rᵢ` when `rⱼ` contains `u` and `rᵢ`
contains `w`?

This is the "commutative" variant of [PO5] CODE GENERATION WITH UNLIMITED REGISTERS
(`WantedExt.Complexity.NPComplete.CodeGenerationWithUnlimitedRegistersWanted`): the result of
an OP instruction may replace either operand. The instance type, `WellFormed`, the digraph,
the leaves, the parent's instructions `rᵢ ← rⱼ` and `rᵢ ← rᵢ op rⱼ` with their semantics
`Step`, and the reading of the machine (unboundedly many registers, each leaf in exactly one
register at the start and nothing else stored, each root held by some register at some point
of the run) are those of the parent, reused unchanged. This module adds the instruction
`rᵢ ← rⱼ op rᵢ` (`CommInstruction.opRev`, semantics `CommStep`) and states the question for
programs over both kinds of instructions.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **COMMUTATIVE CODE GENERATION WITH UNLIMITED REGISTERS is NP-complete.** Source: Garey and
Johnson (1979), [PO5]; Aho, Johnson, and Ullman (1977b). -/
public theorem_wanted commutativeCodeGenerationUnlimitedRegisters_npComplete :
    commutativeCodeGenerationUnlimitedRegistersDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L commutativeCodeGenerationUnlimitedRegistersDec

end MetaMathlibExt.Complexity.NPComplete.CommutativeCodeGenerationUnlimitedRegisters
