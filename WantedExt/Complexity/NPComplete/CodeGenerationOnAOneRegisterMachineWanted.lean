/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CODE GENERATION ON A ONE-REGISTER MACHINE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), pp. 272-273, problem [PO4]
CODE GENERATION ON A ONE-REGISTER MACHINE;
J. Bruno and R. Sethi, "Code generation for a one-register machine", Journal of
the ACM 23 (1976), 502-510, doi:10.1145/321958.321971.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CodeGenerationOnAOneRegisterMachineDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CodeGenerationOnAOneRegisterMachine

/-!
# CODE GENERATION ON A ONE-REGISTER MACHINE is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)` in which no vertex has out-degree larger than
`2`, and a positive integer `K`. QUESTION: is there a program with `K` or fewer instructions
for computing all the root vertices of `G` (those with in-degree `0`) on a one-register
machine, starting with all the leaves of `G` (those with out-degree `0`) in memory and using
only LOAD, STORE and OP instructions?

The machine, as Garey and Johnson define it: a LOAD instruction copies a specified vertex
(from memory) into the register. A STORE instruction copies the vertex in the register into
memory. A new vertex `v` can be computed by an OP instruction if the vertex `u` in the register
satisfies `(v, u) ∈ A` and, if there is another vertex `u'` with `(v, u') ∈ A`, then `u'` is in
memory; executing the OP instruction replaces `u` by `v` in the register. The computation of a
new vertex is not completed until it is copied into memory by a STORE instruction, so the
program computes the roots when every root is in memory after its last instruction. The
register is empty at the start.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CODE GENERATION ON A ONE-REGISTER MACHINE is NP-complete.** Source: Garey and Johnson
(1979), [PO4]; Bruno and Sethi (1976). -/
public theorem_wanted codeGenerationOnAOneRegisterMachine_npComplete :
    codeGenerationOnAOneRegisterMachineDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L codeGenerationOnAOneRegisterMachineDec

end MetaMathlibExt.Complexity.NPComplete.CodeGenerationOnAOneRegisterMachine
