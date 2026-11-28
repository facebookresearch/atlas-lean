/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CODE GENERATION WITH UNLIMITED REGISTERS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 273, problem [PO5] CODE
GENERATION WITH UNLIMITED REGISTERS;
A. V. Aho, S. C. Johnson, and J. D. Ullman, "Code generation for expressions
with common subexpressions", Journal of the ACM 24 (1977), 146-160,
doi:10.1145/321992.322001.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CodeGenerationWithUnlimitedRegistersDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CodeGenerationWithUnlimitedRegisters

/-!
# CODE GENERATION WITH UNLIMITED REGISTERS is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)` in which no vertex has out-degree larger than
`2`, a partition of `A` into disjoint sets `L` and `R` such that two arcs leaving the same
vertex always belong to different sets, and a positive integer `K`. QUESTION: is there a
program with `K` or fewer instructions for computing all the root vertices of `G` (those with
in-degree `0`), starting with all the leaves of `G` (those with out-degree `0`) stored in
registers and using only instructions of the form `rᵢ ← rⱼ` or `rᵢ ← rᵢ op rⱼ`, `i, j ∈ ℤ⁺`,
where a vertex `v` with out-degree `2` and outgoing arcs `(v, u) ∈ L` and `(v, w) ∈ R` can be
computed only by an instruction `rᵢ ← rᵢ op rⱼ` when `rᵢ` contains `u` and `rⱼ` contains `w`?

Reading of the machine. Registers are indexed by `ℕ` (there is no bound on how many are used).
At the start each leaf is in exactly one register and no register holds anything else (with
unboundedly many registers, which registers hold the leaves does not matter). `rᵢ ← rⱼ`
copies the content of `rⱼ` into `rᵢ`; `rᵢ ← rᵢ op rⱼ` computes a vertex `v` as above and puts
it in `rᵢ`. The program computes the roots when each root is held by some register at some
point of the run. Garey and Johnson give the OP instruction only for vertices of out-degree
`2`, so a vertex of out-degree `1` is never computed, as their entry reads.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CODE GENERATION WITH UNLIMITED REGISTERS is NP-complete.** Source: Garey and Johnson
(1979), [PO5]; Aho, Johnson, and Ullman (1977). -/
public theorem_wanted codeGenerationWithUnlimitedRegisters_npComplete :
    codeGenerationWithUnlimitedRegistersDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L codeGenerationWithUnlimitedRegistersDec

end MetaMathlibExt.Complexity.NPComplete.CodeGenerationWithUnlimitedRegisters
