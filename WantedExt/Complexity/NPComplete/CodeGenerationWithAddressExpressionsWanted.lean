/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CODE GENERATION WITH ADDRESS EXPRESSIONS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO7] CODE GENERATION WITH ADDRESS
EXPRESSIONS, pp. 273-274 (reference [Szymanski, 1978]; transformation from 3SAT);
T. G. Szymanski, "Assembling code for machines with span-dependent instructions",
Communications of the ACM 21 (1978), 300-308, doi:10.1145/359460.359474.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CodeGenerationWithAddressExpressionsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CodeGenerationWithAddressExpressions

/-!
# CODE GENERATION WITH ADDRESS EXPRESSIONS is NP-complete

INSTANCE: a sequence `I = (I₁, I₂, …, Iₙ)` of instructions, for each `Iᵢ ∈ I` an expression
`g(Iᵢ)` of the form `Iⱼ`, `Iⱼ + k`, `Iⱼ - k`, or `k`, where `Iⱼ ∈ I` and `k ∈ Z⁺`, and positive
integers `B`, `C` and `M`.
QUESTION: can the instructions in `I` be stored as one- and two-byte instructions so that the
total memory required is at most `M`, i.e., is there a one-to-one function
`f : I → {1, 2, …, M}` such that `f(Iᵢ) < f(Iⱼ)` whenever `i < j` and such that, if `h(Iᵢ)`
is defined to be `f(Iⱼ)`, `f(Iⱼ) ± k`, or `k` depending on whether `g(Iᵢ)` is `Iⱼ`, `Iⱼ ± k`,
or `k`, then for each `i`, `1 ≤ i ≤ n`, either `-C < f(Iᵢ) - h(Iᵢ) < B` or `f(Iᵢ) + 1` is not
in the range of `f`?

The instructions are indexed by `Fin n`, `0`-based: index `j` is the instruction `I_{j+1}`. The
instance lists the expressions `g(I₁), …, g(Iₙ)`, so its length is `n`: `(0, j, 0)` is
`I_{j+1}`, `(1, j, k)` is `I_{j+1} + k`, `(2, j, k)` is `I_{j+1} - k`, and `(3, 0, k)` is the
constant `k`. The value `h(Iᵢ)` (`addressValue`) and the span `f(Iᵢ) - h(Iᵢ)` are integers. The
second byte of a two-byte instruction must also lie in `{1, …, M}` (`f(Iᵢ) + 1 ≤ M`), so that
the total memory required is at most `M`; the source's "i.e." condition leaves this implicit for
the last instruction, whose successor address is never in the range of `f`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding` (numbers in binary). Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CODE GENERATION WITH ADDRESS EXPRESSIONS is NP-complete.** Source: Garey and Johnson
(1979), [PO7]; Szymanski (1978). -/
public theorem_wanted codeGenerationWithAddressExpressions_npComplete :
    codeGenerationWithAddressExpressionsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L codeGenerationWithAddressExpressionsDec

end MetaMathlibExt.Complexity.NPComplete.CodeGenerationWithAddressExpressions
