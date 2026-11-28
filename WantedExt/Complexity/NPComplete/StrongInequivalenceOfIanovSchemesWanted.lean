/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRONG INEQUIVALENCE OF IANOV SCHEMES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO16] STRONG INEQUIVALENCE OF
IANOV SCHEMES, p. 276 (references [Constable, Hunt, and Sahni, 1974] and [Rutledge, 1964];
transformation from 3SAT);
R. L. Constable, H. B. Hunt III and S. Sahni, "On the computational complexity of program
scheme equivalence", SIAM Journal on Computing 9 (1980), 396-416, doi:10.1137/0209031
(journal version of the 1974 Cornell report GJ cites: strong equivalence of single variable
program schemes is NP-complete);
J. D. Rutledge, "On Ianov's program schemata", Journal of the ACM 11 (1964), 1-9,
doi:10.1145/321203.321204 (membership in NP, per GJ).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.StrongInequivalenceOfIanovSchemesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StrongInequivalenceOfIanovSchemes

/-!
# STRONG INEQUIVALENCE OF IANOV SCHEMES is NP-complete

INSTANCE: finite sets `F` and `P` of function and predicate symbols, a single variable `x`,
and two Ianov schemes over `F`, `P` and `x`, each a sequence `I₁, I₂, …, Iₘ` of instructions
of the form `x ← f(x)`, `if p(x) then goto Iⱼ else goto Iₖ`, and `halt`, where `f ∈ F` and
`p ∈ P`.
QUESTION: are the two given Ianov schemes not strongly equivalent, i.e., is there a domain
set `D`, an interpretation of each `f ∈ F` as a function `f : D → D`, an interpretation of
each `p ∈ P` as a function `p : D → {T, F}`, and an initial value `x₀ ∈ D` for `x`, such that
either both schemes halt with different final values for `x` or one halts and the other
doesn't?

The symbols are `f₀, …, f_{|F|-1}` and `p₀, …, p_{|P|-1}`; interpretations are families
indexed by `ℕ`, of which only the indices below `|F|` and `|P|` occur. A scheme is its
instruction list: `(0, r, 0, 0)` is `x ← f_r(x)`, `(1, r, j, k)` is
`if p_r(x) then goto Iⱼ else goto Iₖ` (targets numbered from `1` as in the source), and
`(2, 0, 0, 0)` is `halt`. Execution starts at `I₁` with `x = x₀`; after `x ← f(x)` control
passes to the next instruction; a scheme halts when control reaches a `halt`. A well-formed
scheme is nonempty, its jump targets lie in `1, …, m`, and its last instruction is not an
assignment, so control never leaves `I₁, …, Iₘ`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **STRONG INEQUIVALENCE OF IANOV SCHEMES is NP-complete.** Source: Garey and Johnson
(1979), [PO16]; Constable, Hunt and Sahni (1980); Rutledge (1964). -/
public theorem_wanted strongInequivalenceOfIanovSchemes_npComplete :
    strongInequivalenceOfIanovSchemesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L strongInequivalenceOfIanovSchemesDec

end MetaMathlibExt.Complexity.NPComplete.StrongInequivalenceOfIanovSchemes
