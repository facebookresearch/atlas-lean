/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRONG INEQUIVALENCE OF IANOV SCHEMES (loop-free, trivial `P₂`) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO16] STRONG INEQUIVALENCE OF
IANOV SCHEMES, p. 276 (comment: remains NP-complete even if neither program contains any
loops and `P₂` is the trivial program that leaves the value of `x` unchanged; references
[Constable, Hunt, and Sahni, 1974] and [Rutledge, 1964]);
R. L. Constable, H. B. Hunt III and S. Sahni, "On the computational complexity of program
scheme equivalence", SIAM Journal on Computing 9 (1980), 396-416, doi:10.1137/0209031
(journal version of the 1974 Cornell report GJ cites: strong equivalence of single variable
program schemes is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.StrongInequivalenceOfIanovSchemesLoopFreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StrongInequivalenceOfIanovSchemesLoopFree

/-!
# STRONG INEQUIVALENCE OF IANOV SCHEMES (loop-free, trivial `P₂`) is NP-complete

INSTANCE: finite sets `F` and `P` of function and predicate symbols, a single variable `x`,
and two Ianov schemes over `F`, `P` and `x`, each a sequence `I₁, I₂, …, Iₘ` of instructions
of the form `x ← f(x)`, `if p(x) then goto Iⱼ else goto Iₖ`, and `halt`, where `f ∈ F` and
`p ∈ P`; neither program contains any loops, and `P₂` is the trivial program that leaves the
value of `x` unchanged.
QUESTION: are the two given Ianov schemes not strongly equivalent, i.e., is there a domain
set `D`, an interpretation of each `f ∈ F` as a function `f : D → D`, an interpretation of
each `p ∈ P` as a function `p : D → {T, F}`, and an initial value `x₀ ∈ D` for `x`, such that
either both schemes halt with different final values for `x` or one halts and the other
doesn't?

This is the restriction of `WantedExt.Complexity.NPComplete.StrongInequivalenceOfIanovSchemesWanted`
named in the source's comment. The instance type, the scheme encoding and semantics, the
parent well-formedness condition and the question are that module's
(`StrongInequivalenceOfIanovSchemes.StrongInequivalenceOfIanovSchemesInstance`,
`StrongInequivalenceOfIanovSchemes.WellFormed`,
`StrongInequivalenceOfIanovSchemes.StrongInequivalenceOfIanovSchemesFeasible`); the
restriction is added to `WellFormed`:

* a scheme contains no loop when its control-flow relation `Next` (from an assignment `Iᶜ`
  to `I_{c+1}`, from a test to both of its jump targets) has no cycle;
* the trivial program that leaves `x` unchanged is the one-instruction scheme `halt`,
  `[(2, 0, 0, 0)]`, which has no loop either.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **STRONG INEQUIVALENCE OF IANOV SCHEMES is NP-complete for a loop-free scheme and the
trivial scheme.** Source: Garey and Johnson (1979), [PO16]; Constable, Hunt and Sahni
(1980). -/
public theorem_wanted strongInequivalenceOfIanovSchemesLoopFree_npComplete :
    strongInequivalenceOfIanovSchemesLoopFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L strongInequivalenceOfIanovSchemesLoopFreeDec

end MetaMathlibExt.Complexity.NPComplete.StrongInequivalenceOfIanovSchemesLoopFree
