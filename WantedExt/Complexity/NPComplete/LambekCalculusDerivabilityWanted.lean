/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LAMBEK CALCULUS DERIVABILITY is NP-complete

Source:
M. Pentus, "Lambek calculus is NP-complete", Theoretical Computer Science 357 (2006), 186-201,
doi:10.1016/j.tcs.2006.03.018.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LambekCalculusDerivabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LambekCalculusDerivability

/-!
# LAMBEK CALCULUS DERIVABILITY is NP-complete

INSTANCE: a sequent `Γ → A` of the Lambek calculus `L`, where `Γ` is a finite sequence of types
and `A` is a type, types being built from primitive types `p₀, p₁, …` with the binary
connectives `·` (product), `/` and `\`. QUESTION: is `Γ → A` derivable in `L`?

Pentus (Section 1) defines the Lambek calculus allowing empty premises `L*` by the axioms
`A → A` and the rules (CUT), `(→/)`, `(/→)`, `(→\)`, `(\→)`, `(→·)` and `(·→)`, and `L`, Lambek's
original syntactic calculus, as the same calculus in which `(→\)` and `(→/)` require their
premise context `Π` to be nonempty. He proves that the derivability problem is NP-complete for
both `L` and `L*` (abstract). This module states the result for `L`. `Derivable` is Pentus's
calculus for `L`, rule for rule, with the cut rule included as in the source (the
cut-elimination theorem holds for `L`, so the derivable sequents are the same without it).

A type is written in postfix (reverse Polish) notation as a list of tokens: `0` is `·`, `1` is
`/` and `2` is `\` (binary, applied to the two most recent subtypes in their written order, so
`B A 1` is `B / A` and `A B 2` is `A \ B`), and `k + 3` is the primitive type `pₖ`. `parse`
reads the tokens with a stack into `LType`. The sequent is a list of token lists for the types of
`Γ`, in order, and a token list for `A`; it is well formed when every token list is a type.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LAMBEK CALCULUS DERIVABILITY is NP-complete.** Source: Pentus (2006). -/
public theorem_wanted lambekCalculusDerivability_npComplete :
    lambekCalculusDerivabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L lambekCalculusDerivabilityDec

end MetaMathlibExt.Complexity.NPComplete.LambekCalculusDerivability
