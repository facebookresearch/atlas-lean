/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PREDICATE LOGIC WITHOUT NEGATION, existential sentences over two constants, is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO15] PREDICATE LOGIC WITHOUT
NEGATION, p. 263, comment: remains NP-complete even if there are no universal quantifiers, no
relation symbols, and only two functions, both with dimension 0 (and hence constants);
D. Kozen, "First order predicate logic without negation is NP-complete", Report 77-307,
Department of Computer Science, Cornell University (1977); journal version: D. Kozen,
"Positive first-order logic is NP-complete", IBM Journal of Research and Development 25 (1981),
327-332, doi:10.1147/rd.254.0327.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PredicateLogicWithoutNegationExistentialConstantsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PredicateLogicWithoutNegationExistentialConstants

open FirstOrder FirstOrder.Language

/-!
# PREDICATE LOGIC WITHOUT NEGATION, existential sentences over two constants, is NP-complete

Garey and Johnson's problem: a well-formed predicate logic sentence `A` without negation over
variables `U`, function symbols `F` and relation symbols `R`, built from atomic formulas
`t₁ = t₂`, `(A ∧ B)`, `(A ∨ B)`, `∀uᵢ(A)` and `∃uᵢ(A)`, in which all variables are quantified
before they occur. QUESTION: is `A` true under all interpretations of `F` and `R`? The comment's
restriction: there are no universal quantifiers, no relation symbols, and `F` consists of two
functions of dimension `0`, i.e., two constants `c₀`, `c₁`.

The sentences are Mathlib first-order sentences (`FirstOrder.Language.Sentence`) in the language
`constantsOn (Fin 2)` (two constant symbols, no relation symbols), and "true under all
interpretations" is Mathlib's `(∅ : Theory) ⊨ᵇ A`: `A` holds in every nonempty structure for
that language, i.e., under every interpretation of `c₀`, `c₁` in every domain.

The sentence is written in prefix (Polish) notation as a list of tokens `(code, a, b)`:
`(0, a, b)` is the atomic formula `tₐ = t_b`, and `(1, _, _)`, `(2, _, _)`, `(3, _, _)` are `∧`,
`∨` (followed by their two operands) and `∃` (followed by its body). A term code is `0` for
`c₀`, `1` for `c₁`, and `j + 2` for the variable bound by the `(j + 1)`-th enclosing `∃`,
counting from the outermost one (Mathlib's de Bruijn levels); a term code with no such
quantifier makes the token list malformed, so the parsed formulas are exactly the sentences in
which every variable is quantified before it occurs. A sentence with named variables
`u₁, …, uₙ` converts to this form, and back, in polynomial time (the variable bound by the
quantifier at depth `j` is renamed `j + 2`). `parse` reads the tokens, with the token count as
recursion fuel; a token list is a sentence exactly when the whole list is read as one formula.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PREDICATE LOGIC WITHOUT NEGATION restricted to existential sentences over two constants is
NP-complete.** Source: Garey and Johnson (1979), [LO15], comment; Kozen (1977). -/
public theorem_wanted predicateLogic_npComplete :
    predicateLogicDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L predicateLogicDec

end MetaMathlibExt.Complexity.NPComplete.PredicateLogicWithoutNegationExistentialConstants
