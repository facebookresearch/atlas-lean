/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIRST ORDER SUBSUMPTION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [LO18] FIRST ORDER SUBSUMPTION (reference:
[Baxter, 1976], [Baxter, 1977]; transformation from 3SAT), p. 264;
L. D. Baxter, *The Complexity of Unification*, Doctoral Thesis, Department of Computer Science,
University of Waterloo (1976);
L. D. Baxter, "The NP-completeness of subsumption", unpublished manuscript (1977).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FirstOrderSubsumptionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FirstOrderSubsumption

open FirstOrder FirstOrder.Language
open MetaMathlibExt.Complexity.NPComplete.UnificationForFinitelyPresentedAlgebras (lang tokens)

/-!
# FIRST ORDER SUBSUMPTION is NP-complete

INSTANCE: a finite set `U` of "variable symbols", a finite set `C` of "function symbols", a
collection `E = {E₁, E₂, ..., Eₘ}` of expressions over `U ∪ C`, and a collection
`F = {F₁, F₂, ..., Fₙ}` of expressions over `C`.
QUESTION: is there a substitution mapping `s` that assigns to each `u ∈ U` an expression `s(u)`
over `C` such that, if `s(Eᵢ)` denotes the result of substituting for each occurrence in `Eᵢ` of
each `u ∈ U` the corresponding expression `s(u)`, then `{s(E₁), s(E₂), ..., s(Eₘ)}` is a subset of
`{F₁, F₂, ..., Fₙ}`?

Expressions are first-order terms. The function symbols of `C` are `0, …, |C| - 1`, each with
its arity (constants have arity `0`), as in
`UnificationForFinitelyPresentedAlgebrasWanted`: `lang ar` is the first-order language whose
function symbols are the indices of the arity list `ar`. Expressions over `U ∪ C` are Mathlib's
terms `(lang ar).Term (Fin |U|)`, with variables `0, …, |U| - 1`; expressions over `C` are the
closed terms `(lang ar).Term Empty`; `s(Eᵢ)` is `Term.subst`.

Expressions are given by the prefix token lists `tokens` of that module (Mathlib's
`Term.listEncode`): `(0, u)` is the variable `u` and `(1, f)` the function symbol `f`, followed
by the tokens of its arguments. Since the arities are part of the instance, a token list
determines the expression.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FIRST ORDER SUBSUMPTION is NP-complete.** Source: Garey and Johnson (1979), [LO18];
Baxter (1976, 1977). -/
public theorem_wanted firstOrderSubsumption_npComplete :
    firstOrderSubsumptionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L firstOrderSubsumptionDec

end MetaMathlibExt.Complexity.NPComplete.FirstOrderSubsumption
