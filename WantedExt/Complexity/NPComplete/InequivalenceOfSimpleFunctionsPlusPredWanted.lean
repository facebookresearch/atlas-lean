/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INEQUIVALENCE OF SIMPLE FUNCTIONS in terms of `plus` and `p` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO15] INEQUIVALENCE OF
SIMPLE FUNCTIONS, p. 276 (comment: remains NP-complete even if `f` and `g` are defined only in
terms of `plus` and `p` [Lieberherr, 1977]; Garey and Johnson list [Lieberherr, 1977] as a private
communication, which was not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsPlusPredDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsPlusPred

/-!
# INEQUIVALENCE OF SIMPLE FUNCTIONS in terms of `plus` and `p` is NP-complete

INSTANCE: a finite set `X` of variables, and two expressions `f` and `g` over `X`, each a
composition of the functions `plus(x, y) = x + y` and `p(x) = max {x - 1, 0}` only, where the
leaves `x, y` are variables of `X`.
QUESTION: is there an assignment of non-negative integer values to the variables in `X` for
which the values of `f` and `g` differ?

This is the restriction of [PO15] INEQUIVALENCE OF SIMPLE FUNCTIONS
(`WantedExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsWanted`) in which `f` and `g`
use no functions other than `plus` and `p`. The instance type, the expressions `SimpleExpr`, their
evaluation, their prefix token lists, the base well-formedness and the question are those of
the parent, reused unchanged; this module adds only the restriction to `WellFormed`: every token
of `f` and `g` is a variable `(0, k, 0)`, the operator `p`, `(2, 0, 0)`, or the operator `plus`,
`(3, 0, 0)`; `p` is truncated subtraction on `ℕ`. As in the parent, a bare variable is also
an expression. This does not change the problem: replacing `f` and `g` by `plus(f, z)` and
`plus(g, z)` for a fresh variable `z` preserves whether they differ somewhere.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INEQUIVALENCE OF SIMPLE FUNCTIONS in terms of `plus` and `p` is NP-complete.** Source: Garey
and Johnson (1979), [PO15]; Lieberherr (1977). -/
public theorem_wanted inequivalenceOfSimpleFunctionsPlusPred_npComplete :
    inequivalenceOfSimpleFunctionsPlusPredDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inequivalenceOfSimpleFunctionsPlusPredDec

end MetaMathlibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsPlusPred
