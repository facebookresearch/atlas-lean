/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INEQUIVALENCE OF SIMPLE FUNCTIONS in terms of `w` only is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO15] INEQUIVALENCE OF
SIMPLE FUNCTIONS, p. 276 (comment: remains NP-complete even if `f` and `g` are defined only in
terms of `w(x, y)` [Lieberherr, 1977]; Garey and Johnson list [Lieberherr, 1977] as a private
communication, which was not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsWOnly

/-!
# INEQUIVALENCE OF SIMPLE FUNCTIONS in terms of `w` only is NP-complete

INSTANCE: a finite set `X` of variables, and two expressions `f` and `g` over `X`, each a
composition of the function `w(x, y) = if y = 0 then x else 0` only, where the leaves `x, y`
are variables of `X`.
QUESTION: is there an assignment of non-negative integer values to the variables in `X` for
which the values of `f` and `g` differ?

This is the restriction of [PO15] INEQUIVALENCE OF SIMPLE FUNCTIONS
(`WantedExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsWanted`) in which `f` and `g`
use no function other than `w`. The instance type, the expressions `SimpleExpr`, their
evaluation, their prefix token lists, the base well-formedness and the question are those of
the parent, reused unchanged; this module adds only the restriction to `WellFormed`: every token
of `f` and `g` is a variable `(0, k, 0)` or the operator `w`, `(6, 0, 0)`. As in the parent, a
bare variable is also an expression; this adds nothing, since `x = w(x, w(y, y))` for every
variable `y`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance, as in `InequivalenceOfSimpleFunctionsWanted`: the number `|X|` of variables,
and the prefix token lists of `f` and `g`. -/
abbrev InequivalenceOfSimpleFunctionsWOnlyInstance :=
  InequivalenceOfSimpleFunctions.InequivalenceOfSimpleFunctionsInstance

/-- Well-formedness of an instance: the instance of INEQUIVALENCE OF SIMPLE FUNCTIONS is
well-formed, and every token of `f` and `g` is a variable or the operator `w`. -/
def WellFormed (i : InequivalenceOfSimpleFunctionsWOnlyInstance) : Prop :=
  InequivalenceOfSimpleFunctions.WellFormed i ∧ ∀ t ∈ i.2.1 ++ i.2.2, t.1 = 0 ∨ t.1 = 6

/-- Some assignment of non-negative integers to the variables gives `f` and `g` different
values, exactly as in `InequivalenceOfSimpleFunctionsWanted`. -/
def InequivalenceOfSimpleFunctionsWOnlyFeasible
    (i : InequivalenceOfSimpleFunctionsWOnlyInstance) : Prop :=
  InequivalenceOfSimpleFunctions.InequivalenceOfSimpleFunctionsFeasible i

open Classical in
/-- INEQUIVALENCE OF SIMPLE FUNCTIONS in terms of `w` only as a decision problem over
bitstrings. -/
noncomputable def inequivalenceOfSimpleFunctionsWOnlyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InequivalenceOfSimpleFunctionsWOnlyInstance) x with
  | some i => decide (WellFormed i ∧ InequivalenceOfSimpleFunctionsWOnlyFeasible i)
  | none => false

/-- **INEQUIVALENCE OF SIMPLE FUNCTIONS in terms of `w` only is NP-complete.** Source: Garey
and Johnson (1979), [PO15]; Lieberherr (1977). -/
public theorem_wanted inequivalenceOfSimpleFunctionsWOnly_npComplete :
    inequivalenceOfSimpleFunctionsWOnlyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inequivalenceOfSimpleFunctionsWOnlyDec

end MetaMathlibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsWOnly
