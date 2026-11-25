/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INEQUIVALENCE OF SIMPLE FUNCTIONS in terms of `plus` and `mod` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO15] INEQUIVALENCE OF
SIMPLE FUNCTIONS, p. 276 (comment: remains NP-complete even if `f` and `g` are defined only in
terms of `plus` and `mod` [Lieberherr, 1977]; Garey and Johnson list [Lieberherr, 1977] as a private
communication, which was not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsPlusMod

/-!
# INEQUIVALENCE OF SIMPLE FUNCTIONS in terms of `plus` and `mod` is NP-complete

INSTANCE: a finite set `X` of variables, and two expressions `f` and `g` over `X`, each a
composition of the functions `plus(x, y) = x + y` and `mod(x, t) = x - t · ⌊x / t⌋` only, where
the leaves `x, y` are variables of `X` and `t` is a positive integer.
QUESTION: is there an assignment of non-negative integer values to the variables in `X` for
which the values of `f` and `g` differ?

This is the restriction of [PO15] INEQUIVALENCE OF SIMPLE FUNCTIONS
(`WantedExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsWanted`) in which `f` and `g`
use no functions other than `plus` and `mod`. The instance type, the expressions `SimpleExpr`, their
evaluation, their prefix token lists, the base well-formedness and the question are those of
the parent, reused unchanged; this module adds only the restriction to `WellFormed`: every token
of `f` and `g` is a variable `(0, k, 0)`, the operator `plus`, `(3, 0, 0)`, or an operator
`mod(·, t)`, `(5, t, 0)` (with `0 < t` by the parent's well-formedness). As in the parent, a
bare variable is also an expression; this adds nothing, since `x = plus(x, mod(y, 1))` for
every variable `y`.

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
abbrev InequivalenceOfSimpleFunctionsPlusModInstance :=
  InequivalenceOfSimpleFunctions.InequivalenceOfSimpleFunctionsInstance

/-- Well-formedness of an instance: the instance of INEQUIVALENCE OF SIMPLE FUNCTIONS is
well-formed, and every token of `f` and `g` is a variable, `plus` or `mod`. -/
def WellFormed (i : InequivalenceOfSimpleFunctionsPlusModInstance) : Prop :=
  InequivalenceOfSimpleFunctions.WellFormed i ∧ ∀ t ∈ i.2.1 ++ i.2.2, t.1 = 0 ∨ t.1 = 3 ∨ t.1 = 5

/-- Some assignment of non-negative integers to the variables gives `f` and `g` different
values, exactly as in `InequivalenceOfSimpleFunctionsWanted`. -/
def InequivalenceOfSimpleFunctionsPlusModFeasible
    (i : InequivalenceOfSimpleFunctionsPlusModInstance) : Prop :=
  InequivalenceOfSimpleFunctions.InequivalenceOfSimpleFunctionsFeasible i

open Classical in
/-- INEQUIVALENCE OF SIMPLE FUNCTIONS in terms of `plus` and `mod` as a decision problem over
bitstrings. -/
noncomputable def inequivalenceOfSimpleFunctionsPlusModDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InequivalenceOfSimpleFunctionsPlusModInstance) x with
  | some i => decide (WellFormed i ∧ InequivalenceOfSimpleFunctionsPlusModFeasible i)
  | none => false

/-- **INEQUIVALENCE OF SIMPLE FUNCTIONS in terms of `plus` and `mod` is NP-complete.** Source: Garey
and Johnson (1979), [PO15]; Lieberherr (1977). -/
public theorem_wanted inequivalenceOfSimpleFunctionsPlusMod_npComplete :
    inequivalenceOfSimpleFunctionsPlusModDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inequivalenceOfSimpleFunctionsPlusModDec

end MetaMathlibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsPlusMod
