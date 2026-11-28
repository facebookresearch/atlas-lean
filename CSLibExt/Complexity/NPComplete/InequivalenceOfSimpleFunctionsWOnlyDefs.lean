/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INEQUIVALENCE OF SIMPLE FUNCTIONS in terms of `w` only: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO15] INEQUIVALENCE OF
SIMPLE FUNCTIONS, p. 276 (comment: remains NP-complete even if `f` and `g` are defined only in
terms of `w(x, y)` [Lieberherr, 1977]; Garey and Johnson list [Lieberherr, 1977] as a private
communication, which was not available).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsWOnly

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

end MetaMathlibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsWOnly
