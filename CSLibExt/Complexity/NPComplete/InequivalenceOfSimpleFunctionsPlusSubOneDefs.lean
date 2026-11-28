/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INEQUIVALENCE OF SIMPLE FUNCTIONS in terms of `plus` and `sub1`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO15] INEQUIVALENCE OF
SIMPLE FUNCTIONS, p. 276 (comment: the variant in which `f` and `g` are defined in terms of
`plus` and `sub1(x) = max {0, 1 - x}`, where `x, y ∈ X ∪ Z⁺`, is also NP-complete
[Constable, Hunt, and Sahni, 1974]);
R. L. Constable, H. B. Hunt III and S. Sahni, "On the computational complexity of scheme
equivalence", Report No. 74-201, Department of Computer Science, Cornell University (1974),
as cited by Garey and Johnson (the report itself was not available); journal version:
R. L. Constable, H. B. Hunt III and S. Sahni, "On the computational complexity of program
scheme equivalence", SIAM Journal on Computing 9 (1980), 396-416, doi:10.1137/0209031.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsPlusSubOne

/-- Expressions over `plus` and `sub1`, with variables `xₖ` and constants at the leaves. -/
inductive PlusSubOneExpr where
  /-- The variable `xₖ`. -/
  | var (k : ℕ)
  /-- The constant `c`. -/
  | const (c : ℕ)
  /-- `plus(e, e') = e + e'`. -/
  | plus (e e' : PlusSubOneExpr)
  /-- `sub1(e) = max {0, 1 - e}`. -/
  | sub1 (e : PlusSubOneExpr)

/-- The value of an expression under the assignment `a` of non-negative integers to the
variables (`a k` is the value of `xₖ`). -/
def PlusSubOneExpr.eval (a : ℕ → ℕ) : PlusSubOneExpr → ℕ
  | .var k => a k
  | .const c => c
  | .plus e e' => e.eval a + e'.eval a
  | .sub1 e => 1 - e.eval a

/-- The prefix token list of an expression (see the module docstring). -/
def PlusSubOneExpr.tokens : PlusSubOneExpr → List (ℕ × ℕ)
  | .var k => [(0, k)]
  | .const c => [(1, c)]
  | .plus e e' => (2, 0) :: (e.tokens ++ e'.tokens)
  | .sub1 e => (3, 0) :: e.tokens

/-- An instance: the number `|X|` of variables, and the prefix token lists of `f` and `g`. -/
abbrev InequivalenceOfSimpleFunctionsPlusSubOneInstance :=
  ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)

/-- A token list is the prefix token list of an expression whose variables are among
`x₀, …, x_{nX-1}` and whose constants are positive integers. -/
def IsExpr (nX : ℕ) (ts : List (ℕ × ℕ)) : Prop :=
  (∃ e : PlusSubOneExpr, e.tokens = ts) ∧
    ∀ t ∈ ts, (t.1 = 0 → t.2 < nX) ∧ (t.1 = 1 → 0 < t.2)

/-- Well-formedness of an instance: both token lists are expressions over `X ∪ Z⁺`
(`IsExpr`). -/
def WellFormed (i : InequivalenceOfSimpleFunctionsPlusSubOneInstance) : Prop :=
  IsExpr i.1 i.2.1 ∧ IsExpr i.1 i.2.2

/-- Some assignment of non-negative integers to the variables gives `f` and `g` different
values. -/
def InequivalenceOfSimpleFunctionsPlusSubOneFeasible
    (i : InequivalenceOfSimpleFunctionsPlusSubOneInstance) : Prop :=
  ∃ f g : PlusSubOneExpr, f.tokens = i.2.1 ∧ g.tokens = i.2.2 ∧
    ∃ a : ℕ → ℕ, f.eval a ≠ g.eval a

open Classical in
/-- INEQUIVALENCE OF SIMPLE FUNCTIONS in terms of `plus` and `sub1` as a decision problem over
bitstrings. -/
noncomputable def inequivalenceOfSimpleFunctionsPlusSubOneDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InequivalenceOfSimpleFunctionsPlusSubOneInstance) x with
  | some i => decide (WellFormed i ∧ InequivalenceOfSimpleFunctionsPlusSubOneFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsPlusSubOne
