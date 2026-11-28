/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES (identity versus right linear) is: definitions
# NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO17] STRONG INEQUIVALENCE FOR
MONADIC RECURSION SCHEMES (comment: NP-complete even if one scheme trivially sets
`f₀(x) = x` and the other is right linear);
R. L. Constable, H. B. Hunt III and S. Sahni, "On the computational complexity of program scheme
equivalence", SIAM Journal on Computing 9(2) (1980), 396-416, doi:10.1137/0209031.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.StrongInequivalenceForMonadicRecursionSchemesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RightLinearMonadicRecursionSchemeInequivalence

open StrongInequivalenceForMonadicRecursionSchemes
  (StrongInequivalenceForMonadicRecursionSchemesInstance
    StrongInequivalenceForMonadicRecursionSchemesFeasible)

/-- An instance, as in `StrongInequivalenceForMonadicRecursionSchemesWanted`: `|F|`, `|P|`, `|G|`,
the index `k₀` of `f₀`, and the two schemes. -/
abbrev RightLinearMonadicRecursionSchemeInequivalenceInstance :=
  StrongInequivalenceForMonadicRecursionSchemesInstance

/-- A word is right linear: a defined symbol occurs only as its rightmost character (the last
list entry). -/
def RightLinear (w : List (Bool × ℕ)) : Prop :=
  ∀ j (h : j < w.length), w[j].1 = true → j + 1 = w.length

/-- Well-formedness of an instance: the instance of STRONG INEQUIVALENCE FOR MONADIC RECURSION
SCHEMES is well-formed, the first scheme defines `f₀ x = if p x then x else x` for some
predicate `p`, and every branch of the second scheme is right linear. -/
def WellFormed (i : RightLinearMonadicRecursionSchemeInequivalenceInstance) : Prop :=
  StrongInequivalenceForMonadicRecursionSchemes.WellFormed i ∧
    (∃ j, i.2.2.2.2.1[i.2.2.2.1]? = some (j, [], [])) ∧
    ∀ d ∈ i.2.2.2.2.2, RightLinear d.2.1 ∧ RightLinear d.2.2

/-- The two schemes are strongly inequivalent, exactly as in
`StrongInequivalenceForMonadicRecursionSchemesWanted`. -/
def RightLinearMonadicRecursionSchemeInequivalenceFeasible
    (i : RightLinearMonadicRecursionSchemeInequivalenceInstance) : Prop :=
  StrongInequivalenceForMonadicRecursionSchemesFeasible i

open Classical in
/-- STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES (identity versus right linear) as a decision
problem over bitstrings. -/
noncomputable def rightLinearMonadicRecursionSchemeInequivalenceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RightLinearMonadicRecursionSchemeInequivalenceInstance) x with
  | some i => decide (WellFormed i ∧ RightLinearMonadicRecursionSchemeInequivalenceFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RightLinearMonadicRecursionSchemeInequivalence
