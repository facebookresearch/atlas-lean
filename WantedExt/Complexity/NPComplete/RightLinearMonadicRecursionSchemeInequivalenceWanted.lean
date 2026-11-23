/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES (identity versus right linear) is
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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.StrongInequivalenceForMonadicRecursionSchemesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RightLinearMonadicRecursionSchemeInequivalence

open StrongInequivalenceForMonadicRecursionSchemes
  (StrongInequivalenceForMonadicRecursionSchemesInstance
    StrongInequivalenceForMonadicRecursionSchemesFeasible)

/-!
# STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES (identity versus right linear) is
# NP-complete

The restriction of STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES to pairs in which the first
scheme trivially sets `f₀(x) = x` (its defining statement for `f₀` is
`f₀ x = if p x then x else x`, both branches the empty word) and the second is right linear
(each branch word contains a defined symbol only as its rightmost character, the symbol applied
first). The question is symmetric in the two schemes, so fixing which one is the identity loses
nothing. The instance type, the base well-formedness, the semantics and the question are those
of `StrongInequivalenceForMonadicRecursionSchemesWanted`, reused unchanged; words there list their
symbols from left to right, so the rightmost character is the last list entry.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES (identity versus right linear) is
NP-complete.** Source: Garey and Johnson (1979), [PO17]; Constable, Hunt and Sahni (1980). -/
public theorem_wanted rightLinearMonadicRecursionSchemeInequivalence_npComplete :
    rightLinearMonadicRecursionSchemeInequivalenceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rightLinearMonadicRecursionSchemeInequivalenceDec

end MetaMathlibExt.Complexity.NPComplete.RightLinearMonadicRecursionSchemeInequivalence
