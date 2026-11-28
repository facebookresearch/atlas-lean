/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BREAKPOINT MEDIAN: definitions

Source:
I. Pe'er and R. Shamir, "The median problems for breakpoints are NP-complete", Electronic
Colloquium on Computational Complexity, Report TR98-071 (1998) (Section 2, the signed median
problem and breakpoints; Corollary 4.9: the signed permutations median problem is NP-complete).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ExemplarBreakpointDistanceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BreakpointMedian

open MetaMathlibExt.Complexity.NPComplete.ExemplarBreakpointDistance (breakpointDistance)

/-- An instance: the signed permutations `π₀`, `π₁`, `π₂`, lists of signed elements
`(absolute value, sign)` with `true` for `+`, and the bound `k`. -/
abbrev BreakpointMedianInstance :=
  List (ℕ × Bool) × List (ℕ × Bool) × List (ℕ × Bool) × ℕ

/-- `π` is a signed permutation on `n` elements: its absolute values are a permutation of
`1, …, n`. -/
def IsSignedPerm (n : ℕ) (π : List (ℕ × Bool)) : Prop :=
  (π.map Prod.fst).Perm (List.range' 1 n)

/-- Well-formedness of an instance: `π₀`, `π₁` and `π₂` are signed permutations on `n`
elements, where `n` is the length of `π₀`. -/
def WellFormed (i : BreakpointMedianInstance) : Prop :=
  IsSignedPerm i.1.length i.1 ∧ IsSignedPerm i.1.length i.2.1 ∧
    IsSignedPerm i.1.length i.2.2.1

/-- Some signed permutation `π̂` on `n` elements has total breakpoint distance at most `k` to
`π₀`, `π₁` and `π₂`. -/
def BreakpointMedianFeasible (i : BreakpointMedianInstance) : Prop :=
  ∃ σ : List (ℕ × Bool), IsSignedPerm i.1.length σ ∧
    breakpointDistance i.1 σ + breakpointDistance i.2.1 σ + breakpointDistance i.2.2.1 σ ≤
      i.2.2.2

open Classical in
/-- BREAKPOINT MEDIAN as a decision problem over bitstrings. -/
noncomputable def breakpointMedianDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BreakpointMedianInstance) x with
  | some i => decide (WellFormed i ∧ BreakpointMedianFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BreakpointMedian
