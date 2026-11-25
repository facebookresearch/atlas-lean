/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BREAKPOINT MEDIAN is NP-complete

Source:
I. Pe'er and R. Shamir, "The median problems for breakpoints are NP-complete", Electronic
Colloquium on Computational Complexity, Report TR98-071 (1998) (Section 2, the signed median
problem and breakpoints; Corollary 4.9: the signed permutations median problem is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ExemplarBreakpointDistanceWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BreakpointMedian

open MetaMathlibExt.Complexity.NPComplete.ExemplarBreakpointDistance (breakpointDistance)

/-!
# BREAKPOINT MEDIAN is NP-complete

INSTANCE: three signed permutations `π₀, π₁, π₂` on `n` elements and an integer `k`.
QUESTION: is there a signed permutation `π̂` on `n` elements with
`bp(π₀, π̂) + bp(π₁, π̂) + bp(π₂, π̂) ≤ k`?

Definitions of Pe'er and Shamir (Section 2). A signed permutation on `n` elements is an
`n`-tuple `(π(1), …, π(n))` with `π(i) ∈ {±1, …, ±n}` and `|π(i)| ≠ |π(j)|` for `i ≠ j`. Its
standard augmentation is the unsigned permutation on `0, …, 2n + 1` obtained by replacing `+i`
by `2i - 1, 2i` and `-i` by `2i, 2i - 1`, and adding `0` in front and `2n + 1` at the end; the
pairs at positions `2j, 2j + 1` (`0 ≤ j ≤ n`) of the augmentation are the successive pairs of
the signed permutation. A successive pair of `π` that is not a successive pair of `σ` is a
breakpoint, and `bp(π, σ)` is the number of breakpoints of `π` with respect to `σ`.

A signed element is a pair `(a, s)` of an absolute value `a : ℕ` and a sign `s : Bool` (`true`
for `+`); a signed permutation on `n` elements is a list of signed elements whose absolute values
form a permutation of `1, …, n`. The number `n` is the length of `π₀`. The breakpoint count is
the breakpoint distance `ExemplarBreakpointDistance.breakpointDistance` of
`WantedExt.Complexity.NPComplete.ExemplarBreakpointDistanceWanted` (Sankoff's definition, as
used by Bryant), which agrees with Pe'er and Shamir's count on signed permutations of the same
elements: the successive pair between consecutive elements `a b` of `π` is `{tail(a), head(b)}`,
and it is a successive pair of `σ` exactly when `a b` or `-b -a` are consecutive in `σ`; the pair
containing `0` (resp. `2n + 1`) is a successive pair of `σ` exactly when `π` and `σ` have the
same first (resp. last) signed element. `k` uses the canonical binary encoding.

Pe'er and Shamir prove the signed median problem NP-complete already for three permutations
(Corollary 4.9) and extend the hardness to unsigned permutations (Theorem 5.1).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **BREAKPOINT MEDIAN is NP-complete.** Source: Pe'er and Shamir (1998), Corollary 4.9. -/
public theorem_wanted breakpointMedian_npComplete :
    breakpointMedianDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L breakpointMedianDec

end MetaMathlibExt.Complexity.NPComplete.BreakpointMedian
