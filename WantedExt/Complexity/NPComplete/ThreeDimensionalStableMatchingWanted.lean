/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-DIMENSIONAL STABLE MATCHING is NP-complete

Source:
C. Ng and D. S. Hirschberg, "Three-dimensional stable matching problems", SIAM Journal on
Discrete Mathematics 4 (1991), 245-252, doi:10.1137/0404023;
problem definition as restated by R. Ostrovsky and W. Rosenbaum, "It's not easy being three:
the approximability of three-dimensional stable matching problems", arXiv:1412.1130 (2014),
Section 2.1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Batteries.Data.List.Basic
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalStableMatching

/-!
# THREE-DIMENSIONAL STABLE MATCHING is NP-complete

The three-gender stable marriage problem (3GSM). INSTANCE: three disjoint sets `A` (women),
`B` (men) and `D` (dogs) with `|A| = |B| = |D| = n`; every woman `a ∈ A` has a strict total
order over the pairs `B × D`, every man over `A × D`, and every dog over `A × B`. A family is a
triple `abd` with `a ∈ A`, `b ∈ B`, `d ∈ D`; a marriage is a set of `n` pairwise disjoint
families, so that every agent lies in exactly one family. A triple `abd` is unstable for a
marriage `M` if `a`, `b` and `d` each strictly prefer the triple `abd` to their assigned family
in `M`: `a` prefers `bd` to its partners in `M`, `b` prefers `ad` to its partners, and `d`
prefers `ab` to its partners. QUESTION: is there a stable marriage, i.e., a marriage with no
unstable triple?

The agents of each gender are `0, ..., n - 1`. An agent's preference is the list of all `n²`
pairs of agents of the other two genders, each exactly once, from most to least preferred, so
`x` is preferred to `y` when `x` occurs before `y`. A marriage is given by two bijections
`μ ν : Fin n ≃ Fin n`: woman `a` is in the family `(a, μ a, ν a)`. Then man `b` is in the family
of woman `μ⁻¹ b` and dog `d` in the family of woman `ν⁻¹ d`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of agents of each gender, then the preference lists of the
women (over man-dog pairs `(b, d)`), of the men (over woman-dog pairs `(a, d)`), and of the dogs
(over woman-man pairs `(a, b)`), the `k`-th list being agent `k`'s. -/
abbrev ThreeDimensionalStableMatchingInstance :=
  ℕ × List (List (ℕ × ℕ)) × List (List (ℕ × ℕ)) × List (List (ℕ × ℕ))

/-- A preference list ranks every pair `(x, y)` with `x, y < n` exactly once. -/
def IsRanking (n : ℕ) (r : List (ℕ × ℕ)) : Prop :=
  r.Perm (List.product (List.range n) (List.range n))

/-- Under the preference list `r`, the pair `x` is strictly preferred to the pair `y`. -/
def Prefers (r : List (ℕ × ℕ)) (x y : ℕ × ℕ) : Prop :=
  r.idxOf x < r.idxOf y

/-- Well-formedness of an instance: each gender has `n` preference lists, and every preference
list ranks all `n²` pairs of the other two genders exactly once. -/
def WellFormed (i : ThreeDimensionalStableMatchingInstance) : Prop :=
  i.2.1.length = i.1 ∧ i.2.2.1.length = i.1 ∧ i.2.2.2.length = i.1 ∧
    (∀ r ∈ i.2.1, IsRanking i.1 r) ∧ (∀ r ∈ i.2.2.1, IsRanking i.1 r) ∧
    ∀ r ∈ i.2.2.2, IsRanking i.1 r

/-- The triple `abd` is unstable for the marriage given by `μ` and `ν` (woman `a'` is in the
family `(a', μ a', ν a')`): the woman `a` prefers `(b, d)` to her partners, the man `b` prefers
`(a, d)` to his partners, and the dog `d` prefers `(a, b)` to its partners. -/
def IsUnstableTriple (i : ThreeDimensionalStableMatchingInstance) (μ ν : Fin i.1 ≃ Fin i.1)
    (a b d : Fin i.1) : Prop :=
  Prefers (i.2.1.getD a []) ((b : ℕ), (d : ℕ)) ((μ a : ℕ), (ν a : ℕ)) ∧
    Prefers (i.2.2.1.getD b []) ((a : ℕ), (d : ℕ)) ((μ.symm b : ℕ), (ν (μ.symm b) : ℕ)) ∧
    Prefers (i.2.2.2.getD d []) ((a : ℕ), (b : ℕ)) ((ν.symm d : ℕ), (μ (ν.symm d) : ℕ))

/-- Some marriage has no unstable triple. -/
def ThreeDimensionalStableMatchingFeasible (i : ThreeDimensionalStableMatchingInstance) :
    Prop :=
  ∃ μ ν : Fin i.1 ≃ Fin i.1, ∀ a b d : Fin i.1, ¬ IsUnstableTriple i μ ν a b d

open Classical in
/-- THREE-DIMENSIONAL STABLE MATCHING as a decision problem over bitstrings. -/
noncomputable def threeDimensionalStableMatchingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeDimensionalStableMatchingInstance) x with
  | some i => decide (WellFormed i ∧ ThreeDimensionalStableMatchingFeasible i)
  | none => false

/-- **THREE-DIMENSIONAL STABLE MATCHING is NP-complete.** Source: Ng and Hirschberg (1991). -/
public theorem_wanted threeDimensionalStableMatching_npComplete :
    threeDimensionalStableMatchingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeDimensionalStableMatchingDec

end MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalStableMatching
