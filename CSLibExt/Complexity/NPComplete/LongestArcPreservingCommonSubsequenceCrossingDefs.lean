/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST ARC-PRESERVING COMMON SUBSEQUENCE (crossing, crossing): definitions

Source:
P. A. Evans, "Finding common subsequences with arcs and pseudoknots", Combinatorial Pattern
Matching (CPM 1999), Lecture Notes in Computer Science 1645 (1999), 270-280,
doi:10.1007/3-540-48452-3_20 (full text not available);
G.-H. Lin, Z.-Z. Chen, T. Jiang and J. Wen, "The longest common subsequence problem for
sequences with nested arc annotations", Journal of Computer and System Sciences 65 (2002),
465-480, doi:10.1016/S0022-0000(02)00004-1;
problem definitions as in V. Yu. Popov, "Arc-preserving subsequences of arc-annotated
sequences", Acta Universitatis Sapientiae, Informatica 3 (2011), 35-47, arXiv:1104.4433.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.LongestArcPreservingCommonSubsequenceNestedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestArcPreservingCommonSubsequenceCrossing

open MetaMathlibExt.Complexity.NPComplete.LongestArcPreservingCommonSubsequenceNested
  (LongestArcPreservingCommonSubsequenceNestedInstance
    LongestArcPreservingCommonSubsequenceNestedFeasible)

/-- An instance: the sequence `S₁` and its arc list `P₁`, the sequence `S₂` and its arc list
`P₂`, and the bound `k` (the instance type of the nested problem). -/
abbrev LongestArcPreservingCommonSubsequenceCrossingInstance :=
  LongestArcPreservingCommonSubsequenceNestedInstance

/-- `P` is a crossing arc set on a sequence of length `n`: a list without repetitions of arcs
`(i₁, i₂)` with `i₁ < i₂ < n`, no two sharing an endpoint. -/
def IsCrossingArcSet (n : ℕ) (P : List (ℕ × ℕ)) : Prop :=
  P.Nodup ∧ (∀ a ∈ P, a.1 < a.2 ∧ a.2 < n) ∧
    ∀ a ∈ P, ∀ b ∈ P, a.1 ≠ b.2 ∧ a.2 ≠ b.1 ∧ (a.1 = b.1 ↔ a.2 = b.2)

/-- Well-formedness of an instance: both arc sets are crossing and `k` is positive. -/
def WellFormed (i : LongestArcPreservingCommonSubsequenceCrossingInstance) : Prop :=
  IsCrossingArcSet i.1.length i.2.1 ∧ IsCrossingArcSet i.2.2.1.length i.2.2.2.1 ∧ 0 < i.2.2.2.2

/-- There is an arc-preserving common subsequence of length at least `k` (the question of the
nested problem). -/
def LongestArcPreservingCommonSubsequenceCrossingFeasible
    (i : LongestArcPreservingCommonSubsequenceCrossingInstance) : Prop :=
  LongestArcPreservingCommonSubsequenceNestedFeasible i

open Classical in
/-- LAPCS(CROSSING, CROSSING) as a decision problem over bitstrings. -/
noncomputable def longestArcPreservingCommonSubsequenceCrossingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LongestArcPreservingCommonSubsequenceCrossingInstance) x with
  | some i => decide (WellFormed i ∧ LongestArcPreservingCommonSubsequenceCrossingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.LongestArcPreservingCommonSubsequenceCrossing
