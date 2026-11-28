/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST ARC-PRESERVING COMMON SUBSEQUENCE (nested, nested): definitions

Source:
G.-H. Lin, Z.-Z. Chen, T. Jiang and J. Wen, "The longest common subsequence problem for
sequences with nested arc annotations", Journal of Computer and System Sciences 65 (2002),
465-480, doi:10.1016/S0022-0000(02)00004-1;
problem definitions as in V. Yu. Popov, "Arc-preserving subsequences of arc-annotated
sequences", Acta Universitatis Sapientiae, Informatica 3 (2011), 35-47, arXiv:1104.4433.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Hom.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestArcPreservingCommonSubsequenceNested

/-- An instance: the sequence `S₁` and its arc list `P₁`, the sequence `S₂` and its arc list
`P₂`, and the bound `k`. An arc `(i₁, i₂)` joins the positions `i₁` and `i₂` (`0`-based). -/
abbrev LongestArcPreservingCommonSubsequenceNestedInstance :=
  List ℕ × List (ℕ × ℕ) × List ℕ × List (ℕ × ℕ) × ℕ

/-- `P` is a nested arc set on a sequence of length `n`: a list without repetitions of arcs
`(i₁, i₂)` with `i₁ < i₂ < n`, no two sharing an endpoint, no two crossing. -/
def IsNestedArcSet (n : ℕ) (P : List (ℕ × ℕ)) : Prop :=
  P.Nodup ∧ (∀ a ∈ P, a.1 < a.2 ∧ a.2 < n) ∧
    ∀ a ∈ P, ∀ b ∈ P,
      (a.1 ≠ b.2 ∧ a.2 ≠ b.1 ∧ (a.1 = b.1 ↔ a.2 = b.2)) ∧
        (b.1 ≤ a.1 ∧ a.1 ≤ b.2 ↔ b.1 ≤ a.2 ∧ a.2 ≤ b.2)

/-- Well-formedness of an instance: both arc sets are nested and `k` is positive. -/
def WellFormed (i : LongestArcPreservingCommonSubsequenceNestedInstance) : Prop :=
  IsNestedArcSet i.1.length i.2.1 ∧ IsNestedArcSet i.2.2.1.length i.2.2.2.1 ∧ 0 < i.2.2.2.2

/-- There is an arc-preserving common subsequence of length at least `k`: order embeddings
`f`, `g` of `Fin ℓ`, `k ≤ ℓ`, into the positions of `S₁` and `S₂` that match equal letters
and map arcs of `P₁` exactly onto arcs of `P₂`. -/
def LongestArcPreservingCommonSubsequenceNestedFeasible
    (i : LongestArcPreservingCommonSubsequenceNestedInstance) : Prop :=
  ∃ ℓ, i.2.2.2.2 ≤ ℓ ∧
    ∃ (f : Fin ℓ ↪o Fin i.1.length) (g : Fin ℓ ↪o Fin i.2.2.1.length),
      (∀ t, i.1.get (f t) = i.2.2.1.get (g t)) ∧
        ∀ t t', (((f t : ℕ), (f t' : ℕ)) ∈ i.2.1 ↔ ((g t : ℕ), (g t' : ℕ)) ∈ i.2.2.2.1)

open Classical in
/-- LAPCS(NESTED, NESTED) as a decision problem over bitstrings. -/
noncomputable def longestArcPreservingCommonSubsequenceNestedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LongestArcPreservingCommonSubsequenceNestedInstance) x with
  | some i => decide (WellFormed i ∧ LongestArcPreservingCommonSubsequenceNestedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.LongestArcPreservingCommonSubsequenceNested
