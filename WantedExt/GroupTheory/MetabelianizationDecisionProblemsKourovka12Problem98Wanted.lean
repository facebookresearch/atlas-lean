/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Word and conjugacy problems for `F/R` and `F/[R, R]` (Kourovka Notebook Problem 12.98)

Kourovka Notebook, Archive of Solved Problems, Problem 12.98 (V. E. Shpil'rain): let `F` be a free
group of finite rank and `R` a recursively defined normal subgroup. Is it true that (a) the word
problem for `F/R` is soluble if and only if it is soluble for `F/[R, R]`; (b) the conjugacy problem
for `F/R` is soluble if and only if it is soluble for `F/[R, R]`; (c) the conjugacy problem for
`F/[R, R]` is soluble if the word problem is soluble for `F/[R, R]`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.MetabelianizationDecisionProblemsKourovka12Problem98Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.98 (V. E.
Shpil'rain). UnsolvedMath record UM-00700915 (`KOU-12.98`), dataset ulamai/UnsolvedMath v1.8.0.

Words over `F = F(x₀, …, x_{n-1})` are coded as `List (Fin n × Bool)`, as in
`WordProblemSolvableShared`. A recursively defined normal subgroup is a recursively enumerable one
(so `F ⧸ R` is recursively presented). The word problem for `F ⧸ N` is decidability of membership in
`N`; the conjugacy problem is decidability of `∃ u, u w u⁻¹ v⁻¹ ∈ N`, which is conjugacy in `F ⧸ N`
for normal `N`.
-/

/-- The normal subgroup `N` of `F = F(x₀, …, x_{n-1})` is recursively enumerable (words coded as
`List (Fin n × Bool)`). -/
def IsRecursivelyEnumerable {n : ℕ} (N : Subgroup (FreeGroup (Fin n))) : Prop :=
  REPred fun w : List (Fin n × Bool) => FreeGroup.mk w ∈ N

/-- The word problem for `F ⧸ N` is solvable: membership of words in `N` is decidable. -/
def WordProblemSolvable {n : ℕ} (N : Subgroup (FreeGroup (Fin n))) : Prop :=
  ComputablePred fun w : List (Fin n × Bool) => FreeGroup.mk w ∈ N

/-- The conjugacy problem for `F ⧸ N` (`N` normal) is solvable: it is decidable whether two words
are conjugate modulo `N`. -/
def ConjugacyProblemSolvable {n : ℕ} (N : Subgroup (FreeGroup (Fin n))) : Prop :=
  ComputablePred fun wv : List (Fin n × Bool) × List (Fin n × Bool) =>
    ∃ u : FreeGroup (Fin n), u * FreeGroup.mk wv.1 * u⁻¹ * (FreeGroup.mk wv.2)⁻¹ ∈ N

/-- Kourovka 12.98(a) (V. E. Shpil'rain): for a free group `F` of finite rank and a recursively
enumerable normal subgroup `R`, the word problem for `F ⧸ R` is solvable if and only if it is
solvable for `F ⧸ [R, R]`. -/
def wordProblemIffMetabelianization : Prop :=
  ∀ (n : ℕ) (R : Subgroup (FreeGroup (Fin n))), R.Normal → IsRecursivelyEnumerable R →
    (WordProblemSolvable R ↔ WordProblemSolvable ⁅R, R⁆)

/-- Kourovka 12.98(b): the conjugacy problem for `F ⧸ R` is solvable if and only if it is solvable
for `F ⧸ [R, R]`. -/
def conjugacyProblemIffMetabelianization : Prop :=
  ∀ (n : ℕ) (R : Subgroup (FreeGroup (Fin n))), R.Normal → IsRecursivelyEnumerable R →
    (ConjugacyProblemSolvable R ↔ ConjugacyProblemSolvable ⁅R, R⁆)

/-- Kourovka 12.98(c): if the word problem for `F ⧸ [R, R]` is solvable, so is its conjugacy
problem. -/
def metabelianizationWordProblemSolvesConjugacy : Prop :=
  ∀ (n : ℕ) (R : Subgroup (FreeGroup (Fin n))), R.Normal → IsRecursivelyEnumerable R →
    WordProblemSolvable ⁅R, R⁆ → ConjugacyProblemSolvable ⁅R, R⁆

/--
Resolved true: the Kourovka Archive answers 12.98(a) "Yes, it is" (M. I. Anokhin, 1997). Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.98 (V. E. Shpil'rain);
resolution: M. I. Anokhin, Math. Notes 61 (1997), no. 1-2, 3-8, Kourovka Archive, Problem 12.98: a)
Yes, it is; b) No, it is not; c) No, it is not.
-/
public theorem_wanted wordProblemIffMetabelianization_holds : wordProblemIffMetabelianization

/--
Resolved false: the Kourovka Archive answers 12.98(b) "No, it is not" (M. I. Anokhin, 1997). Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.98 (V. E. Shpil'rain);
resolution: M. I. Anokhin, Math. Notes 61 (1997), no. 1-2, 3-8, Kourovka Archive, Problem 12.98: a)
Yes, it is; b) No, it is not; c) No, it is not.
-/
public theorem_wanted conjugacyProblemIffMetabelianization_refuted :
    ¬ conjugacyProblemIffMetabelianization

/--
Resolved false: the Kourovka Archive answers 12.98(c) "No, it is not" (M. I. Anokhin, 1997). Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.98 (V. E. Shpil'rain);
resolution: M. I. Anokhin, Math. Notes 61 (1997), no. 1-2, 3-8, Kourovka Archive, Problem 12.98: a)
Yes, it is; b) No, it is not; c) No, it is not.
-/
public theorem_wanted metabelianizationWordProblemSolvesConjugacy_refuted :
    ¬ metabelianizationWordProblemSolvesConjugacy

end MathlibExt.GroupTheory.MetabelianizationDecisionProblemsKourovka12Problem98Wanted
