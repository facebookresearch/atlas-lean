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
public import MathlibExt.GroupTheory.MetabelianizationDecisionProblemsKourovka12Problem98

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
for normal `N`. The decision-problem definitions and the proof of part (a) are in
`MathlibExt.GroupTheory.MetabelianizationDecisionProblemsKourovka12Problem98`.
-/

/-- **Kourovka Problem 12.98(b) (V. E. Shpil'rain).** The statement that for every natural
number $n$ and every recursively enumerable normal subgroup $R$ of the free group $F$ on $n$
generators, with commutator subgroup $[R, R]$, the conjugacy problem for $F / R$ is solvable if and
only if the conjugacy problem for $F / [R, R]$ is solvable. -/
def conjugacyProblemIffMetabelianization : Prop :=
  ∀ (n : ℕ) (R : Subgroup (FreeGroup (Fin n))), R.Normal → IsRecursivelyEnumerable R →
    (ConjugacyProblemSolvable R ↔ ConjugacyProblemSolvable ⁅R, R⁆)

/-- **Kourovka Problem 12.98(c) (V. E. Shpil'rain).** The statement that for every natural
number $n$ and every recursively enumerable normal subgroup $R$ of the free group $F$ on $n$
generators, with commutator subgroup $[R, R]$, if the word problem for $F / [R, R]$ is solvable
then the conjugacy problem for $F / [R, R]$ is solvable. -/
def metabelianizationWordProblemSolvesConjugacy : Prop :=
  ∀ (n : ℕ) (R : Subgroup (FreeGroup (Fin n))), R.Normal → IsRecursivelyEnumerable R →
    WordProblemSolvable ⁅R, R⁆ → ConjugacyProblemSolvable ⁅R, R⁆

/--
**Kourovka 12.98(b) has a negative answer.** It is not the case that for every natural number $n$
and every recursively enumerable normal subgroup $R$ of the free group $F$ on $n$ generators, with
commutator subgroup $[R, R]$, the conjugacy problem for $F / R$ is solvable if and only if the
conjugacy problem for $F / [R, R]$ is solvable: for some such $n$ and $R$, exactly one of these two
conjugacy problems is solvable.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.98 (V. E.
Shpil'rain); resolution: M. I. Anokhin, Math. Notes 61 (1997), no. 1-2, 3-8, Kourovka Archive,
Problem 12.98: a) Yes, it is; b) No, it is not; c) No, it is not.
-/
public theorem_wanted conjugacyProblemIffMetabelianization_refuted :
    ¬ conjugacyProblemIffMetabelianization

/--
**Kourovka 12.98(c) has a negative answer.** It is not the case that for every natural number $n$
and every recursively enumerable normal subgroup $R$ of the free group $F$ on $n$ generators, with
commutator subgroup $[R, R]$, solvability of the word problem for $F / [R, R]$ implies solvability
of the conjugacy problem for $F / [R, R]$: for some such $n$ and $R$, the word problem for
$F / [R, R]$ is solvable but its conjugacy problem is not.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.98 (V. E.
Shpil'rain); resolution: M. I. Anokhin, Math. Notes 61 (1997), no. 1-2, 3-8, Kourovka Archive,
Problem 12.98: a) Yes, it is; b) No, it is not; c) No, it is not.
-/
public theorem_wanted metabelianizationWordProblemSolvesConjugacy_refuted :
    ¬ metabelianizationWordProblemSolvesConjugacy

end MathlibExt.GroupTheory.MetabelianizationDecisionProblemsKourovka12Problem98Wanted
