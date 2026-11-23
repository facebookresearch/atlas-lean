/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Square-root dense sets are subcomplete (Erdős Problem 344)

Erdős Problem 344: if `A ⊆ ℕ` satisfies `|A ∩ {1, …, N}| ≫ N^{1/2}` for all `N`, must `A` be
subcomplete, i.e. must `P(A) = {∑_{n ∈ B} n : B ⊆ A finite}` contain an infinite arithmetic
progression?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.NumberTheory.SqrtDenseSubcompleteErdosProblem344Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #344, https://www.erdosproblems.com/344 (status
PROVED); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial number theory
(1980), p. 54. UnsolvedMath record UM-30006831 (`EP-344`), dataset ulamai/UnsolvedMath v1.8.0.

`≫ N^{1/2}` is read as `≥ C N^{1/2}` for a suitable absolute constant `C` and all large `N`
(Folkman's conjecture as stated by Szemerédi and Vu; erdosproblems.com's definitions page: `≫` hides
an absolute constant, and dependence on a parameter would be shown by a subscript): with an
arbitrary constant the claim fails, by the example after Conjecture 1.3 of their Annals paper (the
union of the intervals `[m^{2i}/4, m^{2i}/2]` has density `Ω(n^{1/2})` and is not subcomplete;
erdosproblems.com/344 likewise records that the constant `√2` would be best possible), and `C
N^{1/2} ≤ |A ∩ [1, 1]|` is impossible for `C > 1`. Compared with the formal-conjectures statement
`ErdosProblems/344.lean` (identical reading; no code imported).
-/

open Filter

/-- `P(A)`: the sums of the finite subsets of `A`. -/
def subsetSums (A : Set ℕ) : Set ℕ :=
  {s | ∃ T : Finset ℕ, (T : Set ℕ) ⊆ A ∧ s = ∑ n ∈ T, n}

/-- Erdős Problem 344 (Folkman's conjecture), with `|A ∩ {1, …, N}| ≫ N^{1/2}` read as
`≥ C N^{1/2}` for a suitable absolute constant `C`: such a set `A` is subcomplete, i.e. `P(A)`
contains an infinite arithmetic progression. -/
def sqrtDenseSubcomplete : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ A : Set ℕ, (∀ᶠ N : ℕ in atTop, C * Real.sqrt N ≤ (A ∩ Set.Icc 1 N).ncard) →
    ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, a + i * d ∈ subsetSums A

/--
Resolved true: Szemerédi and Vu proved Folkman's conjecture that there is an absolute `C` such that
every `A` with `|A ∩ [1, N]| ≥ C N^{1/2}` for large `N` is subcomplete (the bound `(2N)^{1/2}`
remains open). erdosproblems.com/344 lists the problem as proved. Source: T. F. Bloom, Erdős
Problems, Problem #344, https://www.erdosproblems.com/344 (status PROVED); P. Erdős and R. L.
Graham, Old and new problems and results in combinatorial number theory (1980), p. 54; resolution:
E. Szemerédi and V. H. Vu, Finite and infinite arithmetic progressions in sumsets, Ann. of Math.
(2006), 1-35; E. Szemerédi and V. Vu, Long arithmetic progressions in sumsets: thresholds and
bounds, J. Amer. Math. Soc. (2006), 119-169, Annals paper, abstract and Conjecture 1.3 (Folkman:
there is c such that every increasing A with A(n) ≥ c n^{1/2} is subcomplete), confirmed there; J.
Amer. Math. Soc. paper (arXiv:math/0507539), Theorem 9.4 (the same statement, proved in the Annals
paper); erdosproblems.com/344, https://www.erdosproblems.com/344.
-/
public theorem_wanted sqrtDenseSubcomplete_holds : sqrtDenseSubcomplete

end MathlibExt.NumberTheory.SqrtDenseSubcompleteErdosProblem344Wanted
