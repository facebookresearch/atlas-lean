/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# No three-way interaction MLE and binary collapsings

This module defines MLE existence through positive tables with prescribed two-way margins,
defines binary collapsing, and refutes detection of MLE nonexistence by binary collapsing
for three levels of each variable.

Source: AIM workshop Computational algebraic statistics, problem list, Conjecture 8 and
the resolution note by Nicholas Eriksson. N. Eriksson, S. E. Fienberg, A. Rinaldo and
S. Sullivant, *Polyhedral conditions for the nonexistence of the MLE for hierarchical
log-linear models*, J. Symbolic Comput. 41 (2006), 222-233,
DOI 10.1016/j.jsc.2005.04.003, arXiv:math/0405044.
-/

@[expose] public section

namespace MathlibExt.Probability.NoThreeWayMLECollapsingAIMComputationProblem22Wanted

open Function

/-- The maximum likelihood estimate of the `I × J × K` table of counts `n` exists under the no
3-way interaction model: some table with strictly positive real cells has the same two-way margins
as `n` (Haberman's criterion: the margins lie in the relative interior of the marginal cone). -/
def MLEExists {I J K : ℕ} (n : Fin I → Fin J → Fin K → ℕ) : Prop :=
  ∃ m : Fin I → Fin J → Fin K → ℝ, (∀ i j k, 0 < m i j k) ∧
    (∀ i j, ∑ k, m i j k = ∑ k, (n i j k : ℝ)) ∧
    (∀ i k, ∑ j, m i j k = ∑ j, (n i j k : ℝ)) ∧
    ∀ j k, ∑ i, m i j k = ∑ i, (n i j k : ℝ)

/-- The collapsing of an `I × J × K` table to a `2 × 2 × 2` table along the maps `a, b, c` that
merge the levels of each variable into two classes: cell `(α, β, γ)` of the collapsed table is the
sum of the cells `(i, j, k)` with `a i = α`, `b j = β`, `c k = γ`. -/
def collapse {I J K : ℕ} (a : Fin I → Fin 2) (b : Fin J → Fin 2) (c : Fin K → Fin 2)
    (n : Fin I → Fin J → Fin K → ℕ) : Fin 2 → Fin 2 → Fin 2 → ℕ :=
  fun α β γ => ∑ i, ∑ j, ∑ k, if a i = α ∧ b j = β ∧ c k = γ then n i j k else 0

/-- Conjecture 8 of the AIM workshop list for `3 × 3 × 3` tables: the MLE of a table under the no
3-way interaction model fails to exist exactly when it fails to exist for some collapsing of the
table to a `2 × 2 × 2` table (each variable's three levels merged into two nonempty classes). -/
def mleNonexistenceDetectedByCollapsing333 : Prop :=
  ∀ n : Fin 3 → Fin 3 → Fin 3 → ℕ, ¬ MLEExists n ↔
    ∃ (a b c : Fin 3 → Fin 2), Surjective a ∧ Surjective b ∧ Surjective c ∧
      ¬ MLEExists (collapse a b c n)

private def counterexample : Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![0, 0, 1], ![0, 1, 1], ![1, 1, 1]],
    ![![1, 0, 1], ![1, 1, 1], ![1, 0, 0]],
    ![![1, 1, 1], ![0, 1, 0], ![1, 1, 0]]]

private theorem counterexample_no_mle : ¬ MLEExists counterexample := by
  rintro ⟨m, hp, hij, hik, hjk⟩
  have h₁ := hij 0 0
  have h₂ := hij 0 1
  have h₃ := hij 2 1
  have h₄ := hik 0 2
  have h₅ := hik 1 1
  have h₆ := hjk 1 1
  have h₇ := hjk 2 2
  norm_num [counterexample, Fin.sum_univ_three] at h₁ h₂ h₃ h₄ h₅ h₆ h₇
  linarith only [h₁, h₂, h₃, h₄, h₅, h₆, h₇,
    hp 0 0 0, hp 0 0 1, hp 0 1 0, hp 1 0 1, hp 1 2 1,
    hp 1 2 2, hp 2 1 0, hp 2 1 2, hp 2 2 2]

private def positiveEven (t : Fin 2 → Fin 2 → Fin 2 → ℕ) : Bool :=
  decide (0 < t 0 0 0 ∧ 0 < t 0 1 1 ∧ 0 < t 1 0 1 ∧ 0 < t 1 1 0)

private def doubledWitness (t : Fin 2 → Fin 2 → Fin 2 → ℕ)
    (i j k : Fin 2) : ℤ :=
  2 * (t i j k : ℤ) +
    if (i.val + j.val + k.val) % 2 = 0 ↔ positiveEven t then -1 else 1

private theorem collapsing_positive :
    ∀ (a b c : Fin 3 → Fin 2), Surjective a → Surjective b → Surjective c →
      ∀ i j k, 0 < doubledWitness (collapse a b c counterexample) i j k := by
  decide

private theorem collapsing_mle (a b c : Fin 3 → Fin 2)
    (ha : Surjective a) (hb : Surjective b) (hc : Surjective c) :
    MLEExists (collapse a b c counterexample) := by
  let t := collapse a b c counterexample
  change MLEExists t
  refine ⟨fun i j k => (doubledWitness t i j k : ℝ) / 2, ?_, ?_, ?_, ?_⟩
  · intro i j k
    exact div_pos (Int.cast_pos.mpr (collapsing_positive a b c ha hb hc i j k))
      (by norm_num)
  · intro i j
    fin_cases i <;> fin_cases j <;> by_cases h : positiveEven t <;>
      simp [doubledWitness, h, Fin.sum_univ_two] <;> ring
  · intro i k
    fin_cases i <;> fin_cases k <;> by_cases h : positiveEven t <;>
      simp [doubledWitness, h, Fin.sum_univ_two] <;> ring
  · intro j k
    fin_cases j <;> fin_cases k <;> by_cases h : positiveEven t <;>
      simp [doubledWitness, h, Fin.sum_univ_two] <;> ring

/--
Resolved false: some `3 × 3 × 3` table has no MLE under the no 3-way interaction model although
every collapsing of it to a `2 × 2 × 2` table has one (Eriksson, as recorded by the list; the
marginal cone of `3 × 3 × 3` tables has facets not obtained by collapsing, EFRS Table 1). Source:
AIM workshop Computational algebraic statistics, problem list, Conjecture 8; resolution: AIM
workshop Computational algebraic statistics, problem list, note after Conjecture 8 (N. Eriksson); N.
Eriksson, S. E. Fienberg, A. Rinaldo and S. Sullivant, Polyhedral conditions for the nonexistence of
the MLE for hierarchical log-linear models, J. Symbolic Comput. 41 (2006), 222-233, DOI
10.1016/j.jsc.2005.04.003, arXiv:math/0405044, list: 'Later in the week, Nicholas Eriksson showed
that this conjecture is false already for 3 × 3 × 3 tables'; EFRS §4.2 and Table 1: for p = q = r =
3 not all facets of the marginal cone are obtained by collapsing ('Collapsing' column 3 3 3; 'a
natural conjecture is that all facets are obtained by collapsing to binary tables ... not all facets
are obtained by collapsing'); Haberman's theorem and Cor. 3 with its proof: the MLE exists iff the
margins lie in the relative interior of the marginal cone, iff a strictly positive table has the
same margins, https://aimath.org/WWN/compalgstat/compalgstat.pdf.
-/
public theorem mleNonexistenceDetectedByCollapsing333_refuted :
    ¬ mleNonexistenceDetectedByCollapsing333
    := by
  intro h
  obtain ⟨a, b, c, ha, hb, hc, hn⟩ := (h counterexample).mp counterexample_no_mle
  exact hn (collapsing_mle a b c ha hb hc)

end MathlibExt.Probability.NoThreeWayMLECollapsingAIMComputationProblem22Wanted
