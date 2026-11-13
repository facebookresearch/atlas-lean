/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# No-3-way-interaction MLE and 2 × 2 × 2 collapsings (AIM list, Conjecture 8)

AIM workshop Computational algebraic statistics, problem list, Conjecture 8: maximum likelihood
estimates for an `I × J × K` table under the no 3-way interaction model do not exist if and only if
they do not exist for all collapsings of the table to a `2 × 2 × 2` table. The list adds: later in
the week, Nicholas Eriksson showed that this conjecture is false already for `3 × 3 × 3` tables.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MathlibExt.Probability.NoThreeWayMLECollapsingAIMComputationProblem22Wanted

/-!
Source: AIM workshop Computational algebraic statistics, problem list, Conjecture 8. UnsolvedMath
record UM-20001184 (`AIM-COMPUTATION-0022`), dataset ulamai/UnsolvedMath v1.8.0.

'Do not exist for all collapsings' is read as 'do not exist for every collapsing to exist', i.e. the
MLE fails to exist for some collapsing (the detection reading): this is the reading for which the
list's note says the conjecture first fails at `3 × 3 × 3` (for `2 × q × r` tables every facet of
the marginal cone comes from a binary collapsing, Eriksson–Fienberg–Rinaldo–Sullivant Prop. 12), and
the direction 'some collapsing has no MLE ⇒ the table has none' holds for all tables. The MLE (with
strictly positive cell probabilities, as the list requires) exists iff the observed two-way margins
lie in the relative interior of the marginal cone, iff some strictly positive real table has the
same two-way margins (Haberman's theorem as stated by Eriksson–Fienberg–Rinaldo–Sullivant, Cor. 3
and its proof); `MLEExists` is this criterion. A collapsing to `2 × 2 × 2` merges the levels of each
variable into two nonempty classes (surjections onto `Fin 2`) and sums the merged cells. The target
is the conjecture for `3 × 3 × 3` tables, the size the list names.
-/

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
public theorem_wanted mleNonexistenceDetectedByCollapsing333_refuted :
    ¬ mleNonexistenceDetectedByCollapsing333

end MathlibExt.Probability.NoThreeWayMLECollapsingAIMComputationProblem22Wanted
