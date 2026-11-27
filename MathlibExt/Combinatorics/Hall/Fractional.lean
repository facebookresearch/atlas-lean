/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Real.Basic

/-!
# Hall's condition from a fractional matching

A fractional matching of a relation `related : Source → Target → Prop` between finite types is a
nonnegative real weight on related pairs. If the weights at each source sum to at least `1` and
the weights at each target to at most `1`, then the relation satisfies Hall's condition; this is
the easy half of the integrality of the bipartite matching polytope. A second lemma gives a strict
inequality between the numbers of sources and targets when the weights at the sources sum to
exactly `1` and some target carries total weight less than `1`.

## Main results

* `finiteRelationHall_of_fractionalWeights`: a source-saturating fractional matching implies
  Hall's condition.
* `finiteSubset_card_lt_of_fractionalWeights_of_target_slack`: if each source sends total weight
  `1` into `targets`, each target receives at most `1`, and one target receives less than `1`,
  then `#sources < #targets`.

## References

* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency* (2003), Chapter 18.
-/

@[expose] public section

open Finset

/-- **Fractional Hall.** If nonnegative weights supported on related pairs sum to at least `1` at
every source and to at most `1` at every target, then every finite set of sources is related to at
least as many targets. Combined with Hall's marriage theorem
(`Fintype.all_card_le_filter_rel_iff_exists_injective`), a fractional matching saturating the
sources yields an integral one (A. Schrijver, *Combinatorial Optimization*, 2003, Ch. 18). -/
theorem finiteRelationHall_of_fractionalWeights
    {Source Target : Type*}
    [Fintype Source] [Fintype Target]
    (related : Source -> Target -> Prop) [DecidableRel related]
    (weight : Source -> Target -> Real)
    (hnonneg : forall source target, 0 <= weight source target)
    (hsupport : forall source target,
      Not (related source target) -> weight source target = 0)
    (hsource : forall source, 1 <= ∑ target, weight source target)
    (htarget : forall target, ∑ source, weight source target <= 1) :
    forall sources : Finset Source,
      sources.card <=
        (Finset.univ.filter fun target =>
          ∃ source ∈ sources, related source target).card := by
  intro sources
  let targets : Finset Target :=
    Finset.univ.filter fun target =>
      ∃ source ∈ sources, related source target
  have hleft : (sources.card : Real) <=
      ∑ source ∈ sources, ∑ target, weight source target := by
    calc
      (sources.card : Real) = ∑ _source ∈ sources, (1 : Real) := by simp
      _ <= ∑ source ∈ sources, ∑ target, weight source target :=
        Finset.sum_le_sum fun source _ => hsource source
  have hrestrict :
      (∑ source ∈ sources, ∑ target, weight source target) =
        ∑ target ∈ targets, ∑ source ∈ sources,
          weight source target := by
    rw [Finset.sum_comm]
    symm
    apply Finset.sum_subset (Finset.subset_univ targets)
    intro target _ htargetNot
    have hnone : Not (∃ source ∈ sources,
        related source target) := by
      simpa [targets] using htargetNot
    apply Finset.sum_eq_zero
    intro source hsourceMem
    exact hsupport source target fun hrelated =>
      hnone ⟨source, hsourceMem, hrelated⟩
  have hright :
      (∑ target ∈ targets, ∑ source ∈ sources,
          weight source target) <= (targets.card : Real) := by
    calc
      (∑ target ∈ targets, ∑ source ∈ sources,
          weight source target) <=
          ∑ _target ∈ targets, (1 : Real) := by
        apply Finset.sum_le_sum
        intro target _
        calc
          (∑ source ∈ sources, weight source target) <=
              ∑ source, weight source target := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.subset_univ sources)
              (fun source _ _ => hnonneg source target)
          _ <= 1 := htarget target
      _ = (targets.card : Real) := by simp
  have hcardReal : (sources.card : Real) <= targets.card :=
    hleft.trans (hrestrict.trans_le hright)
  exact_mod_cast hcardReal

/-- Strict counting from a slack target: if each source in `sources` sends total weight exactly `1`
into `targets`, each target receives total weight at most `1`, and some target receives less than
`1`, then `#sources < #targets`. The weights need not be nonnegative. -/
theorem finiteSubset_card_lt_of_fractionalWeights_of_target_slack
    {Source Target : Type*}
    (weight : Source -> Target -> Real)
    (sources : Finset Source) (targets : Finset Target)
    (hsource : forall source, source ∈ sources ->
      (∑ target ∈ targets, weight source target) = 1)
    (htarget : forall target, target ∈ targets ->
      (∑ source ∈ sources, weight source target) ≤ 1)
    (slackTarget : Target) (hslackMem : slackTarget ∈ targets)
    (hslack : (∑ source ∈ sources, weight source slackTarget) < 1) :
    sources.card < targets.card := by
  classical
  let load := fun target => ∑ source ∈ sources, weight source target
  have hsourceSum : (sources.card : Real) =
      ∑ source ∈ sources, ∑ target ∈ targets, weight source target := by
    calc
      (sources.card : Real) = ∑ _source ∈ sources, (1 : Real) := by simp
      _ = ∑ source ∈ sources,
          ∑ target ∈ targets, weight source target := by
        apply Finset.sum_congr rfl
        intro source hsourceMem
        exact (hsource source hsourceMem).symm
  have hother : (∑ target ∈ targets.erase slackTarget, load target) ≤
      ((targets.erase slackTarget).card : Real) := by
    calc
      (∑ target ∈ targets.erase slackTarget, load target) ≤
          ∑ _target ∈ targets.erase slackTarget, (1 : Real) := by
        apply Finset.sum_le_sum
        intro target htargetMem
        exact htarget target (Finset.mem_of_mem_erase htargetMem)
      _ = ((targets.erase slackTarget).card : Real) := by simp
  have hloadLt : (∑ target ∈ targets, load target) <
      (targets.card : Real) := by
    have hsplit := Finset.sum_erase_add
      targets (fun target => load target) hslackMem
    have hcardNat : (targets.erase slackTarget).card + 1 = targets.card :=
      Finset.card_erase_add_one hslackMem
    have hcardReal : ((targets.erase slackTarget).card : Real) + 1 =
        (targets.card : Real) := by
      exact_mod_cast hcardNat
    rw [← hsplit]
    exact (add_lt_add_of_le_of_lt hother hslack).trans_eq hcardReal
  have hcardReal : (sources.card : Real) < targets.card := by
    rw [hsourceSum, Finset.sum_comm]
    exact hloadLt
  exact_mod_cast hcardReal
