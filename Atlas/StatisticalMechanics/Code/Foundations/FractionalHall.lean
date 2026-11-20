/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic









open Finset



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
