/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card









open Finset



theorem finiteRelationHall_of_bidegree
    {Source Target : Type*}
    [Fintype Source] [Fintype Target]
    (related : Source -> Target -> Prop) [DecidableRel related]
    (degree : Nat) (hdegree : 0 < degree)
    (hsource : forall source,
      degree <= (Finset.univ.filter (related source)).card)
    (htarget : forall target,
      (Finset.univ.filter fun source => related source target).card <= degree) :
    forall sources : Finset Source,
      sources.card <=
        (Finset.univ.filter fun target =>
          ∃ source ∈ sources, related source target).card := by
  intro sources
  let targets : Finset Target :=
    Finset.univ.filter fun target =>
      ∃ source ∈ sources, related source target
  have hleft : degree * sources.card <=
      ∑ source ∈ sources,
        (Finset.univ.filter (related source)).card := by
    calc
      degree * sources.card = ∑ _source ∈ sources, degree := by
        simp [Nat.mul_comm]
      _ <= ∑ source ∈ sources,
          (Finset.univ.filter (related source)).card :=
        Finset.sum_le_sum fun source _ => hsource source
  have hcount :
      (∑ source ∈ sources,
          (Finset.univ.filter (related source)).card) =
        ∑ target ∈ targets,
          (sources.filter fun source => related source target).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    rw [show (∑ target : Target,
        ∑ source ∈ sources, if related source target then 1 else 0) =
        ∑ target ∈ targets,
          ∑ source ∈ sources, if related source target then 1 else 0 by
      symm
      apply Finset.sum_subset (Finset.subset_univ targets)
      intro target _ htargetNot
      have hnone : ¬ ∃ source ∈ sources, related source target := by
        simpa [targets] using htargetNot
      apply Finset.sum_eq_zero
      intro source hsourceMem
      rw [if_neg]
      intro hrelated
      exact hnone ⟨source, hsourceMem, hrelated⟩]
  have hright :
      (∑ target ∈ targets,
          (sources.filter fun source => related source target).card) <=
        degree * targets.card := by
    calc
      (∑ target ∈ targets,
          (sources.filter fun source => related source target).card) <=
          ∑ _target ∈ targets, degree := by
        apply Finset.sum_le_sum
        intro target _
        calc
          (sources.filter fun source => related source target).card <=
              (Finset.univ.filter fun source =>
                related source target).card := by
            apply Finset.card_le_card
            intro source hsourceFiltered
            simp only [Finset.mem_filter] at hsourceFiltered ⊢
            exact ⟨Finset.mem_univ source, hsourceFiltered.2⟩
          _ <= degree := htarget target
      _ = degree * targets.card := by simp [Nat.mul_comm]
  have hmul : degree * sources.card <= degree * targets.card :=
    hleft.trans (hcount ▸ hright)
  exact Nat.le_of_mul_le_mul_left hmul hdegree




theorem finiteRelationHall_of_certificateEmbeddings
    {Source Target : Type*}
    [Finite Source] [Fintype Target]
    (related : Source -> Target -> Prop) [DecidableRel related]
    (degree : Nat) (hdegree : 0 < degree)
    (sourceCertificates : forall source,
      Fin degree ↪ {target : Target // related source target})
    (targetCertificateCode : forall target,
      {source : Source // related source target} ↪ Fin degree) :
    forall sources : Finset Source,
      sources.card <=
        (Finset.univ.filter fun target =>
          ∃ source ∈ sources, related source target).card := by
  letI := Fintype.ofFinite Source
  apply finiteRelationHall_of_bidegree related degree hdegree
  · intro source
    have hcard := Fintype.card_le_of_embedding
      (sourceCertificates source)
    simpa [Fintype.card_subtype] using hcard
  · intro target
    have hcard := Fintype.card_le_of_embedding
      (targetCertificateCode target)
    simpa [Fintype.card_subtype] using hcard



theorem finiteRelation_exists_injective_of_certificateEmbeddings
    {Source Target : Type*}
    [Finite Source] [Finite Target]
    (related : Source -> Target -> Prop)
    (degree : Nat) (hdegree : 0 < degree)
    (sourceCertificates : forall source,
      Fin degree ↪ {target : Target // related source target})
    (targetCertificateCode : forall target,
      {source : Source // related source target} ↪ Fin degree) :
    exists matching : Source -> Target,
      Function.Injective matching ∧
        forall source, related source (matching source) := by
  classical
  letI := Fintype.ofFinite Source
  letI := Fintype.ofFinite Target
  apply (Fintype.all_card_le_filter_rel_iff_exists_injective related).mp
  exact finiteRelationHall_of_certificateEmbeddings related degree hdegree
    sourceCertificates targetCertificateCode
