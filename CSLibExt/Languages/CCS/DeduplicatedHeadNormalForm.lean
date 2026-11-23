/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `9db2af32bec4c1fe1731f17c030e9410961257ed`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Deduplicated finite CCS head-normal forms
-/
module

public import CSLibExt.Languages.CCS.HeadNormalForm
public import CSLibExt.Languages.CCS.SumEquivalence

/-!
# Deduplicated finite CCS head-normal forms

The raw head-normal-form construction can contain the same transition more
than once, for example after idempotent choice or coincident synchronization
branches.  We remove those duplicates to obtain a finite, duplicate-free
presentation and prove that it still represents the original process.
`List.dedup` retains the last occurrence of each repeated branch and preserves
the relative order of those retained occurrences. This is not a canonical
representative of a strong-bisimilarity class: source order and the syntax of
continuation processes remain observable in the list.
-/

@[expose] public section

namespace Cslib.CCS.StaticProcess

open Cslib.LTS

variable {Name : Type*} [DecidableEq Name]

/-- Duplicate-free head summands, retaining each branch's last occurrence. -/
def deduplicatedHeadSummands (process : StaticProcess Name) : List (Summand Name) :=
  (headSummands process).dedup

/-- The duplicate-free head normal form of a finite process. -/
def deduplicatedHeadNormalForm (process : StaticProcess Name) : StaticProcess Name :=
  sum (deduplicatedHeadSummands process)

@[simp] theorem deduplicatedHeadSummands_nodup (process : StaticProcess Name) :
    (deduplicatedHeadSummands process).Nodup :=
  List.nodup_dedup _

theorem mem_deduplicatedHeadSummands_iff {process : StaticProcess Name}
    {branch : Summand Name} :
    branch ∈ deduplicatedHeadSummands process ↔
      branch ∈ headSummands process := by
  simp [deduplicatedHeadSummands]

/-- Deduplicating the computed head normal form preserves strong behaviour. -/
theorem deduplicatedHeadNormalForm_bisimilar_headNormalForm
    (process : StaticProcess Name) :
    lts.HomBisimilarity (deduplicatedHeadNormalForm process) (headNormalForm process) :=
  sum_dedup_bisimilar (headSummands process)

/-- Every finite static CCS process is strongly bisimilar to its deduplicated
head normal form. -/
theorem bisimilar_deduplicatedHeadNormalForm (process : StaticProcess Name) :
    lts.HomBisimilarity process (deduplicatedHeadNormalForm process) :=
  (bisimilar_headNormalForm process).trans
    (deduplicatedHeadNormalForm_bisimilar_headNormalForm process).symm

/-- Deduplicating the head form preserves and reflects enabled actions. -/
theorem enabled_deduplicatedHeadNormalForm_iff (process : StaticProcess Name)
    (action : Label Name) :
    lts.HasOutLabel process action ↔
      lts.HasOutLabel (deduplicatedHeadNormalForm process) action :=
  HomBisimilarity.hasOutLabel_iff
    (bisimilar_deduplicatedHeadNormalForm process) action

/-- An action is enabled precisely when it labels a deduplicated head summand. -/
theorem enabled_iff_mem_deduplicatedHeadSummands (process : StaticProcess Name)
    (action : Label Name) :
    lts.HasOutLabel process action ↔
      ∃ continuation, (action, continuation) ∈ deduplicatedHeadSummands process := by
  rw [enabled_deduplicatedHeadNormalForm_iff, deduplicatedHeadNormalForm, sum_enabled_iff]

/-- Deduplicating the head form preserves the ready set exactly. -/
theorem deduplicatedHeadNormalForm_readySet (process : StaticProcess Name) :
    lts.outgoingLabels (deduplicatedHeadNormalForm process) = lts.outgoingLabels process :=
  HomBisimilarity.outgoingLabels_eq
    (bisimilar_deduplicatedHeadNormalForm process).symm

/-- Deduplicating the head form is idempotent up to strong bisimilarity. -/
theorem deduplicatedHeadNormalForm_idempotent (process : StaticProcess Name) :
    lts.HomBisimilarity
      (deduplicatedHeadNormalForm (deduplicatedHeadNormalForm process))
      (deduplicatedHeadNormalForm process) :=
  (bisimilar_deduplicatedHeadNormalForm (deduplicatedHeadNormalForm process)).symm

/-- Processes with identical deduplicated summand membership are strongly
bisimilar.  This is a convenient finite certificate for strong equivalence. -/
theorem bisimilar_of_deduplicated_members {left right : StaticProcess Name}
    (members : ∀ branch,
      branch ∈ deduplicatedHeadSummands left ↔
        branch ∈ deduplicatedHeadSummands right) :
    lts.HomBisimilarity left right := by
  exact (bisimilar_deduplicatedHeadNormalForm left).trans
    ((sum_bisimilar_of_mem_iff members).trans
      (bisimilar_deduplicatedHeadNormalForm right).symm)

/-- Syntactically equal deduplicated summand lists certify strong equivalence. -/
theorem bisimilar_of_deduplicatedHeadSummands_eq {left right : StaticProcess Name}
    (equal : deduplicatedHeadSummands left = deduplicatedHeadSummands right) :
    lts.HomBisimilarity left right := by
  apply bisimilar_of_deduplicated_members
  intro branch
  rw [equal]

/-- Strongly bisimilar processes have the same enabled labels after head-form
deduplication, even when their continuation presentations differ. -/
theorem deduplicated_enabled_iff_of_bisimilar {left right : StaticProcess Name}
    (related : lts.HomBisimilarity left right) (action : Label Name) :
    lts.HasOutLabel (deduplicatedHeadNormalForm left) action ↔
      lts.HasOutLabel (deduplicatedHeadNormalForm right) action := by
  rw [← enabled_deduplicatedHeadNormalForm_iff left,
    ← enabled_deduplicatedHeadNormalForm_iff right]
  exact HomBisimilarity.hasOutLabel_iff related action

end Cslib.CCS.StaticProcess
