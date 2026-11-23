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

module

public import CSLibExt.Languages.CCS.DeduplicatedHeadNormalForm

@[expose] public section

namespace CslibTest.Languages.CCS.HeadNormalForm

open Cslib.CCS Cslib.CCS.StaticProcess Cslib.LTS

inductive Channel where
  | request
  | reply
  | hidden
  deriving DecidableEq

abbrev Process := StaticProcess Channel

def requester : Process :=
  .prefix (.output .request) (.prefix (.input .reply) .nil)

def server : Process :=
  .prefix (.input .request) (.prefix (.output .reply) .nil)

def system : Process := .parallel requester server

def repeatedChoice : Process :=
  .choice (.prefix (.input .request) .nil)
    (.choice (.prefix (.output .reply) .nil)
      (.prefix (.input .request) .nil))

example : lts.HomBisimilarity system (headNormalForm system) :=
  bisimilar_headNormalForm system

example : lts.HomBisimilarity system (deduplicatedHeadNormalForm system) :=
  bisimilar_deduplicatedHeadNormalForm system

example : (deduplicatedHeadSummands system).Nodup :=
  deduplicatedHeadSummands_nodup system

/-- Deduplication retains the last repeated branch, so the middle distinct
branch precedes it in the resulting executable list. -/
example : deduplicatedHeadSummands repeatedChoice =
    [((.output .reply : Label Channel), .nil),
      ((.input .request : Label Channel), .nil)] := by
  decide

example : lts.HasOutLabel system (.output .request) := by
  exact ⟨_, .parallelLeft (.prefix _ _)⟩

example : lts.HasOutLabel (deduplicatedHeadNormalForm system) (.output .request) := by
  exact (enabled_deduplicatedHeadNormalForm_iff system (.output .request)).mp (by
    exact ⟨_, .parallelLeft (.prefix _ _)⟩)

example : lts.HasOutLabel system .tau := by
  exact ⟨_, .communicate (.prefix _ _) (.prefix _ _) (by simp [Label.Complementary])⟩

example : ∃ continuation,
    ((.tau : Label Channel), continuation) ∈ deduplicatedHeadSummands system := by
  exact (enabled_iff_mem_deduplicatedHeadSummands system .tau).mp (by
    exact ⟨_, .communicate (.prefix _ _) (.prefix _ _) (by simp [Label.Complementary])⟩)

example : lts.HomBisimilarity
    (sum [((.input .request : Label Channel), .nil),
      ((.output .reply : Label Channel), .nil)])
    (sum [((.output .reply : Label Channel), .nil),
      ((.input .request : Label Channel), .nil)]) := by
  simpa using sum_append_comm_bisimilar
    ([((.input .request : Label Channel), .nil)] : List (Summand Channel))
    ([((.output .reply : Label Channel), .nil)] : List (Summand Channel))

example : lts.HomBisimilarity
    (sum [((.input .request : Label Channel), .nil),
      ((.input .request : Label Channel), .nil)])
    (sum [((.input .request : Label Channel), .nil)]) := by
  apply sum_cons_of_mem_bisimilar
  simp

example :
    restrictSummands [.hidden]
      [((.input .hidden : Label Channel), .nil),
       ((.output .request : Label Channel), .nil)] =
      [((.output .request : Label Channel), .restriction [.hidden] .nil)] := by
  simp [restrictSummands, Allowed]

example :
    (restrictSummands [.hidden]
      [((.input .hidden : Label Channel), .nil),
       ((.output .request : Label Channel), .nil)]).length ≤ 2 :=
  restrictSummands_length_le _ _

#print axioms Cslib.CCS.StaticProcess.parallel_sum_bisimilar_expansion
#print axioms Cslib.CCS.StaticProcess.restriction_sum_bisimilar
#print axioms Cslib.CCS.StaticProcess.relabelling_sum_bisimilar
#print axioms Cslib.CCS.StaticProcess.bisimilar_headNormalForm
#print axioms Cslib.CCS.StaticProcess.bisimilar_deduplicatedHeadNormalForm
#print axioms Cslib.CCS.StaticProcess.bisimilar_of_deduplicated_members

end CslibTest.Languages.CCS.HeadNormalForm
