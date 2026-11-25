/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.SessionTypes.Multiparty.LTS

/-!
# Multiparty LTS statement tests

The two-buyer first step and its three local projections, action
independence, a negative test for the synchronous side condition, the
branch-order bystander example, a step under choice, and preservation of
well-formedness on a one-message type.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.SessionTypes

namespace MultipartyLTSTests

/-- Participants for examples. -/
inductive TestPeer where
  | buyer1 : TestPeer
  | buyer2 : TestPeer
  | seller : TestPeer
  | peerA : TestPeer
  | peerB : TestPeer
  | peerC : TestPeer
  | peerD : TestPeer
deriving DecidableEq

/-- Payload sorts for examples. -/
inductive TestSort where
  | str : TestSort
  | int : TestSort
  | date : TestSort
  | bool : TestSort
deriving DecidableEq

/-- Choice labels for examples. -/
inductive TestLabel where
  | ok : TestLabel
  | quit : TestLabel
deriving DecidableEq

/-- The two-buyer global type. -/
def twoBuyer : GlobalType TestPeer TestSort TestLabel :=
  .msg .buyer1 .seller .str
    (.msg .seller .buyer1 .int
      (.msg .seller .buyer2 .int
        (.msg .buyer1 .buyer2 .int
          (.choice .buyer2 .seller
            (.cons .ok
              (.msg .buyer2 .seller .str
                (.msg .seller .buyer2 .date .end))
              (.cons .quit .end .nil))))))

/-- The two-buyer global type after its first message. -/
def twoBuyerAfter : GlobalType TestPeer TestSort TestLabel :=
  .msg .seller .buyer1 .int
    (.msg .seller .buyer2 .int
      (.msg .buyer1 .buyer2 .int
        (.choice .buyer2 .seller
          (.cons .ok
            (.msg .buyer2 .seller .str
              (.msg .seller .buyer2 .date .end))
            (.cons .quit .end .nil)))))

/-- Example (9): both branches send bool from C to D. -/
def example9 : GlobalType TestPeer TestSort TestLabel :=
  .choice .peerA .peerB
    (.cons .ok (.msg .peerC .peerD .bool .end)
      (.cons .quit (.msg .peerC .peerD .bool .end) .nil))

/-- The branch-order merging example: C's two branch projections differ
only in branch order. -/
def reorder : GlobalType TestPeer TestSort TestLabel :=
  .choice .peerA .peerB
    (.cons .ok
      (.choice .peerC .peerD
        (.cons .ok (.msg .peerC .peerD .bool .end)
          (.cons .quit .end .nil)))
      (.cons .quit
        (.choice .peerC .peerD
          (.cons .quit .end
            (.cons .ok (.msg .peerC .peerD .bool .end) .nil)))
        .nil))

/-- The selected second branch of the branch-order example. -/
def reorderAfter : GlobalType TestPeer TestSort TestLabel :=
  .choice .peerC .peerD
    (.cons .quit .end
      (.cons .ok (.msg .peerC .peerD .bool .end) .nil))

/-- Two-buyer takes its first global step. -/
theorem two_buyer_first_step :
    GlobalType.Step twoBuyer (.msg .buyer1 .seller .str)
      twoBuyerAfter := by
  exact GlobalType.Step.msg

/-- Buyer1 performs the matching send in the two-buyer first step. -/
theorem two_buyer_first_step_buyer1 :
    ∃ t t' : LocalType TestPeer TestSort TestLabel,
      twoBuyer.project .buyer1 = some t ∧
      twoBuyerAfter.project .buyer1 = some t' ∧
      LocalType.Step t (.send .seller .str) t' := by
  refine ⟨.send .seller .str (.recv .seller .int (.send .buyer2 .int .end)),
    .recv .seller .int (.send .buyer2 .int .end), by decide, by decide,
    LocalType.Step.send⟩

/-- The seller performs the matching receive in the two-buyer first
step. -/
theorem two_buyer_first_step_seller :
    ∃ t t' : LocalType TestPeer TestSort TestLabel,
      twoBuyer.project .seller = some t ∧
      twoBuyerAfter.project .seller = some t' ∧
      LocalType.Step t (.recv .buyer1 .str) t' := by
  refine ⟨.recv .buyer1 .str
      (.send .buyer1 .int
        (.send .buyer2 .int
          (.branch .buyer2
            (.cons .ok (.recv .buyer2 .str (.send .buyer2 .date .end))
              (.cons .quit .end .nil))))),
    .send .buyer1 .int
      (.send .buyer2 .int
        (.branch .buyer2
          (.cons .ok (.recv .buyer2 .str (.send .buyer2 .date .end))
            (.cons .quit .end .nil)))),
    by decide, by decide, LocalType.Step.recv⟩

/-- Buyer2 is a bystander in the two-buyer first step. -/
theorem two_buyer_first_step_buyer2 :
    ∃ t t' : LocalType TestPeer TestSort TestLabel,
      twoBuyer.project .buyer2 = some t ∧
      twoBuyerAfter.project .buyer2 = some t' ∧
      t.braceEq t' = true := by
  refine ⟨.recv .seller .int
      (.recv .buyer1 .int
        (.select .seller
          (.cons .ok (.send .seller .str (.recv .seller .date .end))
            (.cons .quit .end .nil)))),
    .recv .seller .int
      (.recv .buyer1 .int
        (.select .seller
          (.cons .ok (.send .seller .str (.recv .seller .date .end))
            (.cons .quit .end .nil)))),
    by decide, by decide, by decide⟩

/-- An independent second interaction may fire first. -/
theorem independent_second_step_first :
    GlobalType.Step
      ((GlobalType.msg TestPeer.peerA TestPeer.peerB TestSort.int
        (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)) :
        GlobalType TestPeer TestSort TestLabel)
      (GlobalType.Label.msg TestPeer.peerC TestPeer.peerD TestSort.bool)
      (GlobalType.msg TestPeer.peerA TestPeer.peerB TestSort.int .end) := by
  exact GlobalType.Step.msgCongr GlobalType.Step.msg
    (by decide) (by decide) (by decide) (by decide)

/-- The synchronous LTS rejects firing a later interaction whose
receiver is the first interaction's sender before that sender acts. -/
theorem synchronous_rejects_async_step :
    ¬ ∃ G' : GlobalType TestPeer TestSort TestLabel,
      GlobalType.Step
        (.msg .peerA .peerB .int (.msg .peerC .peerA .bool .end))
        (.msg .peerC .peerA .bool) G' := by
  rintro ⟨G', h⟩
  cases h with
  | msgCongr _ _ hs2 _ _ => exact hs2 rfl

/-- After the quit branch of the reorder example is selected, C's
projection changes only by branch order. -/
theorem reorder_step_bystander_brace_not_eq :
    GlobalType.Step reorder (.choice .peerA .peerB .quit) reorderAfter ∧
    ∃ t t' : LocalType TestPeer TestSort TestLabel,
      reorder.project .peerC = some t ∧
      reorderAfter.project .peerC = some t' ∧
      t.braceEq t' = true ∧ t ≠ t' := by
  refine ⟨GlobalType.Step.choice (by decide),
    .select .peerD
      (.cons .ok (.send .peerD .bool .end) (.cons .quit .end .nil)),
    .select .peerD
      (.cons .quit .end (.cons .ok (.send .peerD .bool .end) .nil)),
    by decide, by decide, by decide, by decide⟩

/-- A third party's interaction can step under every branch of a choice. -/
theorem choice_congr_third_party_sender :
    GlobalType.Step example9 (.msg .peerC .peerD .bool)
      (.choice .peerA .peerB
        (.cons .ok .end (.cons .quit .end .nil))) := by
  exact GlobalType.Step.choiceCongr
    (GlobalType.Branches.Step.cons GlobalType.Step.msg
      (GlobalType.Branches.Step.cons GlobalType.Step.msg
        GlobalType.Branches.Step.nil))
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- An empty choice has no global step: neither a branch selection nor the
choice congruence rule applies. -/
theorem empty_choice_no_step :
    ¬ ∃ (ℓ : GlobalType.Label TestPeer TestSort TestLabel)
        (G' : GlobalType TestPeer TestSort TestLabel),
      GlobalType.Step (.choice .peerA .peerB .nil) ℓ G' := by
  rintro ⟨ℓ, G', h⟩
  cases h with
  | choice hmem => exact absurd hmem List.not_mem_nil
  | choiceCongr _ hne _ _ _ _ => exact hne rfl

/-- A one-message well-formed type steps to the well-formed end type. -/
theorem wellFormed_step_msg_end :
    (GlobalType.msg .peerA .peerB .bool .end :
      GlobalType TestPeer TestSort TestLabel).WellFormed ∧
    GlobalType.Step
      (GlobalType.msg .peerA .peerB .bool .end :
        GlobalType TestPeer TestSort TestLabel)
      (.msg .peerA .peerB .bool) .end ∧
    (GlobalType.end : GlobalType TestPeer TestSort TestLabel).WellFormed := by
  exact ⟨by decide, GlobalType.Step.msg, by decide⟩

end MultipartyLTSTests

end Cslib.SessionTypes
