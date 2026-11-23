/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.SessionTypes.Multiparty.Projection

/-!
# Multiparty projection statement tests

Examples over seven participants, five sorts and two labels: the two-buyer
protocol and its projections, well-formedness positives and negatives from
the source's examples (8) and (9), branch-order merging, non-participant
projection, and a two-party duality instance.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.SessionTypes

namespace MultipartyProjectionTests

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
  | nat : TestSort
deriving DecidableEq

/-- Choice labels for examples. -/
inductive TestLabel where
  | ok : TestLabel
  | quit : TestLabel
deriving DecidableEq

example : DecidableEq (GlobalType TestPeer TestSort TestLabel) := inferInstance
example : DecidableEq (LocalType TestPeer TestSort TestLabel) := inferInstance

/-- Two-buyer (source Ex. 3.8) projects onto buyer1, buyer2 and seller;
buyer1/buyer2 types are the source's, the seller type is derived. -/
theorem two_buyer_projections :
    GlobalType.project
      (GlobalType.msg TestPeer.buyer1 TestPeer.seller TestSort.str
        (GlobalType.msg TestPeer.seller TestPeer.buyer1 TestSort.int
          (GlobalType.msg TestPeer.seller TestPeer.buyer2 TestSort.int
            (GlobalType.msg TestPeer.buyer1 TestPeer.buyer2 TestSort.int
              (GlobalType.choice TestPeer.buyer2 TestPeer.seller
                (GlobalType.Branches.cons TestLabel.ok
                  (GlobalType.msg TestPeer.buyer2 TestPeer.seller TestSort.str
                    (GlobalType.msg TestPeer.seller TestPeer.buyer2 TestSort.date .end))
                  (GlobalType.Branches.cons TestLabel.quit .end
                    GlobalType.Branches.nil))))))) TestPeer.buyer1 =
      some (LocalType.send TestPeer.seller TestSort.str
        (LocalType.recv TestPeer.seller TestSort.int
          (LocalType.send TestPeer.buyer2 TestSort.int .end))) ∧
    GlobalType.project
      (GlobalType.msg TestPeer.buyer1 TestPeer.seller TestSort.str
        (GlobalType.msg TestPeer.seller TestPeer.buyer1 TestSort.int
          (GlobalType.msg TestPeer.seller TestPeer.buyer2 TestSort.int
            (GlobalType.msg TestPeer.buyer1 TestPeer.buyer2 TestSort.int
              (GlobalType.choice TestPeer.buyer2 TestPeer.seller
                (GlobalType.Branches.cons TestLabel.ok
                  (GlobalType.msg TestPeer.buyer2 TestPeer.seller TestSort.str
                    (GlobalType.msg TestPeer.seller TestPeer.buyer2 TestSort.date .end))
                  (GlobalType.Branches.cons TestLabel.quit .end
                    GlobalType.Branches.nil))))))) TestPeer.buyer2 =
      some (LocalType.recv TestPeer.seller TestSort.int
        (LocalType.recv TestPeer.buyer1 TestSort.int
          (LocalType.select TestPeer.seller
            (LocalType.Branches.cons TestLabel.ok
              (LocalType.send TestPeer.seller TestSort.str
                (LocalType.recv TestPeer.seller TestSort.date .end))
              (LocalType.Branches.cons TestLabel.quit .end
                LocalType.Branches.nil))))) ∧
    GlobalType.project
      (GlobalType.msg TestPeer.buyer1 TestPeer.seller TestSort.str
        (GlobalType.msg TestPeer.seller TestPeer.buyer1 TestSort.int
          (GlobalType.msg TestPeer.seller TestPeer.buyer2 TestSort.int
            (GlobalType.msg TestPeer.buyer1 TestPeer.buyer2 TestSort.int
              (GlobalType.choice TestPeer.buyer2 TestPeer.seller
                (GlobalType.Branches.cons TestLabel.ok
                  (GlobalType.msg TestPeer.buyer2 TestPeer.seller TestSort.str
                    (GlobalType.msg TestPeer.seller TestPeer.buyer2 TestSort.date .end))
                  (GlobalType.Branches.cons TestLabel.quit .end
                    GlobalType.Branches.nil))))))) TestPeer.seller =
      some (LocalType.recv TestPeer.buyer1 TestSort.str
        (LocalType.send TestPeer.buyer1 TestSort.int
          (LocalType.send TestPeer.buyer2 TestSort.int
            (LocalType.branch TestPeer.buyer2
              (LocalType.Branches.cons TestLabel.ok
                (LocalType.recv TestPeer.buyer2 TestSort.str
                  (LocalType.send TestPeer.buyer2 TestSort.date .end))
                (LocalType.Branches.cons TestLabel.quit .end
                  LocalType.Branches.nil)))))) := by exact ⟨by decide, by decide, by decide⟩

/-- The two-buyer global type is well formed. -/
theorem two_buyer_wellFormed :
    (GlobalType.msg TestPeer.buyer1 TestPeer.seller TestSort.str
      (GlobalType.msg TestPeer.seller TestPeer.buyer1 TestSort.int
        (GlobalType.msg TestPeer.seller TestPeer.buyer2 TestSort.int
          (GlobalType.msg TestPeer.buyer1 TestPeer.buyer2 TestSort.int
            (GlobalType.choice TestPeer.buyer2 TestPeer.seller
              (GlobalType.Branches.cons TestLabel.ok
                (GlobalType.msg TestPeer.buyer2 TestPeer.seller TestSort.str
                  (GlobalType.msg TestPeer.seller TestPeer.buyer2 TestSort.date .end))
                (GlobalType.Branches.cons TestLabel.quit .end
                  GlobalType.Branches.nil))))))).WellFormed := by decide

/-- Source example (8): mismatched branch payloads make the third-party
projection undefined, so the global type is not well formed. -/
theorem example8_not_wellFormed :
    GlobalType.project
      (GlobalType.choice TestPeer.peerA TestPeer.peerB
        (GlobalType.Branches.cons TestLabel.ok
          (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)
          (GlobalType.Branches.cons TestLabel.quit
            (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.nat .end)
            GlobalType.Branches.nil))) TestPeer.peerC = none ∧
    ¬ (GlobalType.choice TestPeer.peerA TestPeer.peerB
      (GlobalType.Branches.cons TestLabel.ok
        (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)
        (GlobalType.Branches.cons TestLabel.quit
          (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.nat .end)
          GlobalType.Branches.nil))).WellFormed := by exact ⟨by decide, by decide⟩

/-- Source example (9): matching payloads project at all four parties. -/
theorem example9_wellFormed :
    (GlobalType.choice TestPeer.peerA TestPeer.peerB
      (GlobalType.Branches.cons TestLabel.ok
        (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)
        (GlobalType.Branches.cons TestLabel.quit
          (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)
          GlobalType.Branches.nil))).WellFormed ∧
    GlobalType.project
      (GlobalType.choice TestPeer.peerA TestPeer.peerB
        (GlobalType.Branches.cons TestLabel.ok
          (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)
          (GlobalType.Branches.cons TestLabel.quit
            (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)
            GlobalType.Branches.nil))) TestPeer.peerA =
      some (LocalType.select TestPeer.peerB
        (LocalType.Branches.cons TestLabel.ok .end
          (LocalType.Branches.cons TestLabel.quit .end LocalType.Branches.nil))) ∧
    GlobalType.project
      (GlobalType.choice TestPeer.peerA TestPeer.peerB
        (GlobalType.Branches.cons TestLabel.ok
          (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)
          (GlobalType.Branches.cons TestLabel.quit
            (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)
            GlobalType.Branches.nil))) TestPeer.peerB =
      some (LocalType.branch TestPeer.peerA
        (LocalType.Branches.cons TestLabel.ok .end
          (LocalType.Branches.cons TestLabel.quit .end LocalType.Branches.nil))) ∧
    GlobalType.project
      (GlobalType.choice TestPeer.peerA TestPeer.peerB
        (GlobalType.Branches.cons TestLabel.ok
          (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)
          (GlobalType.Branches.cons TestLabel.quit
            (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)
            GlobalType.Branches.nil))) TestPeer.peerC =
      some (LocalType.send TestPeer.peerD TestSort.bool .end) ∧
    GlobalType.project
      (GlobalType.choice TestPeer.peerA TestPeer.peerB
        (GlobalType.Branches.cons TestLabel.ok
          (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)
          (GlobalType.Branches.cons TestLabel.quit
            (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)
            GlobalType.Branches.nil))) TestPeer.peerD =
      some (LocalType.recv TestPeer.peerC TestSort.bool .end) := by
  exact ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- A reflexive interaction does not project. -/
theorem reflexive_not_wellFormed :
    ¬ ((GlobalType.msg TestPeer.peerA TestPeer.peerA TestSort.bool .end) :
      GlobalType TestPeer TestSort TestLabel).WellFormed := by decide

/-- A third party whose branch projections differ only in branch order
still merges (brace equality, not syntactic equality). -/
theorem reorder_merge_wellFormed :
    (GlobalType.choice TestPeer.peerA TestPeer.peerB
      (GlobalType.Branches.cons TestLabel.ok
        (GlobalType.choice TestPeer.peerC TestPeer.peerD
          (GlobalType.Branches.cons TestLabel.ok
            (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)
            (GlobalType.Branches.cons TestLabel.quit .end GlobalType.Branches.nil)))
        (GlobalType.Branches.cons TestLabel.quit
          (GlobalType.choice TestPeer.peerC TestPeer.peerD
            (GlobalType.Branches.cons TestLabel.quit .end
              (GlobalType.Branches.cons TestLabel.ok
                (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)
                GlobalType.Branches.nil)))
          GlobalType.Branches.nil))).WellFormed ∧
    GlobalType.project
      (GlobalType.choice TestPeer.peerA TestPeer.peerB
        (GlobalType.Branches.cons TestLabel.ok
          (GlobalType.choice TestPeer.peerC TestPeer.peerD
            (GlobalType.Branches.cons TestLabel.ok
              (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)
              (GlobalType.Branches.cons TestLabel.quit .end GlobalType.Branches.nil)))
          (GlobalType.Branches.cons TestLabel.quit
            (GlobalType.choice TestPeer.peerC TestPeer.peerD
              (GlobalType.Branches.cons TestLabel.quit .end
                (GlobalType.Branches.cons TestLabel.ok
                  (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)
                  GlobalType.Branches.nil)))
            GlobalType.Branches.nil))) TestPeer.peerC =
      some (LocalType.select TestPeer.peerD
        (LocalType.Branches.cons TestLabel.ok
          (LocalType.send TestPeer.peerD TestSort.bool .end)
          (LocalType.Branches.cons TestLabel.quit .end LocalType.Branches.nil))) := by
  exact ⟨by decide, by decide⟩

/-- A non-participant projects to inaction. -/
theorem nonparticipant_projects_end :
    GlobalType.project
      (GlobalType.choice TestPeer.peerA TestPeer.peerB
        (GlobalType.Branches.cons TestLabel.ok
          (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)
          (GlobalType.Branches.cons TestLabel.quit
            (GlobalType.msg TestPeer.peerC TestPeer.peerD TestSort.bool .end)
            GlobalType.Branches.nil))) TestPeer.buyer1 =
      some (LocalType.end : LocalType TestPeer TestSort TestLabel) := by decide

/-- A two-party example of the erasure duality bridge. -/
theorem two_party_erase_dual_example :
    ∃ tp tq : LocalType TestPeer TestSort TestLabel,
      GlobalType.project
        (GlobalType.msg TestPeer.peerA TestPeer.peerB TestSort.bool
          (GlobalType.choice TestPeer.peerB TestPeer.peerA
            (GlobalType.Branches.cons TestLabel.ok
              (GlobalType.msg TestPeer.peerB TestPeer.peerA TestSort.nat .end)
              (GlobalType.Branches.cons TestLabel.quit .end
                GlobalType.Branches.nil)))) TestPeer.peerA = some tp ∧
      GlobalType.project
        (GlobalType.msg TestPeer.peerA TestPeer.peerB TestSort.bool
          (GlobalType.choice TestPeer.peerB TestPeer.peerA
            (GlobalType.Branches.cons TestLabel.ok
              (GlobalType.msg TestPeer.peerB TestPeer.peerA TestSort.nat .end)
              (GlobalType.Branches.cons TestLabel.quit .end
                GlobalType.Branches.nil)))) TestPeer.peerB = some tq ∧
      tp.erase = tq.erase.dual := by
  have htwoparty : (GlobalType.msg TestPeer.peerA TestPeer.peerB TestSort.bool
    (GlobalType.choice TestPeer.peerB TestPeer.peerA
      (GlobalType.Branches.cons TestLabel.ok
        (GlobalType.msg TestPeer.peerB TestPeer.peerA TestSort.nat .end)
        (GlobalType.Branches.cons TestLabel.quit .end
          GlobalType.Branches.nil)))).TwoParty TestPeer.peerA TestPeer.peerB :=
    GlobalType.TwoParty.msg (Or.inl ⟨rfl, rfl⟩) (GlobalType.TwoParty.choice
      (Or.inr ⟨rfl, rfl⟩) (GlobalType.Branches.TwoParty.cons
        (GlobalType.TwoParty.msg (Or.inr ⟨rfl, rfl⟩) GlobalType.TwoParty.end)
        (GlobalType.Branches.TwoParty.cons GlobalType.TwoParty.end
          GlobalType.Branches.TwoParty.nil)))
  exact GlobalType.project_erase_dual (p := TestPeer.peerA)
    (q := TestPeer.peerB) (by decide) htwoparty

end MultipartyProjectionTests

end Cslib.SessionTypes
