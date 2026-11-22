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

public import CSLibExt.Languages.CCS.StaticLaws

@[expose] public section

namespace CslibTest.Languages.CCS.StaticLaws

open Cslib.CCS Cslib.CCS.StaticProcess Cslib.LTS

inductive Channel where
  | left
  | right
  | renamed
  deriving DecidableEq

abbrev Process := StaticProcess Channel

def renameLeft : Relabelling Channel := ⟨[(.left, .input .renamed)]⟩
def leftInput : Process := .prefix (.input .left) .nil
def rightInput : Process := .prefix (.input .right) .nil

example : lts.HomBisimilarity (.restriction ([.left] : List Channel) (.nil : Process)) .nil :=
  restriction_nil ([.left] : List Channel)

example : lts.HomBisimilarity (.restriction [.left] rightInput)
    (.prefix (.input .right) (.restriction [.left] .nil)) :=
  restriction_prefix_of_allowed ([.left] : List Channel) (.input .right) .nil (by simp)

example : lts.HomBisimilarity (.restriction [.left] leftInput) .nil :=
  restriction_prefix_of_blocked ([.left] : List Channel) (.input .left) .nil (by simp)

example : lts.HomBisimilarity (.restriction [.left] (.choice leftInput rightInput))
    (.choice (.restriction [.left] leftInput) (.restriction [.left] rightInput)) :=
  restriction_choice [.left] leftInput rightInput

example : lts.HomBisimilarity (.restriction [] leftInput) leftInput :=
  restriction_empty leftInput

example : lts.HomBisimilarity (.restriction [.left, .right, .left] leftInput)
    (.restriction [.right, .left] leftInput) := by
  apply restriction_congr_list
  intro name
  cases name <;> simp

example : lts.HomBisimilarity (.relabelling renameLeft (.nil : Process)) .nil :=
  relabelling_nil renameLeft

example : lts.HomBisimilarity (.relabelling renameLeft leftInput)
    (.prefix (.input .renamed) (.relabelling renameLeft .nil)) := by
  simpa [leftInput, renameLeft, VisibleLabel.toLabel] using
    relabelling_prefix renameLeft (.input .left) (.nil : Process)

example : lts.HomBisimilarity (.relabelling renameLeft (.choice leftInput rightInput))
    (.choice (.relabelling renameLeft leftInput) (.relabelling renameLeft rightInput)) :=
  relabelling_choice renameLeft leftInput rightInput

example : lts.HomBisimilarity (.relabelling ⟨[]⟩ leftInput) leftInput :=
  relabelling_empty leftInput

#print axioms Cslib.CCS.StaticProcess.restriction_nil
#print axioms Cslib.CCS.StaticProcess.restriction_prefix_of_allowed
#print axioms Cslib.CCS.StaticProcess.restriction_prefix_of_blocked
#print axioms Cslib.CCS.StaticProcess.restriction_choice
#print axioms Cslib.CCS.StaticProcess.restriction_empty
#print axioms Cslib.CCS.StaticProcess.restriction_congr_list
#print axioms Cslib.CCS.StaticProcess.relabelling_nil
#print axioms Cslib.CCS.StaticProcess.relabelling_prefix
#print axioms Cslib.CCS.StaticProcess.relabelling_choice
#print axioms Cslib.CCS.StaticProcess.relabelling_empty

end CslibTest.Languages.CCS.StaticLaws
