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

public import CSLibExt.Languages.CCS.Parallel

/-!
# Tests for CCS parallel composition

The examples exercise interleaving, complementary synchronization, transition
inversion, constructor congruence, and the parallel monoid laws.
-/

namespace CslibTest.Languages.CCS.Parallel

open Cslib.CCS
open Cslib.CCS.Process

inductive Channel where
  | request
  | response
  deriving DecidableEq

abbrev Process := Cslib.CCS.Process (Cslib.CCS.Label Channel)
abbrev Action := Cslib.CCS.Label Channel

def sender : Process :=
  .prefix (.output .request) (.prefix (.input .response) .nil)

def receiver : Process :=
  .prefix (.input .request) (.prefix (.output .response) .nil)

def system : Process := .parallel sender receiver

def afterRequest : Process :=
  .parallel
    (.prefix (.input .response) .nil)
    (.prefix (.output .response) .nil)

example : CommunicationStep sender (.output .request) (.prefix (.input .response) .nil) :=
  .prefix _ _

example : CommunicationStep system (.output .request)
    (.parallel (.prefix (.input .response) .nil) receiver) :=
  .parallelLeft (.prefix _ _)

example : CommunicationStep system (.input .request)
    (.parallel sender (.prefix (.output .response) .nil)) :=
  .parallelRight (.prefix _ _)

/-- Complementary request actions communicate silently. -/
example : CommunicationStep system .tau afterRequest := by
  exact .communicate (.prefix _ _) (.prefix _ _)
    (Cslib.CCS.Label.synchronize_eq_some_iff.mpr ⟨rfl, rfl⟩)

/-- The continuations can communicate on the response channel as well. -/
example : CommunicationStep afterRequest .tau (.parallel .nil .nil) := by
  exact .communicate (.prefix _ _) (.prefix _ _)
    (Cslib.CCS.Label.synchronize_eq_some_iff.mpr ⟨rfl, rfl⟩)

example (label : Action) (next : Process) : ¬CommunicationStep .nil label next :=
  communication_nil_no_step

example {head label : Action} {continuation next : Process} :
    CommunicationStep (.prefix head continuation) label next ↔
      label = head ∧ next = continuation :=
  communication_prefix_step_iff

example {left right next : Process} {label : Action} :
    CommunicationStep (.choice left right) label next ↔
      CommunicationStep left label next ∨ CommunicationStep right label next :=
  communication_choice_step_iff

example {left right next : Process} {label : Action} :
    CommunicationStep (.parallel left right) label next ↔
      (∃ left', CommunicationStep left label left' ∧ next = .parallel left' right) ∨
      (∃ right', CommunicationStep right label right' ∧ next = .parallel left right') ∨
      (label = .tau ∧ ∃ left' right' leftLabel rightLabel,
        CommunicationStep left leftLabel left' ∧ CommunicationStep right rightLabel right' ∧
        leftLabel.Complementary rightLabel ∧ next = .parallel left' right') :=
  communication_parallel_step_iff

open Cslib.LTS

example (left right : Process)
    (h : (communicationLTS (Name := Channel)).HomBisimilarity left right) :
    (communicationLTS (Name := Channel)).HomBisimilarity
      (.prefix (.input .request) left) (.prefix (.input .request) right) :=
  communication_prefix_congr _ h

example {left₁ left₂ right₁ right₂ : Process}
    (hleft : (communicationLTS (Name := Channel)).HomBisimilarity left₁ left₂)
    (hright : (communicationLTS (Name := Channel)).HomBisimilarity right₁ right₂) :
    (communicationLTS (Name := Channel)).HomBisimilarity
      (.choice left₁ right₁) (.choice left₂ right₂) :=
  communication_choice_congr hleft hright

example {left₁ left₂ right₁ right₂ : Process}
    (hleft : (communicationLTS (Name := Channel)).HomBisimilarity left₁ left₂)
    (hright : (communicationLTS (Name := Channel)).HomBisimilarity right₁ right₂) :
    (communicationLTS (Name := Channel)).HomBisimilarity
      (.parallel left₁ right₁) (.parallel left₂ right₂) :=
  parallel_congr hleft hright

example (left right : Process) :
    (communicationLTS (Name := Channel)).HomBisimilarity
      (.parallel left right) (.parallel right left) :=
  parallel_comm left right

example (process : Process) :
    (communicationLTS (Name := Channel)).HomBisimilarity (.parallel .nil process) process :=
  parallel_nil_left process

example (process : Process) :
    (communicationLTS (Name := Channel)).HomBisimilarity (.parallel process .nil) process :=
  parallel_nil_right process

#print axioms Cslib.CCS.Process.parallel_congr
#print axioms Cslib.CCS.Process.parallel_comm
#print axioms Cslib.CCS.Process.parallel_nil_left

end CslibTest.Languages.CCS.Parallel
