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

public import CSLibExt.Languages.CCS.WeakStaticLaws

/-!
# Tests for weak equivalence in extended finite CCS

These examples exercise weak synchronization and every static congruence API
at the extended process type.
-/

namespace CslibTest.Languages.CCS.WeakStatic

open Cslib.CCS Cslib.CCS.StaticProcess Cslib.LTS

inductive Channel where
  | request
  | response
  deriving DecidableEq

abbrev Process := StaticProcess Channel

def sender : Process :=
  .prefix .tau (.prefix (.output .request) .nil)

def receiver : Process :=
  .prefix .tau (.prefix (.input .request) .nil)

def senderReady : Process := .prefix (.output .request) .nil
def receiverReady : Process := .prefix (.input .request) .nil

example : lts.τSTr sender senderReady :=
  τSTr.of_tr (.prefix _ _)

example : lts.τSTr
    (.parallel sender receiver) (.parallel senderReady receiverReady) := by
  exact (τSTr.parallelLeft (τSTr.of_tr (.prefix _ _))).trans
    (τSTr.parallelRight (τSTr.of_tr (.prefix _ _)))

example : lts.τSTr
    (.parallel sender receiver) (.parallel .nil .nil) := by
  apply weakComplementary_parallel
  · exact _root_.Cslib.LTS.STr.tr (τSTr.of_tr (.prefix _ _))
      (.prefix _ _) Relation.ReflTransGen.refl
  · exact _root_.Cslib.LTS.STr.tr (τSTr.of_tr (.prefix _ _))
      (.prefix _ _) Relation.ReflTransGen.refl
  · exact rfl

example (blocked : List Channel) {left right : Process}
    (h : StaticProcess.WeaklyBisimilar left right) :
    StaticProcess.WeaklyBisimilar (.restriction blocked left) (.restriction blocked right) :=
  restriction_weaklyBisimilar_congr blocked h

example (rename : Relabelling Channel) {left right : Process}
    (h : StaticProcess.WeaklyBisimilar left right) :
    StaticProcess.WeaklyBisimilar (.relabelling rename left) (.relabelling rename right) :=
  relabelling_weaklyBisimilar_congr rename h

example {left₁ left₂ right₁ right₂ : Process}
    (hleft : StaticProcess.WeaklyBisimilar left₁ left₂)
    (hright : StaticProcess.WeaklyBisimilar right₁ right₂) :
    StaticProcess.WeaklyBisimilar (.parallel left₁ right₁) (.parallel left₂ right₂) :=
  parallel_weaklyBisimilar_congr hleft hright

example (blocked : List Channel) {left right : Process}
    (h : ObservationCongruent left right) :
    ObservationCongruent (.restriction blocked left) (.restriction blocked right) :=
  restriction_observationCongruent_congr blocked h

example (rename : Relabelling Channel) {left right : Process}
    (h : ObservationCongruent left right) :
    ObservationCongruent (.relabelling rename left) (.relabelling rename right) :=
  relabelling_observationCongruent_congr rename h

example {left₁ left₂ right₁ right₂ : Process}
    (hleft : ObservationCongruent left₁ left₂)
    (hright : ObservationCongruent right₁ right₂) :
    ObservationCongruent (.choice left₁ right₁) (.choice left₂ right₂) :=
  choice_observationCongruent_congr hleft hright

example {left₁ left₂ right₁ right₂ : Process}
    (hleft : ObservationCongruent left₁ left₂)
    (hright : ObservationCongruent right₁ right₂) :
    ObservationCongruent (.parallel left₁ right₁) (.parallel left₂ right₂) :=
  parallel_observationCongruent_congr hleft hright

example (process : Process) :
    StaticProcess.WeaklyBisimilar (.prefix .tau process) process :=
  tau_prefix_weaklyBisimilar process

example (blocked : List Channel) :
    ObservationCongruent (.restriction blocked (.choice sender receiver))
      (.choice (.restriction blocked sender) (.restriction blocked receiver)) :=
  restriction_choice_observationCongruent blocked sender receiver

example : StaticProcess.WeaklyBisimilar
    (.relabelling ⟨[]⟩ sender) sender :=
  relabelling_empty_weaklyBisimilar sender

example : ObservationCongruent (.choice sender receiver) (.choice receiver sender) :=
  choice_comm_observationCongruent sender receiver

#print axioms Cslib.CCS.StaticProcess.restriction_weaklyBisimilar_congr
#print axioms Cslib.CCS.StaticProcess.relabelling_weaklyBisimilar_congr
#print axioms Cslib.CCS.StaticProcess.parallel_weaklyBisimilar_congr
#print axioms Cslib.CCS.StaticProcess.restriction_observationCongruent_congr
#print axioms Cslib.CCS.StaticProcess.relabelling_observationCongruent_congr
#print axioms Cslib.CCS.StaticProcess.choice_observationCongruent_congr
#print axioms Cslib.CCS.StaticProcess.parallel_observationCongruent_congr
#print axioms Cslib.CCS.StaticProcess.tau_prefix_weaklyBisimilar
#print axioms Cslib.CCS.StaticProcess.restriction_choice_observationCongruent
#print axioms Cslib.CCS.StaticProcess.relabelling_empty_weaklyBisimilar
#print axioms Cslib.CCS.StaticProcess.choice_comm_observationCongruent

end CslibTest.Languages.CCS.WeakStatic
