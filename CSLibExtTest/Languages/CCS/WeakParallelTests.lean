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

public import CSLibExt.Languages.CCS.WeakParallel

/-!
# Tests for weak CCS parallel semantics

The examples check silent-closure lifting, synchronization after silent
preparation, and congruence of weak bisimilarity under parallel composition.
-/

namespace CslibTest.Languages.CCS.WeakParallel

open Cslib.CCS Cslib.CCS.Process
open Cslib.LTS

inductive Channel where
  | request
  | response
  deriving DecidableEq

abbrev Process := Cslib.CCS.Process (Cslib.CCS.Label Channel)
abbrev Action := Cslib.CCS.Label Channel

/-- The ordinary public import supplies the canonical silent-label instance. -/
example : Cslib.HasTau.τ = (Label.tau : Action) := rfl

def leftDelayed : Process :=
  .prefix .tau (.prefix (.output .request) .nil)

def leftReady : Process :=
  .prefix (.output .request) .nil

def rightDelayed : Process :=
  .prefix .tau (.prefix (.input .request) .nil)

def rightReady : Process :=
  .prefix (.input .request) .nil

example : (communicationLTS (Name := Channel)).τSTr leftDelayed leftReady :=
  τSTr.of_tr (.prefix _ _)

example : (communicationLTS (Name := Channel)).τSTr rightDelayed rightReady :=
  τSTr.of_tr (.prefix _ _)

example : (communicationLTS (Name := Channel)).τSTr
    (.parallel leftDelayed rightDelayed) (.parallel leftReady rightDelayed) :=
  τSTr.parallelLeft (τSTr.of_tr (.prefix _ _))

example : (communicationLTS (Name := Channel)).τSTr
    (.parallel leftDelayed rightDelayed) (.parallel leftDelayed rightReady) :=
  τSTr.parallelRight (τSTr.of_tr (.prefix _ _))

example : (communicationLTS (Name := Channel)).STr
    leftDelayed (.output .request) .nil := by
  exact _root_.Cslib.LTS.STr.tr (τSTr.of_tr (.prefix _ _))
    (.prefix _ _) Relation.ReflTransGen.refl

example : (communicationLTS (Name := Channel)).STr
    rightDelayed (.input .request) .nil := by
  exact _root_.Cslib.LTS.STr.tr (τSTr.of_tr (.prefix _ _))
    (.prefix _ _) Relation.ReflTransGen.refl

/-- Two delayed complementary actions prepare independently and then
synchronize. -/
example : (communicationLTS (Name := Channel)).τSTr
    (.parallel leftDelayed rightDelayed) (.parallel .nil .nil) := by
  apply weakComplementary_parallel
  · exact _root_.Cslib.LTS.STr.tr (τSTr.of_tr (.prefix _ _))
      (.prefix _ _) Relation.ReflTransGen.refl
  · exact _root_.Cslib.LTS.STr.tr (τSTr.of_tr (.prefix _ _))
      (.prefix _ _) Relation.ReflTransGen.refl
  · exact rfl

example {left left' right : Process} {label : Action}
    (hstep : (communicationLTS (Name := Channel)).STr left label left') :
    (communicationLTS (Name := Channel)).STr
      (.parallel left right) label (.parallel left' right) :=
  STr.parallelLeft hstep

example {left right right' : Process} {label : Action}
    (hstep : (communicationLTS (Name := Channel)).STr right label right') :
    (communicationLTS (Name := Channel)).STr
      (.parallel left right) label (.parallel left right') :=
  STr.parallelRight hstep

example {left left' right right' : Process} {leftLabel rightLabel : Action}
    (hleft : Cslib.LTS.RootedWeakStep (lts := (communicationLTS (Name := Channel)))
      left leftLabel left')
    (hright : Cslib.LTS.RootedWeakStep (lts := (communicationLTS (Name := Channel)))
      right rightLabel right')
    (hcomplementary : leftLabel.Complementary rightLabel) :
    Cslib.LTS.RootedWeakStep (lts := (communicationLTS (Name := Channel)))
      (.parallel left right) .tau (.parallel left' right') :=
  rootedComplementary_parallel hleft hright hcomplementary

example {left₁ left₂ right₁ right₂ : Process}
    (hleft : (communicationLTS (Name := Channel)).HomWeakBisimilarity left₁ left₂)
    (hright : (communicationLTS (Name := Channel)).HomWeakBisimilarity right₁ right₂) :
    (communicationLTS (Name := Channel)).HomWeakBisimilarity
      (.parallel left₁ right₁) (.parallel left₂ right₂) :=
  parallel_weaklyBisimilar_congr hleft hright

example {left₁ left₂ right₁ right₂ : Process}
    (hleft : Cslib.LTS.RootedWeaklyBisimilar
      (lts := communicationLTS (Name := Channel)) left₁ left₂)
    (hright : Cslib.LTS.RootedWeaklyBisimilar
      (lts := communicationLTS (Name := Channel)) right₁ right₂) :
    Cslib.LTS.RootedWeaklyBisimilar (lts := (communicationLTS (Name := Channel)))
      (.parallel left₁ right₁) (.parallel left₂ right₂) :=
  parallel_rootedWeaklyBisimilar_congr hleft hright

example (left right : Process) :
    (communicationLTS (Name := Channel)).HomWeakBisimilarity
      (.parallel left right) (.parallel right left) :=
  parallel_comm_weaklyBisimilar left right

example (process : Process) :
    (communicationLTS (Name := Channel)).HomWeakBisimilarity
      (.parallel .nil process) process :=
  parallel_nil_left_weaklyBisimilar process

#print axioms Cslib.CCS.Process.weakComplementary_parallel
#print axioms Cslib.CCS.Process.parallel_weaklyBisimilar_congr
#print axioms Cslib.CCS.Process.parallel_rootedWeaklyBisimilar_congr

end CslibTest.Languages.CCS.WeakParallel
