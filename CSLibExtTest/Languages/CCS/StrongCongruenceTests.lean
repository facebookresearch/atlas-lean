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

public import CSLibExt.Languages.CCS.StrongCongruence

@[expose] public section

namespace CslibTest.Languages.CCS.StrongCongruence

open Cslib.CCS Cslib.CCS.StaticProcess Cslib.LTS

inductive Channel where
  | left
  | right
  deriving DecidableEq

abbrev Process := StaticProcess Channel

def left : Process := .prefix (.input .left) .nil
def right : Process := .prefix (.input .right) .nil

example (action : Label Channel) {p q : Process} (h : lts.HomBisimilarity p q) :
    lts.HomBisimilarity (.prefix action p) (.prefix action q) :=
  prefix_congr action h

example {p₁ p₂ q₁ q₂ : Process} (hp : lts.HomBisimilarity p₁ p₂)
    (hq : lts.HomBisimilarity q₁ q₂) :
    lts.HomBisimilarity (.choice p₁ q₁) (.choice p₂ q₂) :=
  choice_congr hp hq

example {p₁ p₂ q₁ q₂ : Process} (hp : lts.HomBisimilarity p₁ p₂)
    (hq : lts.HomBisimilarity q₁ q₂) :
    lts.HomBisimilarity (.parallel p₁ q₁) (.parallel p₂ q₂) :=
  parallel_congr hp hq

example : lts.HomBisimilarity (.choice left right) (.choice right left) :=
  choice_comm left right

example : lts.HomBisimilarity (.choice .nil left) left :=
  choice_nil_left left

example : lts.HomBisimilarity (.choice left left) left :=
  choice_self left

#print axioms Cslib.CCS.StaticProcess.prefix_congr
#print axioms Cslib.CCS.StaticProcess.choice_congr
#print axioms Cslib.CCS.StaticProcess.parallel_congr
#print axioms Cslib.CCS.StaticProcess.choice_comm
#print axioms Cslib.CCS.StaticProcess.choice_nil_left
#print axioms Cslib.CCS.StaticProcess.choice_self

end CslibTest.Languages.CCS.StrongCongruence
