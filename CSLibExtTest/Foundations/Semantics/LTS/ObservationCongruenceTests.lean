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

public import CSLibExt.Foundations.Semantics.LTS.ObservationCongruence

namespace CslibTest.LTS.ObservationCongruence

open Cslib.LTS

inductive Label where
  | tau
  | visible
  deriving DecidableEq

inductive State where
  | delayed
  | ready
  | done
  deriving DecidableEq

inductive Step : State → Label → State → Prop
  | delay : Step .delayed .tau .ready
  | visible : Step .ready .visible .done

def exampleLTS : Cslib.LTS State Label := ⟨Step⟩

local instance : Cslib.HasTau Label := ⟨.tau⟩

example : Cslib.LTS.RootedWeakStep
    (lts := exampleLTS) .delayed .visible .done :=
  ⟨.ready, .done, τSTr.of_tr .delay, .visible, .refl⟩

example : exampleLTS.STr .delayed .visible .done :=
  (show Cslib.LTS.RootedWeakStep
      (lts := exampleLTS) .delayed .visible .done from
    ⟨.ready, .done, τSTr.of_tr .delay, .visible, .refl⟩).toSTr

example (state : State) : Cslib.LTS.RootedWeaklyBisimilar
    (lts := exampleLTS) state state :=
  observationCongruent_refl state

example {left right : State} (h : exampleLTS.HomBisimilarity left right) :
    Cslib.LTS.RootedWeaklyBisimilar
      (lts := exampleLTS) left right :=
  observationCongruent_of_bisimilar h

example {left right : State}
    (h : Cslib.LTS.RootedWeaklyBisimilar
      (lts := exampleLTS) left right) :
    exampleLTS.HomWeakBisimilarity left right :=
  Cslib.LTS.RootedWeaklyBisimilar.to_homWeakBisimilarity h

example {left middle right : State}
    (hleft : Cslib.LTS.RootedWeaklyBisimilar
      (lts := exampleLTS) left middle)
    (hright : Cslib.LTS.RootedWeaklyBisimilar
      (lts := exampleLTS) middle right) :
    Cslib.LTS.RootedWeaklyBisimilar
      (lts := exampleLTS) left right :=
  Cslib.LTS.RootedWeaklyBisimilar.trans hleft hright

#check Cslib.LTS.observationCongruent_equivalence

#print axioms Cslib.LTS.RootedWeaklyBisimilar.to_homWeakBisimilarity

end CslibTest.LTS.ObservationCongruence
