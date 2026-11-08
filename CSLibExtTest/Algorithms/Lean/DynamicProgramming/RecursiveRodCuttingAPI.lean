/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.RecursiveRodCutting

set_option autoImplicit false

open Cslib.Algorithms.Lean.RodCutting

universe u

example {α : Type u} [AddCommMonoid α] [LinearOrder α] {n : Nat}
    (prices : Vector α n) : Cslib.Algorithms.Lean.TimeM Nat α := recursiveCutRod prices

example {α : Type u} [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α]
    {n : Nat} (prices : Vector α n) :
    IsGreatest (Set.range fun parts : Composition n =>
      compositionRevenue prices parts le_rfl) (recursiveCutRod prices).ret :=
  recursiveCutRod_correct prices

example {α : Type u} [AddCommMonoid α] [LinearOrder α] {n : Nat}
    (prices : Vector α n) : (recursiveCutRod prices).time = 2 ^ n :=
  recursiveCutRod_time prices

#check recursiveCutRod
#check recursiveCutRod_correct
#check recursiveCutRod_time

#print axioms recursiveCutRod
#print axioms recursiveCutRod_correct
#print axioms recursiveCutRod_time
