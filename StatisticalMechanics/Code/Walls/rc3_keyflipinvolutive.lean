/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































import Code.Inequalities.PerOrbitCardClose

open Finset
open scoped StatMech

namespace StatMech.Walls

variable {α : Type*} [Fintype α] [DecidableEq α]



omit [Fintype α] [DecidableEq α] in




theorem rc3_flip_involutive (d : α → Bool) :
    Function.Involutive (StatMech.poc_flip d : ConfigSpace α → ConfigSpace α) := by
  intro ω
  funext a
  simp only [StatMech.poc_flip]
  cases d a <;> simp

omit [Fintype α] [DecidableEq α] in


@[simp] theorem rc3_flip_flip (d : α → Bool) (ω : ConfigSpace α) :
    StatMech.poc_flip d (StatMech.poc_flip d ω) = ω :=
  rc3_flip_involutive d ω







omit [Fintype α] [DecidableEq α] in




theorem rc3_keyFlip_involutive (k : ConfigSpace α × ConfigSpace α) :
    Function.Involutive (StatMech.poc_keyFlip k : ConfigSpace α → ConfigSpace α) := by
  simpa only [StatMech.poc_keyFlip] using
    rc3_flip_involutive (fun a => decide (k.1 a ≠ k.2 a))

omit [Fintype α] [DecidableEq α] in




@[simp] theorem rc3_keyFlip_keyFlip (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α) :
    StatMech.poc_keyFlip k (StatMech.poc_keyFlip k ω) = ω :=
  rc3_keyFlip_involutive k ω

omit [Fintype α] [DecidableEq α] in

theorem rc3_keyFlip_injective (k : ConfigSpace α × ConfigSpace α) :
    Function.Injective (StatMech.poc_keyFlip k : ConfigSpace α → ConfigSpace α) :=
  (rc3_keyFlip_involutive k).injective

omit [Fintype α] [DecidableEq α] in

theorem rc3_keyFlip_bijective (k : ConfigSpace α × ConfigSpace α) :
    Function.Bijective (StatMech.poc_keyFlip k : ConfigSpace α → ConfigSpace α) :=
  (rc3_keyFlip_involutive k).bijective







omit [Fintype α] [DecidableEq α] in


theorem rc3_keyFlip_top_involutive (ω : ConfigSpace α) :
    StatMech.poc_keyFlip (StatMech.poc_topKey : ConfigSpace α × ConfigSpace α)
      (StatMech.poc_keyFlip (StatMech.poc_topKey : ConfigSpace α × ConfigSpace α) ω) = ω :=
  rc3_keyFlip_keyFlip StatMech.poc_topKey ω

end StatMech.Walls
