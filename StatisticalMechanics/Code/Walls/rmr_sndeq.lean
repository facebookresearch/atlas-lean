/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































import Code.Inequalities.PerOrbitCardClose

open Finset

namespace StatMech.Walls

open ConfigSpace StatMech

variable {α : Type*}







def rmr_flip (d : α → Bool) (ω : ConfigSpace α) : ConfigSpace α :=
  fun a => if d a then !ω a else ω a


def rmr_keyFlip (k : ConfigSpace α × ConfigSpace α) : ConfigSpace α → ConfigSpace α :=
  rmr_flip (fun a => decide (k.1 a ≠ k.2 a))









theorem rmr_snd_eq (p : ConfigSpace α × ConfigSpace α) (k : ConfigSpace α × ConfigSpace α)
    (hk : orbitKey p = k) : p.2 = rmr_keyFlip k p.1 := by
  funext a
  
  have hor := congrFun (congrArg Prod.fst hk) a
  have hand := congrFun (congrArg Prod.snd hk) a
  simp only [orbitKey] at hor hand
  simp only [rmr_keyFlip, rmr_flip, ← hor, ← hand]
  
  revert hor hand
  cases hp1 : p.1 a <;> cases hp2 : p.2 a <;> simp_all




theorem rmr_keyFlip_eq_poc (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α) :
    rmr_keyFlip k ω = poc_keyFlip k ω := by
  funext a
  simp only [rmr_keyFlip, rmr_flip, poc_keyFlip, poc_flip]








theorem rmr_keyFlip_fst (p : ConfigSpace α × ConfigSpace α) (k : ConfigSpace α × ConfigSpace α)
    (hk : orbitKey p = k) : p.1 = rmr_keyFlip k p.2 := by
  funext a
  have hor := congrFun (congrArg Prod.fst hk) a
  have hand := congrFun (congrArg Prod.snd hk) a
  simp only [orbitKey] at hor hand
  simp only [rmr_keyFlip, rmr_flip, ← hor, ← hand]
  revert hor hand
  cases hp1 : p.1 a <;> cases hp2 : p.2 a <;> simp_all



theorem rmr_keyFlip_keyFlip (p : ConfigSpace α × ConfigSpace α) (k : ConfigSpace α × ConfigSpace α)
    (hk : orbitKey p = k) : rmr_keyFlip k (rmr_keyFlip k p.1) = p.1 := by
  rw [← rmr_snd_eq p k hk, ← rmr_keyFlip_fst p k hk]

end StatMech.Walls
