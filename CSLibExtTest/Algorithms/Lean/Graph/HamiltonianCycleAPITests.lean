/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Bounds

open Cslib.Algorithms.Lean.Graph

example (x y : Array Bool) (h : (verifyHamiltonianCycle x y).ret = true) :
    Nat.sqrt x.size * Nat.sqrt x.size = x.size ∧ 3 ≤ Nat.sqrt x.size := by
  have hc := (verifyHamiltonianCycle_iff x y).mp h
  exact ⟨hc.1, hc.2.1⟩

example (x y : Array Bool) (h : Nat.sqrt x.size < 3) :
    (verifyHamiltonianCycle x y).ret ≠ true := by
  intro hc
  have hm := ((verifyHamiltonianCycle_iff x y).mp hc).2.1
  exact Nat.not_le_of_lt h hm

example (x y : Array Bool) (h : (verifyHamiltonianCycle x y).ret = true) :
    ∃ G : SimpleGraph (Fin (Nat.sqrt x.size)),
      ∃ v : Fin (Nat.sqrt x.size), ∃ p : G.Walk v v, p.IsHamiltonianCycle := by
  obtain ⟨_, _, G, _, v, p, hp⟩ := verifyHamiltonianCycle_sound x y h
  exact ⟨G, v, p, hp⟩

example (x y : Array Bool) (h : (verifyHamiltonianCycle x y).ret = true) :
    y.size ≤ x.size := (verifyHamiltonianCycle_certificate_size x y h).2

example (x : Array Bool) (G : SimpleGraph (Fin (Nat.sqrt x.size)))
    (hs : Nat.sqrt x.size * Nat.sqrt x.size = x.size)
    (hG : ∀ i j, G.Adj i j ↔ x[i.val * Nat.sqrt x.size + j.val]? = some true)
    (v : Fin (Nat.sqrt x.size)) (p : G.Walk v v) (hp : p.IsHamiltonianCycle) :
    ∃ y : Array Bool, (verifyHamiltonianCycle x y).ret = true := by
  obtain ⟨y, _, hy⟩ := verifyHamiltonianCycle_complete x G hs hG v p hp
  exact ⟨y, hy⟩

example (x : Array Bool) :
    (∃ y : Array Bool, (verifyHamiltonianCycle x y).ret = true) ↔
    (let m := Nat.sqrt x.size;
      m * m = x.size ∧ 3 ≤ m ∧
        ∃ G : SimpleGraph (Fin m),
          (∀ i j, G.Adj i j ↔ x[i.val * m + j.val]? = some true) ∧
          ∃ v : Fin m, ∃ p : G.Walk v v, p.IsHamiltonianCycle) :=
  verifyHamiltonianCycle_language_iff x

example : ∃ c : Nat, 0 < c ∧ ∀ x y : Array Bool,
    (verifyHamiltonianCycle x y).time ≤ c * (x.size + y.size + 1) ^ 2 :=
  verifyHamiltonianCycle_time_le

example : ∃ c : Nat, 0 < c ∧ ∀ x y : Array Bool,
    (verifyHamiltonianCycle x y).ret = true →
      (verifyHamiltonianCycle x y).time ≤ c * (x.size + 1) ^ 2 :=
  verifyHamiltonianCycle_time_le_of_accept

#check @verifyHamiltonianCycle
#check @verifyHamiltonianCycle_iff
#check @verifyHamiltonianCycle_sound
#check @verifyHamiltonianCycle_complete
#check @verifyHamiltonianCycle_language_iff
#check @verifyHamiltonianCycle_certificate_size
#check @verifyHamiltonianCycle_time_le
#check @verifyHamiltonianCycle_time_le_of_accept

#print axioms verifyHamiltonianCycle_iff
#print axioms verifyHamiltonianCycle_sound
#print axioms verifyHamiltonianCycle_complete
#print axioms verifyHamiltonianCycle_language_iff
#print axioms verifyHamiltonianCycle_certificate_size
#print axioms verifyHamiltonianCycle_time_le
#print axioms verifyHamiltonianCycle_time_le_of_accept
