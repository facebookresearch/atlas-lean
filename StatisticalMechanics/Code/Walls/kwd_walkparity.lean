/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.Ising.KramersWannierGeneral

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech

namespace Walls








section Handshake

variable {V : Type*} (Gp : SimpleGraph V) (s : V → Bool)




def walkDis : {x y : V} → Gp.Walk x y → ℕ
  | _, _, .nil => 0
  | _, _, .cons (u := u) (v := v) _ p => (if s u ≠ s v then 1 else 0) + walkDis p

@[simp] theorem walkDis_nil {x : V} : walkDis Gp s (.nil : Gp.Walk x x) = 0 := rfl

@[simp] theorem walkDis_cons {u v w : V} (h : Gp.Adj u v) (p : Gp.Walk v w) :
    walkDis Gp s (.cons h p) = (if s u ≠ s v then 1 else 0) + walkDis Gp s p := rfl

variable {Gp s}







theorem walkDis_parity {x y : V} (p : Gp.Walk x y) :
    walkDis Gp s p % 2 = (if s x ≠ s y then 1 else 0) := by
  induction p with
  | nil => simp
  | @cons u v w h q ih =>
    simp only [walkDis_cons]
    rw [Nat.add_mod, ih]
    cases hu : s u <;> cases hv : s v <;> cases hw : s w <;> simp_all






theorem walkDis_closed_even {x : V} (p : Gp.Walk x x) :
    walkDis Gp s p % 2 = 0 := by
  rw [walkDis_parity]; simp




theorem closedWalk_even_disagreements {x : V} (p : Gp.Walk x x) :
    Even (walkDis Gp s p) := by
  rw [Nat.even_iff]; exact walkDis_closed_even p





theorem walkDis_eq_darts_sum {x y : V} (p : Gp.Walk x y) :
    walkDis Gp s p
      = (p.darts.map (fun d => if s d.fst ≠ s d.snd then 1 else 0)).sum := by
  induction p with
  | nil => simp
  | @cons u v w h q ih =>
    simp only [walkDis_cons, SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, ih]




theorem closedWalk_even_dartsSum {x : V} (p : Gp.Walk x x) :
    Even (p.darts.map (fun d => if s d.fst ≠ s d.snd then 1 else 0)).sum := by
  rw [← walkDis_eq_darts_sum]; exact closedWalk_even_disagreements p

end Handshake









section Faithful

variable {V : Type*} (Gp : SimpleGraph V) (s : V → Bool)




theorem walkDis_eq_ising {x y : V} (p : Gp.Walk x y) :
    walkDis Gp s p = StatMech.Ising.walkDis Gp s p := by
  induction p with
  | nil => rfl
  | @cons u v w h q ih => simp only [walkDis_cons, StatMech.Ising.walkDis, ih]






theorem closedWalk_even_disagreements_ising {x : V} (p : Gp.Walk x x) :
    StatMech.Ising.walkDis Gp s p % 2 = 0 := by
  rw [← walkDis_eq_ising]; exact walkDis_closed_even p

end Faithful

end Walls

end StatMech
