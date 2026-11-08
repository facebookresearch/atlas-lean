/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.IndexedMinQueue
public import Mathlib.Basic.Real.Basic

@[expose] public section

noncomputable section

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.IndexedMinQueue

universe u

#check IndexedMinQueue
#check empty
#check Cslib.Algorithms.Lean.IndexedMinQueue.insert
#check member
#check extractMin
#check decreaseKey
#check position_valid
#check position_eq_none_iff
#check empty_position
#check insert_eq_none_iff
#check insert_ret
#check extractMin_eq_none_iff
#check extractMin_ret
#check decreaseKey_eq_none_iff
#check decreaseKey_ret
#check member_ret
#check member_time
#check insert_time
#check extractMin_time
#check decreaseKey_time
#check repeated_insert_time

example : IndexedMinQueue Real 4 := empty 4

example (q : IndexedMinQueue Real 4) (v : Fin 4) :
    TimeM (Fin 5 → Nat) Bool := member q v

example (q : IndexedMinQueue Real 4) (v : Fin 4) :
    TimeM (Fin 5 → Nat) (Option (IndexedMinQueue Real 4)) :=
  insert q v ⊤

example (q : IndexedMinQueue Real 4) (v : Fin 4) (key : Real) :
    TimeM (Fin 5 → Nat) (Option (IndexedMinQueue Real 4)) :=
  decreaseKey q v key

example (q : IndexedMinQueue Real 4) :
    TimeM (Fin 5 → Nat)
      (Option ((WithTop Real ×ₗ Fin 4) × IndexedMinQueue Real 4)) :=
  extractMin q

example (q : IndexedMinQueue Real 4) (v : Fin 4) :
    (member q v).time = fun c : Fin 5 => if c = 2 then 1 else 0 :=
  member_time q v

open scoped BigOperators

example {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v i : Fin n)
    (h : q.position[v] = some i) : i.val < q.heap.data.size :=
  position_valid q v i h

example {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) :
    q.position[v] = none ↔
      ¬ ∃ entry ∈ q.heap.data.toList, (ofLex entry).2 = v :=
  position_eq_none_iff q v

example {W : Type u} [LinearOrder W] {n : Nat}
    (v : Fin n) : (empty (W := W) n).position[v] = none :=
  empty_position v

example {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) (key : WithTop W) :
    (insert q v key).ret = none ↔ q.position[v].isSome = true :=
  insert_eq_none_iff q v key

example {W : Type u} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (v : Fin n) (key : WithTop W)
    (h : (insert q v key).ret = some q') :
    q'.heap = q.heap.push (toLex (key, v)) ∧
      (∃ (i : Fin n) (hi : i.val < q'.heap.data.size),
        q'.position[v] = some i ∧ q'.heap.data[i.val]'hi = toLex (key, v)) ∧
      ∀ w : Fin n, w ≠ v → q'.position[w].isSome = q.position[w].isSome :=
  insert_ret q q' v key h

example {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) :
    (extractMin q).ret = none ↔ q.heap.data.size = 0 :=
  extractMin_eq_none_iff q

example {W : Type u} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (h : (extractMin q).ret = some (entry, q')) :
    q.heap.extractMin = some (entry, q'.heap) ∧
      q'.position[(ofLex entry).2] = none ∧
      ∀ w : Fin n, w ≠ (ofLex entry).2 →
        q'.position[w].isSome = q.position[w].isSome :=
  extractMin_ret q q' entry h

example {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) (key : W) :
    (decreaseKey q v key).ret = none ↔
      q.position[v] = none ∨
        ∃ (i : Fin n) (hi : i.val < q.heap.data.size),
          q.position[v] = some i ∧
            ¬ (↑key : WithTop W) < (ofLex (q.heap.data[i.val]'hi)).1 :=
  decreaseKey_eq_none_iff q v key

example {W : Type u} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (v : Fin n) (key : W)
    (h : (decreaseKey q v key).ret = some q') :
    (∃ (i : Fin n) (hi : i.val < q.heap.data.size),
      q.position[v] = some i ∧
        (↑key : WithTop W) < (ofLex (q.heap.data[i.val]'hi)).1 ∧
        q'.heap.data = siftUp
          (q.heap.data.set i.val (toLex ((↑key : WithTop W), v)) hi) i.val) ∧
      ∀ w : Fin n, q'.position[w].isSome = q.position[w].isSome :=
  decreaseKey_ret q q' v key h

example {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) :
    (member q v).ret = q.position[v].isSome :=
  member_ret q v

example {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) :
    (member q v).time = fun c : Fin 5 => if c = 2 then 1 else 0 :=
  member_time q v

example {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) (key : WithTop W) (c : Fin 5) :
    (insert q v key).time c ≤ 20 * (Nat.log2 (q.heap.data.size + 1) + 1) :=
  insert_time q v key c

example {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (c : Fin 5) :
    (extractMin q).time c ≤ 20 * (Nat.log2 (q.heap.data.size + 1) + 1) :=
  extractMin_time q c

example {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) (key : W) (c : Fin 5) :
    (decreaseKey q v key).time c ≤ 20 * (Nat.log2 (q.heap.data.size + 1) + 1) :=
  decreaseKey_time q v key c

example {W : Type u} [LinearOrder W] {n : Nat}
    (qs : Fin (n + 1) → IndexedMinQueue W n) (keys : Fin n → WithTop W)
    (hstart : qs 0 = empty (W := W) n)
    (hsteps : ∀ i : Fin n,
      (insert (qs i.castSucc) i (keys i)).ret = some (qs i.succ))
    (c : Fin 5) :
    (∑ i : Fin n, (insert (qs i.castSucc) i (keys i)).time c) ≤
      20 * n * (Nat.log2 (n + 1) + 1) :=
  repeated_insert_time qs keys hstart hsteps c

end
