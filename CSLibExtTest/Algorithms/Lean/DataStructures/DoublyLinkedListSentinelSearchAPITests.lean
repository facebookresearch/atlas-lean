/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Sentinel.Search

/-!
# Ordinary sentinel-search API consumers

The five authored API roles use only canonical types and ordinary imports.
Satellite payloads need neither equality nor ordering, including function values.
-/

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.DoublyLinkedList

universe u v

example {Key : Type u} {Satellite : Type v} {capacity : Nat} [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (valid : ∃ ids, CircularRepresents store s ids) :
    TimeM Nat (Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity ×
      Option (Fin capacity)) := listSearchSentinel store s key valid

example {Key : Type u} {Satellite : Type v} {capacity : Nat} [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (valid : ∃ ids, CircularRepresents store s ids)
    (z : Fin capacity) :
    (listSearchSentinel store s key valid).ret.1.get z =
      if z = s then
        (store.get z).map (fun node => { node with payload := (key, node.payload.2) })
      else store.get z := listSearchSentinel_get store s key valid z

example {Key : Type u} {Satellite : Type v} {capacity : Nat} [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (ids : List (Fin capacity))
    (rep : CircularRepresents store s ids) :
    CircularRepresents (listSearchSentinel store s key ⟨ids, rep⟩).ret.1 s ids :=
  listSearchSentinel_circular store s key ids rep

example {Key : Type u} {Satellite : Type v} {capacity : Nat} [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (ids : List (Fin capacity))
    (rep : CircularRepresents store s ids) :
    (listSearchSentinel store s key ⟨ids, rep⟩).ret.2 =
      ids.find? (fun x => decide ((store.get x).map (fun node => node.payload.1) = some key)) :=
  listSearchSentinel_ret store s key ids rep

example {Key : Type u} {Satellite : Type v} {capacity : Nat} [DecidableEq Key]
    (store : Vector (Option (Node (Key × Satellite) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Key) (ids : List (Fin capacity))
    (rep : CircularRepresents store s ids) :
    (listSearchSentinel store s key ⟨ids, rep⟩).time =
      2 * (ids.findIdx? (fun x => decide
        ((store.get x).map (fun node => node.payload.1) = some key))).getD ids.length + 4 :=
  listSearchSentinel_time store s key ids rep

example {capacity : Nat}
    (store : Vector (Option (Node (Int × (Nat → Nat)) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Int) (valid : ∃ ids, CircularRepresents store s ids) :
    TimeM Nat (Vector (Option (Node (Int × (Nat → Nat)) (Fin capacity))) capacity ×
      Option (Fin capacity)) := listSearchSentinel store s key valid

example {capacity : Nat}
    (store : Vector (Option (Node (Int × String) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Int) (ids : List (Fin capacity))
    (rep : CircularRepresents store s ids) :
    (listSearchSentinel store s key ⟨ids, rep⟩).ret.2 = none ↔
      ∀ x ∈ ids, (store.get x).map (fun node => node.payload.1) ≠ some key := by
  rw [listSearchSentinel_ret store s key ids rep]
  simp

example {capacity : Nat}
    (store : Vector (Option (Node (Int × String) (Fin capacity))) capacity)
    (s : Fin capacity) (key : Int) (ids : List (Fin capacity))
    (rep : CircularRepresents store s ids) (x : Fin capacity) :
    (listSearchSentinel store s key ⟨ids, rep⟩).ret.2 = some x ↔
      (store.get x).map (fun node => node.payload.1) = some key ∧
        ∃ before after, ids = before ++ x :: after ∧
          ∀ y ∈ before, (store.get y).map (fun node => node.payload.1) ≠ some key := by
  rw [listSearchSentinel_ret store s key ids rep]
  simpa using (List.find?_eq_some_iff_append (xs := ids) (b := x) (p := fun y => decide
    ((store.get y).map (fun node => node.payload.1) = some key)))
