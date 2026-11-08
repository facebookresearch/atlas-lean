/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Deque

/-!
# Tests for the two-list deque API

Client examples over empty, singleton, front-only, back-only, and mixed
representations, exercising both reversal branches of `popFront`/`popBack`
and the public contents/peek theorems.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DequeTests

open Cslib.Algorithms.Lean

example : (Deque.empty : Deque Nat).peekFront = none := rfl
example : (Deque.empty : Deque Nat).peekBack = none := rfl
example : (Deque.empty : Deque Nat).popFront = none := rfl
example : (Deque.empty : Deque Nat).popBack = none := rfl
example : Deque.contents (Deque.empty : Deque Nat) = [] := rfl

/-- A deque built only by `pushBack`, so `front` stays empty. -/
public def backOnly : Deque Nat :=
  (Deque.empty.pushBack 1).pushBack 2 |>.pushBack 3

/-- A deque built only by `pushFront`, so `back` stays empty. -/
public def frontOnly : Deque Nat :=
  (Deque.empty.pushFront 3).pushFront 2 |>.pushFront 1

/-- A mixed deque using both ends. -/
public def mixed : Deque Nat :=
  ((Deque.empty.pushBack 2).pushFront 1).pushBack 3

example : Deque.contents backOnly = [1, 2, 3] := rfl
example : Deque.contents frontOnly = [1, 2, 3] := rfl
example : Deque.contents mixed = [1, 2, 3] := rfl

-- Peeking a back-only deque exercises the `getLast?` traversal branch.
example : backOnly.peekFront = some 1 := rfl
example : backOnly.peekBack = some 3 := rfl
example : frontOnly.peekFront = some 1 := rfl
example : frontOnly.peekBack = some 3 := rfl

-- Popping a back-only deque exercises the reversal branch of `popFront`.
example : backOnly.popFront.map Prod.fst = some 1 := rfl
example : frontOnly.popBack.map Prod.fst = some 3 := rfl

example (d : Deque Nat) : d.peekFront = (Deque.contents d).head? :=
  Deque.peekFront_eq_head d

example (d : Deque Nat) : d.peekBack = (Deque.contents d).getLast? :=
  Deque.peekBack_eq_getLast d

example : mixed.popFront.map (fun p => (p.1, Deque.contents p.2)) = some (1, [2, 3]) := rfl
example : mixed.popBack.map (fun p => (p.1, Deque.contents p.2)) = some (3, [1, 2]) := rfl

end Cslib.Algorithms.Lean.DequeTests
