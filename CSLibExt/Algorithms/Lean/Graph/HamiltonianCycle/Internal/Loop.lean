/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Basic
import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Internal.Decoding
import Init.Data.Array.Lemmas
import Init.Data.List.Control

/-!
# Private carried-state proof for binary certificate verification

`sourceStep` is the actual compiler-lowered loop body, not another verifier.
The equation below binds it to the unchanged executor, including both result and cost.
The saved vector, first identity and previous identity are always carried together.
-/

namespace Cslib.Algorithms.Lean.Graph

open Cslib.Algorithms.Lean

@[no_expose] def sourceStep (x y : Array Bool) (m w : Nat) (i : Fin m)
    (s : Option Bool × Vector Bool m × Option (Fin m) × Option (Fin m)) :
    TimeM Nat (ForInStep (Option Bool × Vector Bool m × Option (Fin m) × Option (Fin m))) := do
  let seen := s.2.1
  let first := s.2.2.1
  let previous := s.2.2.2
  let value ← countedBits y ((i.val + 1) * w) (i.val * w)
  TimeM.tick 1
  if h : value < m then
    let vertex : Fin m := ⟨value, h⟩
    TimeM.tick 1
    if seen[vertex] then return .done (some false, seen, first, previous)
    TimeM.tick 1
    let seen := seen.set value true h
    if let some p := previous then
      let present ← graphRead x (p.val * m + value)
      TimeM.tick 1
      if !present then return .done (some false, seen, first, previous)
      return .yield (none, seen, first, some vertex)
    else
      return .yield (none, seen, some vertex, some vertex)
  else
    return .done (some false, seen, first, previous)

@[no_expose] def sourceFinish (x : Array Bool) (m : Nat)
    (s : Option Bool × Vector Bool m × Option (Fin m) × Option (Fin m)) :
    TimeM Nat Bool :=
  match s.1 with
  | some r => pure r
  | none =>
    match s.2.2.1, s.2.2.2 with
    | some a, some b => do
      let present ← graphRead x (b.val * m + a.val)
      TimeM.tick 1
      pure present
    | _, _ => pure false

lemma verifyHamiltonianCycle_eq (x y : Array Bool) :
    verifyHamiltonianCycle x y = (do
      let m := Nat.sqrt x.size
      let valid ← validateGraph x m
      if !valid then return false
      TimeM.tick 1
      if m < 3 then return false
      let w := Nat.clog 2 m
      TimeM.tick 1
      if y.size != m * w then return false
      let s ← forIn (Array.ofFn fun i : Fin m => i)
        (none, Vector.replicate m false, none, none) (sourceStep x y m w)
      sourceFinish x m s) := by
  unfold verifyHamiltonianCycle sourceStep sourceFinish
  dsimp only
  congr 10
  funext valid
  split_ifs <;> congr 10
  funext ignored
  congr 10
  funext ignored₂
  congr 10
  funext s
  rcases s with ⟨flag, seen, first, previous⟩
  cases flag with
  | some r => rfl
  | none => cases first <;> cases previous <;> rfl

lemma ret_forIn_list {α β : Type} (xs : List α) (b : β)
    (f : α → β → TimeM Nat (ForInStep β)) :
    (forIn xs b f).ret =
      (forIn xs b (fun a s => pure (f a s).ret) : Id β).run := by
  induction xs generalizing b with
  | nil => simp only [List.forIn_nil, TimeM.ret_pure]; rfl
  | cons a xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    simp only [TimeM.ret_bind]
    cases (f a b).ret <;> simp [TimeM.ret_pure, ih]

lemma sourceStep_ret (x y : Array Bool) (m w : Nat) (i : Fin m)
    (seen : Vector Bool m) (first previous : Option (Fin m)) (hsize : y.size = m * w) :
    (sourceStep x y m w i (none, seen, first, previous)).ret =
      let value := Nat.ofDigits 2
        ((y.toList.drop (i.val * w)).take w |>.map fun bit => if bit then 1 else 0)
      if h : value < m then
        let vertex : Fin m := ⟨value, h⟩
        if seen[vertex] then .done (some false, seen, first, previous)
        else
          let seen := seen.set value true h
          match previous with
          | some p =>
            if !(x[p.val * m + value]?.getD false) then
              .done (some false, seen, first, previous)
            else .yield (none, seen, first, some vertex)
          | none => .yield (none, seen, some vertex, some vertex)
      else .done (some false, seen, first, previous) := by
  unfold sourceStep
  rw [countedBits_word y m w i.val hsize i.isLt]
  dsimp only
  simp only [TimeM.ret_bind]
  split_ifs <;> cases previous <;>
    simp_all only [graphRead, TimeM.ret_bind, TimeM.ret_pure]
  split_ifs <;> simp_all only [Bool.false_eq_true, ↓reduceIte, TimeM.ret_pure]

lemma accept_guards (x y : Array Bool) (h : (verifyHamiltonianCycle x y).ret = true) :
    (validateGraph x (Nat.sqrt x.size)).ret = true ∧
      3 ≤ Nat.sqrt x.size ∧ y.size = Nat.sqrt x.size * Nat.clog 2 (Nat.sqrt x.size) := by
  rw [verifyHamiltonianCycle_eq] at h
  simp only [TimeM.ret_bind] at h
  split_ifs at h <;>
    simp_all only [TimeM.ret_bind, TimeM.ret_pure, Bool.false_eq_true, Bool.not_eq_true,
      bne_iff_ne, not_lt, not_not, and_true]
  cases hv : (validateGraph x (Nat.sqrt x.size)).ret <;> simp_all

end Cslib.Algorithms.Lean.Graph
