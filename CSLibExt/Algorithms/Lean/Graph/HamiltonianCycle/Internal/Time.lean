/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Basic
import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Internal.Loop
import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Internal.Decoding
import Init.Data.Array.Lemmas

/-!
# Private selected-event bounds

Bounds concern the same source's `TimeM.time` fields, counting actual bit reads,
validation comparisons and seen writes. Early rejection can only shorten each scan.
-/

namespace Cslib.Algorithms.Lean.Graph

open Cslib.Algorithms.Lean

lemma time_list_findSomeM_le {α β : Type} (f : α → TimeM Nat (Option β))
    (xs : List α) (c : Nat) (hc : ∀ a ∈ xs, (f a).time ≤ c) :
    (xs.findSomeM? f).time ≤ xs.length * c := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hc a (by simp)
    have ht := ih (fun b hb => hc b (by simp [hb]))
    rw [List.findSomeM?_cons]
    cases hf : (f a).ret <;> simp [TimeM.time_bind, hf, Nat.succ_mul]
    all_goals omega

lemma time_forIn_list_le {α β : Type} (xs : List α) (b : β)
    (f : α → β → TimeM Nat (ForInStep β)) (c : Nat)
    (hc : ∀ a ∈ xs, ∀ s : β, (f a s).time ≤ c) :
    (forIn xs b f).time ≤ xs.length * c := by
  induction xs generalizing b with
  | nil => simp
  | cons a xs ih =>
    have ha := hc a List.mem_cons_self b
    have ht (s : β) := ih s (fun z hz => hc z (List.mem_cons_of_mem _ hz))
    rw [List.forIn_cons, TimeM.time_bind]
    cases hf : (f a b).ret with
    | done s =>
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul, TimeM.time_pure]
      omega
    | yield s =>
      have hs := ht s
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

lemma sourceStep_time_le (x y : Array Bool) (m w : Nat) (i : Fin m)
    (s : Option Bool × Vector Bool m × Option (Fin m) × Option (Fin m))
    (hy : y.size = m * w) : (sourceStep x y m w i s).time ≤ w + 5 := by
  rcases s with ⟨flag, seen, first, previous⟩
  unfold sourceStep
  rw [countedBits_word y m w i.val hy i.isLt]
  dsimp only
  simp only [TimeM.time_bind, TimeM.time_tick]
  split_ifs <;> cases previous <;>
    simp_all only [graphRead, TimeM.time_bind, TimeM.time_pure,
      TimeM.time_tick, TimeM.ret_bind, TimeM.ret_pure, Nat.add_zero]
  all_goals (try split_ifs) <;>
    (try simp_all only [Bool.not_eq_true, Bool.false_eq_true, ↓reduceIte,
      TimeM.time_pure, Nat.add_zero]) <;> omega

lemma sourceFinish_time_le (x : Array Bool) (m : Nat)
    (s : Option Bool × Vector Bool m × Option (Fin m) × Option (Fin m)) :
    (sourceFinish x m s).time ≤ 2 := by
  rcases s with ⟨flag, seen, first, previous⟩
  cases flag <;> cases first <;> cases previous <;>
    simp [sourceFinish, graphRead, TimeM.time_bind]

lemma time_array_findSomeM_le {α β : Type} (f : α → TimeM Nat (Option β))
    (xs : Array α) (c : Nat) (hc : ∀ a : α, (f a).time ≤ c) :
    (xs.findSomeM? f).time ≤ xs.size * c := by
  rw [← Array.findSomeM?_toList]
  simpa only [Array.length_toList] using time_list_findSomeM_le f xs.toList c
    (fun a _ => hc a)

lemma symmetry_row_time_le (x : Array Bool) (m : Nat) (i : Fin m) :
    ((Array.ofFn fun j : Fin m => j).findSomeM? (fun j : Fin m => do
      if i.val < j.val then
        let a ← graphRead x (i.val * m + j.val)
        let b ← graphRead x (j.val * m + i.val)
        TimeM.tick 1
        pure (if a != b then some true else none)
      else pure none)).time ≤ m * 3 := by
  have h := time_array_findSomeM_le
    (fun j : Fin m => do
      if i.val < j.val then
        let a ← graphRead x (i.val * m + j.val)
        let b ← graphRead x (j.val * m + i.val)
        TimeM.tick 1
        pure (if a != b then some true else none)
      else pure none) (Array.ofFn fun j : Fin m => j) 3 (fun j => by
      split_ifs <;> simp [graphRead, TimeM.time_bind])
  simpa only [Array.size_ofFn] using h

lemma validateGraph_time_le (x : Array Bool) (m : Nat) :
    (validateGraph x m).time ≤ 1 + m * 2 + m * (m * 3) := by
  let indices := Array.ofFn fun i : Fin m => i
  let diag := fun i : Fin m => do
    let bit ← graphRead x (i.val * m + i.val)
    TimeM.tick 1
    pure (if bit then some true else none)
  let row := fun i : Fin m => indices.findSomeM? (fun j : Fin m => do
    if i.val < j.val then
      let a ← graphRead x (i.val * m + j.val)
      let b ← graphRead x (j.val * m + i.val)
      TimeM.tick 1
      pure (if a != b then some true else none)
    else pure none)
  have hd : (indices.findSomeM? diag).time ≤ m * 2 := by
    simpa only [indices, Array.size_ofFn] using
      time_array_findSomeM_le diag indices 2 (fun i => by
        simp [diag, graphRead, TimeM.time_bind])
  have hr : ∀ i : Fin m, (row i).time ≤ m * 3 := fun i => symmetry_row_time_le x m i
  have hs : (indices.findSomeM? row).time ≤ m * (m * 3) := by
    simpa only [indices, Array.size_ofFn] using time_array_findSomeM_le row indices (m * 3) hr
  by_cases hg : m * m = x.size
  · simp only [validateGraph, hg, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      TimeM.time_bind, TimeM.time_tick]
    change 1 + ((indices.findSomeM? diag).time +
      (if (indices.findSomeM? diag).ret.isSome then pure false else do
        let bad ← indices.findSomeM? row
        pure (!bad.isSome)).time) ≤ _
    split_ifs <;> simp only [TimeM.time_pure, TimeM.time_bind, Nat.add_zero] <;> omega
  · simp [validateGraph, hg]
    omega

lemma sourceLoop_time_le (x y : Array Bool) (m w : Nat)
    (s : Option Bool × Vector Bool m × Option (Fin m) × Option (Fin m))
    (hy : y.size = m * w) :
    (forIn (Array.ofFn fun i : Fin m => i) s (sourceStep x y m w)).time ≤ m * (w + 5) := by
  rw [← Array.forIn_toList, Array.toList_ofFn]
  simpa only [List.length_ofFn] using time_forIn_list_le
    (List.ofFn fun i : Fin m => i) s (sourceStep x y m w) (w + 5)
    (fun i _ s => sourceStep_time_le x y m w i s hy)

lemma verify_time_le_scans (x y : Array Bool) :
    (verifyHamiltonianCycle x y).time ≤ (validateGraph x (Nat.sqrt x.size)).time +
      2 + Nat.sqrt x.size * (Nat.clog 2 (Nat.sqrt x.size) + 5) + 2 := by
  let m := Nat.sqrt x.size
  let w := Nat.clog 2 m
  by_cases hy : y.size = m * w
  · have hl := sourceLoop_time_le x y m w
      (none, Vector.replicate m false, none, none) hy
    have hf := sourceFinish_time_le x m
      (forIn (Array.ofFn fun i : Fin m => i)
        (none, Vector.replicate m false, none, none) (sourceStep x y m w)).ret
    dsimp only [m, w] at hy hl hf
    rw [verifyHamiltonianCycle_eq]
    simp only [TimeM.time_bind, bne_iff_ne]
    split_ifs <;>
      simp_all only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, Nat.add_zero] <;> omega
  · dsimp only [m, w] at hy
    rw [verifyHamiltonianCycle_eq]
    simp only [TimeM.time_bind, bne_iff_ne]
    split_ifs <;>
      simp_all only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, Nat.add_zero] <;> omega

lemma verify_time_le_input (x y : Array Bool) :
    (verifyHamiltonianCycle x y).time ≤ 11 * x.size + 5 := by
  have h := verify_time_le_scans x y
  have hv := validateGraph_time_le x (Nat.sqrt x.size)
  have hm := Nat.sqrt_le_self x.size
  have hs := Nat.sqrt_le x.size
  have hw : Nat.clog 2 (Nat.sqrt x.size) ≤ Nat.sqrt x.size :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hmw := Nat.mul_le_mul_left (Nat.sqrt x.size) hw
  simp only [Nat.mul_add] at h
  rw [← Nat.mul_assoc] at hv
  omega

end Cslib.Algorithms.Lean.Graph
