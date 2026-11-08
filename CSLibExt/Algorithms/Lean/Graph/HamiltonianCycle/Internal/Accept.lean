/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Internal.Trace

/-!
# Private final closing-edge bridge

The finishing check reads the carried last and first identities of the actual
traversal. It does not run an independent certificate validator.
-/

namespace Cslib.Algorithms.Lean.Graph

open Cslib.Algorithms.Lean

lemma sourceFinish_prefix_iff (x : Array Bool) (m : Nat) (vs : List (Fin m)) :
    (sourceFinish x m (prefixState vs)).ret = true ↔
      ∃ a b, vs.head? = some a ∧ vs.getLast? = some b ∧
        x[b.val * m + a.val]?.getD false = true := by
  unfold sourceFinish prefixState
  cases vs.head? <;> cases vs.getLast?
  · simp only [TimeM.ret_pure, Bool.false_eq_true, reduceCtorEq, false_and,
      and_self, exists_false]
  · simp only [TimeM.ret_pure, Bool.false_eq_true, reduceCtorEq, Option.some.injEq,
      false_and, exists_false]
  · simp only [TimeM.ret_pure, Bool.false_eq_true, Option.some.injEq, reduceCtorEq,
      false_and, and_false, exists_false]
  · simp only [graphRead, bind_pure_comp, bind_map_left, TimeM.ret_bind, TimeM.ret_map,
      Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, exists_eq_left']

lemma sourceFinish_accept_flag (x : Array Bool) (m : Nat)
    (s : Option Bool × Vector Bool m × Option (Fin m) × Option (Fin m))
    (hf : s.1 = none ∨ s.1 = some false) (ha : (sourceFinish x m s).ret = true) :
    s.1 = none := by
  rcases hf with hf | hf
  · exact hf
  · have heq : (sourceFinish x m s).ret = false := by
      unfold sourceFinish
      rw [hf]
      rfl
    rw [heq] at ha
    cases ha

lemma sourceLoop_accept_iff (x y : Array Bool) (m w : Nat) (hsize : y.size = m * w)
    (indices : List (Fin m)) :
    (sourceFinish x m (forIn indices (prefixState []) (sourceStep x y m w)).ret).ret =
      true ↔
      ∃ us : List (Fin m),
        List.Forall₂ (fun i v => Nat.ofDigits 2
          ((y.toList.drop (i.val * w)).take w |>.map fun bit => if bit then 1 else 0) =
          v.val) indices us ∧ us.Nodup ∧
        us.IsChain (fun a b => x[a.val * m + b.val]?.getD false = true) ∧
        ∃ a b, us.head? = some a ∧ us.getLast? = some b ∧
          x[b.val * m + a.val]?.getD false = true := by
  constructor
  · intro h
    have hf := forIn_flags x y m w indices (prefixState []) rfl
    have hn := sourceFinish_accept_flag x m _ hf h
    obtain ⟨us, hs, halign, hnd, hch⟩ :=
      forIn_prefix_sound x y m w hsize indices [] (by simp) .nil _ rfl hn
    simp only [List.nil_append] at hs hnd hch
    rw [hs, sourceFinish_prefix_iff] at h
    exact ⟨us, halign, hnd, hch, h⟩
  · rintro ⟨us, halign, hnd, hch, hclose⟩
    have hs := forIn_prefix_complete x y m w hsize indices us [] halign
      (by simpa using hnd) (by simpa using hch)
    simp only [List.nil_append] at hs
    rw [hs, sourceFinish_prefix_iff]
    exact hclose

lemma verify_ret_of_guards (x y : Array Bool)
    (hv : (validateGraph x (Nat.sqrt x.size)).ret = true)
    (hm : 3 ≤ Nat.sqrt x.size)
    (hy : y.size = Nat.sqrt x.size * Nat.clog 2 (Nat.sqrt x.size)) :
    (verifyHamiltonianCycle x y).ret =
      (sourceFinish x (Nat.sqrt x.size)
        (forIn (List.ofFn fun i : Fin (Nat.sqrt x.size) => i) (prefixState [])
          (sourceStep x y (Nat.sqrt x.size) (Nat.clog 2 (Nat.sqrt x.size)))).ret).ret := by
  have hinit (m : Nat) :
      (none, Vector.replicate m false, none, none) = prefixState [] := by
    change (none, Vector.replicate m false, none, none) =
      (none, Vector.ofFn (fun _ : Fin m => false), none, none)
    apply congrArg (fun v : Vector Bool m =>
      ((none : Option Bool), v, (none : Option (Fin m)), (none : Option (Fin m))))
    apply Vector.ext
    intro i hi
    simp
  rw [verifyHamiltonianCycle_eq]
  simp only [TimeM.ret_bind, hv, Bool.not_true, Bool.false_eq_true, ite_false,
    show ¬Nat.sqrt x.size < 3 from Nat.not_lt.mpr hm, hy, bne_self_eq_false]
  rw [← Array.forIn_toList, Array.toList_ofFn, hinit]

end Cslib.Algorithms.Lean.Graph
