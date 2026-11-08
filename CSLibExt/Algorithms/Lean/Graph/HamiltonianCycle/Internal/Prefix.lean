/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Internal.Loop
import Init.Data.Vector.OfFn

/-!
# Private successful-prefix invariant for the actual certificate loop

`prefixState` describes saved data only. It performs no verifier execution.
The loop proof below uses the exact `sourceStep_ret` equation and canonical `forIn`.
-/

namespace Cslib.Algorithms.Lean.Graph

open Cslib.Algorithms.Lean

@[no_expose] def prefixState {m : Nat} (vs : List (Fin m)) :
    Option Bool × Vector Bool m × Option (Fin m) × Option (Fin m) :=
  (none, Vector.ofFn (fun v => decide (v ∈ vs)), vs.head?, vs.getLast?)

lemma prefix_bitmap_append {m : Nat} (vs : List (Fin m)) (v : Fin m) :
    (Vector.ofFn (fun a => decide (a ∈ vs))).set v.val true v.isLt =
      Vector.ofFn (fun a => decide (a ∈ vs ++ [v])) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_set, Vector.getElem_ofFn, List.mem_append,
    List.mem_singleton]
  by_cases h : v.val = j
  · have hv : (⟨j, hj⟩ : Fin m) = v := Fin.ext h.symm
    simp [h, hv]
  · have hv : (⟨j, hj⟩ : Fin m) ≠ v := fun e => h (congrArg Fin.val e).symm
    simp [h, hv]

lemma sourceStep_prefix_yield (x y : Array Bool) (m w : Nat) (i v : Fin m)
    (vs : List (Fin m)) (hsize : y.size = m * w)
    (hv : Nat.ofDigits 2
      ((y.toList.drop (i.val * w)).take w |>.map fun bit => if bit then 1 else 0) = v.val)
    (hfresh : v ∉ vs)
    (hedge : ∀ p, vs.getLast? = some p → x[p.val * m + v.val]?.getD false = true) :
    (sourceStep x y m w i (prefixState vs)).ret = .yield (prefixState (vs ++ [v])) := by
  unfold prefixState
  rw [sourceStep_ret x y m w i _ _ _ hsize, hv]
  simp only [dite_eq_left v.isLt, prefix_bitmap_append]
  cases hp : vs.getLast? with
  | none =>
    have hvs := List.getLast?_eq_none_iff.mp hp
    subst vs
    simp
  | some p =>
    have he := hedge p hp
    cases vs with
    | nil => simp at hp
    | cons a vs =>
      simp_all only [List.mem_cons, Bool.decide_or, Fin.eta, Fin.getElem_fin,
        Vector.getElem_ofFn, Bool.or_eq_true, decide_eq_true_eq, List.head?_cons,
        Bool.not_true, List.cons_append, List.mem_append,
        List.not_mem_nil, or_false]
      simp only [Bool.false_eq_true, ite_false, ForInStep.yield.injEq, Prod.mk.injEq, true_and]
      change some v = ((a :: vs) ++ [v]).getLast?
      rw [List.getLast?_append]
      simp

lemma sourceStep_flags (x y : Array Bool) (m w : Nat) (i : Fin m)
    (s : Option Bool × Vector Bool m × Option (Fin m) × Option (Fin m)) :
    match (sourceStep x y m w i s).ret with
    | .done t => t.1 = some false
    | .yield t => t.1 = none := by
  rcases s with ⟨flag, seen, first, previous⟩
  unfold sourceStep
  simp only [TimeM.ret_bind]
  split_ifs <;> cases previous <;>
    simp_all only [graphRead, TimeM.ret_bind, TimeM.ret_pure]
  all_goals split_ifs <;> simp_all only [↓reduceIte, TimeM.ret_pure, Bool.false_eq_true]

lemma sourceStep_prefix_yield_info (x y : Array Bool) (m w : Nat) (i : Fin m)
    (vs : List (Fin m)) (hsize : y.size = m * w)
    (s : Option Bool × Vector Bool m × Option (Fin m) × Option (Fin m))
    (hy : (sourceStep x y m w i (prefixState vs)).ret = .yield s) :
    ∃ v : Fin m, Nat.ofDigits 2
        ((y.toList.drop (i.val * w)).take w |>.map fun bit => if bit then 1 else 0) = v.val ∧
      v ∉ vs ∧ (∀ p, vs.getLast? = some p → x[p.val * m + v.val]?.getD false = true) ∧
      s = prefixState (vs ++ [v]) := by
  let d := Nat.ofDigits 2
    ((y.toList.drop (i.val * w)).take w |>.map fun bit => if bit then 1 else 0)
  have heq := sourceStep_ret x y m w i
    (Vector.ofFn (fun a => decide (a ∈ vs))) vs.head? vs.getLast? hsize
  have hrun := hy
  unfold prefixState at hy
  rw [heq] at hy
  simp only [← show d = Nat.ofDigits 2
    ((y.toList.drop (i.val * w)).take w |>.map fun bit => if bit then 1 else 0) from rfl] at hy
  by_cases hd : d < m
  · let v : Fin m := ⟨d, hd⟩
    have hval : d = v.val := rfl
    simp only [dite_eq_left hd, Fin.getElem_fin, Vector.getElem_ofFn,
      show (⟨d, hd⟩ : Fin m) = v from rfl] at hy
    by_cases hf : v ∈ vs
    · simp only [hf, decide_true, ite_true, reduceCtorEq] at hy
    · have hed : ∀ p, vs.getLast? = some p → x[p.val * m + v.val]?.getD false = true := by
        intro p hp
        change x[p.val * m + d]?.getD false = true
        cases hb : x[p.val * m + d]?.getD false with
        | false =>
          simp only [hf, decide_false, Bool.false_eq_true, ite_false, hp, hb,
            Bool.not_false, ite_true, reduceCtorEq] at hy
        | true => rfl
      refine ⟨v, hval, hf, hed, ?_⟩
      have hs := sourceStep_prefix_yield x y m w i v vs hsize hval hf hed
      exact ForInStep.yield.inj (hrun.symm.trans hs)
  · simp only [dite_eq_right hd, reduceCtorEq] at hy

end Cslib.Algorithms.Lean.Graph
