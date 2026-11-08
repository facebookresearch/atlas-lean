/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Internal.Order
import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Internal.Validation

/-!
# Private complete verifier characteristic

CLRS4's ordered certificate checks are coupled to the same source-order saved
state. Validation and strict cycle size are actual guards, not caller premises.
-/

namespace Cslib.Algorithms.Lean.Graph

lemma verify_order_iff (x y : Array Bool) :
    let m := Nat.sqrt x.size
    let w := Nat.clog 2 m
    (verifyHamiltonianCycle x y).ret = true ↔
      (validateGraph x m).ret = true ∧ 3 ≤ m ∧ y.size = m * w ∧
      ∃ f : Fin m → Fin m,
        (∀ i, Nat.ofDigits 2
          ((y.toList.drop (i.val * w)).take w |>.map fun bit => if bit then 1 else 0) =
          (f i).val) ∧ Function.Injective f ∧
        ∀ i : Fin m,
          x[(f i).val * m +
            (f ⟨(i.val + 1) % m, Nat.mod_lt _ (by have := i.isLt; omega)⟩).val]?.getD false =
              true := by
  dsimp only
  constructor
  · intro h
    obtain ⟨hv, hm, hy⟩ := accept_guards x y h
    refine ⟨hv, hm, hy, ?_⟩
    have ht := (verify_ret_of_guards x y hv hm hy).symm.trans h
    exact (sourceLoop_accept_order_iff x y _ _ (by omega) hy).mp ht
  · rintro ⟨hv, hm, hy, hf⟩
    rw [verify_ret_of_guards x y hv hm hy]
    exact (sourceLoop_accept_order_iff x y _ _ (by omega) hy).mpr hf

lemma validateGraph_nat_iff (x : Array Bool) (m : Nat) :
    (validateGraph x m).ret = true ↔ m * m = x.size ∧
      (∀ i < m, x[i * m + i]? = some false) ∧
      (∀ i < m, ∀ j < m, x[i * m + j]? = x[j * m + i]?) := by
  rw [validateGraph_iff]
  constructor
  · rintro ⟨hs, hd, he⟩
    exact ⟨hs, fun i hi => hd ⟨i, hi⟩, fun i hi j hj => he ⟨i, hi⟩ ⟨j, hj⟩⟩
  · rintro ⟨hs, hd, he⟩
    exact ⟨hs, fun i => hd i.val i.isLt, fun i j => he i.val i.isLt j.val j.isLt⟩

lemma order_nat_forward (x : Array Bool) (m : Nat) (d : Nat → Nat)
    (f : Fin m → Fin m) (hd : ∀ i : Fin m, d i.val = (f i).val)
    (hf : Function.Injective f)
    (he : ∀ i : Fin m, x[(f i).val * m +
      (f ⟨(i.val + 1) % m, Nat.mod_lt _ (by have := i.isLt; omega)⟩).val]?.getD false =
        true) :
    (∀ i < m, d i < m) ∧
      (∀ i < m, ∀ j < m, d i = d j → i = j) ∧
      (∀ i < m, x[d i * m + d ((i + 1) % m)]?.getD false = true) := by
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · rw [hd ⟨i, hi⟩]
    exact (f ⟨i, hi⟩).isLt
  · intro i hi j hj hij
    have h : f ⟨i, hi⟩ = f ⟨j, hj⟩ := Fin.ext
      ((hd ⟨i, hi⟩).symm.trans (hij.trans (hd ⟨j, hj⟩)))
    exact congrArg Fin.val (hf h)
  · intro i hi
    have h := he ⟨i, hi⟩
    rw [← hd ⟨i, hi⟩,
      ← hd ⟨(i + 1) % m, Nat.mod_lt _ (by omega)⟩] at h
    exact h

lemma order_nat_backward (x : Array Bool) (m : Nat) (d : Nat → Nat)
    (hr : ∀ i < m, d i < m)
    (hi : ∀ i < m, ∀ j < m, d i = d j → i = j)
    (he : ∀ i < m, x[d i * m + d ((i + 1) % m)]?.getD false = true) :
    ∃ f : Fin m → Fin m, (∀ i : Fin m, d i.val = (f i).val) ∧
      Function.Injective f ∧
      ∀ i : Fin m, x[(f i).val * m +
        (f ⟨(i.val + 1) % m, Nat.mod_lt _ (by have := i.isLt; omega)⟩).val]?.getD false =
          true := by
  let f : Fin m → Fin m := fun i => ⟨d i.val, hr i.val i.isLt⟩
  refine ⟨f, fun _ => rfl, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    exact hi i.val i.isLt j.val j.isLt (congrArg Fin.val hij)
  · intro i
    exact he i.val i.isLt

lemma order_optional_iff (x : Array Bool) (m : Nat) (d : Nat → Nat)
    (hs : m * m = x.size) (hr : ∀ i < m, d i < m) :
    (∀ i < m, x[d i * m + d ((i + 1) % m)]?.getD false = true) ↔
      (∀ i < m, x[d i * m + d ((i + 1) % m)]? = some true) := by
  have hb (i : Nat) (hi : i < m) : d i * m + d ((i + 1) % m) < x.size := by
    rw [← hs]
    exact row_major_lt m _ _ (hr i hi)
      (hr _ (Nat.mod_lt _ (by omega)))
  constructor
  · intro h i hi
    have hg := graph_read_some x _ (hb i hi)
    rwa [h i hi] at hg
  · intro h i hi
    exact congrArg (fun p : Option Bool => p.getD false) (h i hi)

end Cslib.Algorithms.Lean.Graph
