/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Internal.Accept
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Nodup

/-!
# Private complete source-index alignment

Canonical `Forall₂` and `List.ofFn` translate the actual saved traversal to the
source's indexed decoding clauses. They do not supply an executor input oracle.
-/

namespace Cslib.Algorithms.Lean.Graph

lemma aligned_indices (y : Array Bool) (m w : Nat) (us : List (Fin m))
    (h : List.Forall₂ (fun i v => Nat.ofDigits 2
      ((y.toList.drop (i.val * w)).take w |>.map fun bit => if bit then 1 else 0) = v.val)
      (List.ofFn fun i : Fin m => i) us) :
    ∃ hl : us.length = m, ∀ i : Fin m, Nat.ofDigits 2
      ((y.toList.drop (i.val * w)).take w |>.map fun bit => if bit then 1 else 0) =
      (us[i.val]'(by rw [hl]; exact i.isLt)).val := by
  have hl : us.length = m := by simpa only [List.length_ofFn] using h.length_eq.symm
  refine ⟨hl, fun i => ?_⟩
  have hi := h.get (i := i.val) (by simpa only [List.length_ofFn] using i.isLt)
    (by rw [hl]; exact i.isLt)
  simpa using hi

lemma ofFn_nodup_of_injective {α : Type} (m : Nat) (f : Fin m → α)
    (hf : Function.Injective f) : (List.ofFn f).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j hij
  rw [List.get_ofFn, List.get_ofFn] at hij
  have heq := hf hij
  have hv : i.val = j.val := congrArg (fun k : Fin m => k.val) heq
  exact Fin.ext hv

lemma aligned_indices_of_get (y : Array Bool) (m w : Nat) (us : List (Fin m))
    (hl : us.length = m)
    (h : ∀ i : Fin m, Nat.ofDigits 2
      ((y.toList.drop (i.val * w)).take w |>.map fun bit => if bit then 1 else 0) =
      (us[i.val]'(by rw [hl]; exact i.isLt)).val) :
    List.Forall₂ (fun i v => Nat.ofDigits 2
      ((y.toList.drop (i.val * w)).take w |>.map fun bit => if bit then 1 else 0) = v.val)
      (List.ofFn fun i : Fin m => i) us := by
  rw [List.forall₂_iff_get]
  refine ⟨by simpa only [List.length_ofFn] using hl.symm, ?_⟩
  intro i hi hu
  have him : i < m := by simpa only [List.length_ofFn] using hi
  simpa using h ⟨i, him⟩

lemma chain_closing_edges {α : Type} {R : α → α → Prop} (vs : List α)
    (hch : vs.IsChain R) (a b : α) (ha : vs.head? = some a)
    (hb : vs.getLast? = some b) (he : R b a) :
    ∀ i : Fin vs.length, R vs[i.val]
      (vs[(i.val + 1) % vs.length]'(Nat.mod_lt _ (by have := i.isLt; omega))) := by
  have hne : vs ≠ [] := by
    intro h
    subst vs
    cases ha
  have hh : vs.head hne = a := Option.some.inj
    ((List.head?_eq_some_head hne).symm.trans ha)
  have hl : vs.getLast hne = b := Option.some.inj
    ((List.getLast?_eq_some_getLast hne).symm.trans hb)
  intro i
  by_cases hi : i.val + 1 < vs.length
  · simp only [Nat.mod_eq_of_lt hi]
    exact List.isChain_iff_getElem.mp hch i.val hi
  · have hi' : i.val + 1 = vs.length := by omega
    have hi'' : i.val = vs.length - 1 := by omega
    simp only [hi', Nat.mod_self]
    simp only [hi'']
    rw [← List.getLast_eq_getElem hne, ← List.head_eq_getElem_zero hne, hl, hh]
    exact he

lemma ofFn_chain_of_cycle_edges {α : Type} {R : α → α → Prop} (m : Nat)
    (hm : 0 < m) (f : Fin m → α)
    (he : ∀ i : Fin m, R (f i) (f ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩)) :
    (List.ofFn f).IsChain R := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hi' : i + 1 < m := by simpa only [List.length_ofFn] using hi
  have him : i < m := by omega
  have h := he ⟨i, him⟩
  simpa only [List.getElem_ofFn, Nat.mod_eq_of_lt hi'] using h

lemma ofFn_closing_of_cycle_edges {α : Type} {R : α → α → Prop} (m : Nat)
    (hm : 0 < m) (f : Fin m → α)
    (he : ∀ i : Fin m, R (f i) (f ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩)) :
    ∃ a b, (List.ofFn f).head? = some a ∧ (List.ofFn f).getLast? = some b ∧ R b a := by
  have hne : List.ofFn f ≠ [] := by
    intro h
    have hz := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at hz
    exact hm.ne' hz
  refine ⟨(List.ofFn f).head hne, (List.ofFn f).getLast hne,
    List.head?_eq_some_head hne, List.getLast?_eq_some_getLast hne, ?_⟩
  rw [List.getLast_ofFn, List.head_ofFn]
  have hl : m - 1 + 1 = m := by omega
  have h := he ⟨m - 1, by omega⟩
  simpa only [hl, Nat.mod_self] using h

lemma aligned_list_order (x y : Array Bool) (m w : Nat) (hm : 0 < m)
    (us : List (Fin m))
    (halign : List.Forall₂ (fun i v => Nat.ofDigits 2
      ((y.toList.drop (i.val * w)).take w |>.map fun bit => if bit then 1 else 0) = v.val)
      (List.ofFn fun i : Fin m => i) us) (hnd : us.Nodup)
    (hch : us.IsChain (fun a b => x[a.val * m + b.val]?.getD false = true))
    (a b : Fin m) (ha : us.head? = some a) (hb : us.getLast? = some b)
    (he : x[b.val * m + a.val]?.getD false = true) :
    ∃ f : Fin m → Fin m,
      (∀ i, Nat.ofDigits 2
        ((y.toList.drop (i.val * w)).take w |>.map fun bit => if bit then 1 else 0) =
        (f i).val) ∧ Function.Injective f ∧
      ∀ i : Fin m,
        x[(f i).val * m + (f ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩).val]?.getD false = true := by
  obtain ⟨hl, hget⟩ := aligned_indices y m w us halign
  let f : Fin m → Fin m := fun i => us[i.val]'(by rw [hl]; exact i.isLt)
  refine ⟨f, hget, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    exact hnd.getElem_inj_iff.mp hij
  · intro i
    have hc := chain_closing_edges us hch a b ha hb he
      ⟨i.val, by rw [hl]; exact i.isLt⟩
    simpa only [hl, f] using hc

lemma sourceLoop_accept_of_order (x y : Array Bool) (m w : Nat) (hm : 0 < m)
    (hsize : y.size = m * w) (f : Fin m → Fin m)
    (hd : ∀ i, Nat.ofDigits 2
      ((y.toList.drop (i.val * w)).take w |>.map fun bit => if bit then 1 else 0) =
      (f i).val) (hf : Function.Injective f)
    (he : ∀ i : Fin m,
      x[(f i).val * m + (f ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩).val]?.getD false = true) :
    (sourceFinish x m (forIn (List.ofFn fun i : Fin m => i) (prefixState [])
      (sourceStep x y m w)).ret).ret = true := by
  apply (sourceLoop_accept_iff x y m w hsize _).mpr
  have halign : List.Forall₂ (fun i v => Nat.ofDigits 2
      ((y.toList.drop (i.val * w)).take w |>.map fun bit => if bit then 1 else 0) = v.val)
      (List.ofFn fun i : Fin m => i) (List.ofFn f) := by
    apply aligned_indices_of_get y m w _ List.length_ofFn
    intro i
    simpa only [List.getElem_ofFn] using hd i
  exact ⟨List.ofFn f, halign, ofFn_nodup_of_injective m f hf,
    ofFn_chain_of_cycle_edges m hm f he, ofFn_closing_of_cycle_edges m hm f he⟩

lemma sourceLoop_accept_order_iff (x y : Array Bool) (m w : Nat) (hm : 0 < m)
    (hsize : y.size = m * w) :
    (sourceFinish x m (forIn (List.ofFn fun i : Fin m => i) (prefixState [])
      (sourceStep x y m w)).ret).ret = true ↔
      ∃ f : Fin m → Fin m,
        (∀ i, Nat.ofDigits 2
          ((y.toList.drop (i.val * w)).take w |>.map fun bit => if bit then 1 else 0) =
          (f i).val) ∧ Function.Injective f ∧
        ∀ i : Fin m,
          x[(f i).val * m + (f ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩).val]?.getD false =
            true := by
  constructor
  · intro h
    obtain ⟨us, halign, hnd, hch, a, b, ha, hb, he⟩ :=
      (sourceLoop_accept_iff x y m w hsize _).mp h
    exact aligned_list_order x y m w hm us halign hnd hch a b ha hb he
  · rintro ⟨f, hd, hf, he⟩
    exact sourceLoop_accept_of_order x y m w hm hsize f hd hf he

end Cslib.Algorithms.Lean.Graph
