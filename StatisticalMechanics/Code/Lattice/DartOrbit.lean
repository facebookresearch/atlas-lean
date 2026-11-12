/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective

open SimpleGraph Function

namespace StatMech

namespace Lattice









theorem dartDir_ne_zero (e : Dart) : e.dir ≠ 0 := by
  intro h
  have := unitWt_dir e
  rw [h] at this
  simp [unitWt] at this


theorem rot90Fun_zero : rot90Fun (0 : Site 2) = 0 := by
  funext i; fin_cases i <;> simp [rot90Fun]


theorem rot90Fun_dartDir_ne_zero (e : Dart) : rot90Fun e.dir ≠ 0 := by
  intro h
  exact dartDir_ne_zero e (rot90Fun_injective (by rw [h, rot90Fun_zero]))


theorem neg_rot90Fun_dartDir_ne_zero (e : Dart) : (-rot90Fun e.dir : Site 2) ≠ 0 := by
  intro h
  apply rot90Fun_dartDir_ne_zero e
  have := congrArg Neg.neg h; rwa [neg_neg, neg_zero] at this



theorem rot90Fun_dartDir_ne_dartDir (e : Dart) : rot90Fun e.dir ≠ e.dir := by
  intro h
  have h2 : rot90Fun (rot90Fun e.dir) = e.dir := by rw [h, h]
  rw [rot90Fun_rot90Fun'] at h2
  apply dartDir_ne_zero e
  funext i; have hi := congrFun h2 i
  simp only [Pi.neg_apply, Pi.zero_apply] at hi ⊢; omega




theorem neg_rot90Fun_dartDir_ne_dartDir (e : Dart) : -rot90Fun e.dir ≠ e.dir := by
  intro h
  have hr : rot90Fun e.dir = -e.dir := by
    have := congrArg Neg.neg h; rwa [neg_neg] at this
  have h2 : rot90Fun (rot90Fun e.dir) = rot90Fun (-e.dir) := congrArg rot90Fun hr
  rw [rot90Fun_rot90Fun', rot90Fun_neg, hr, neg_neg] at h2
  apply dartDir_ne_zero e
  funext i; have hi := congrFun h2 i
  simp only [Pi.neg_apply, Pi.zero_apply] at hi ⊢; omega








theorem dartNext_ne_self (K : Set (Site 2)) (e : Dart) (_he : IsBoundaryDart K e) :
    dartNext K e ≠ e := by
  classical
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · 
    intro hcon
    have hdir : (dartNext K e).dir = rot90Fun e.dir := (dartNext_front_head K e hA).2
    rw [hcon] at hdir
    exact rot90Fun_dartDir_ne_dartDir e hdir.symm
  · by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · 
      intro hcon
      have ht : (dartNext K e).tail = e.tail + (-rot90Fun e.dir) :=
        dartNext_straight_tail K e hA hB
      rw [hcon] at ht
      apply neg_rot90Fun_dartDir_ne_zero e
      have h' : e.tail + (-rot90Fun e.dir) = e.tail + 0 := by rw [add_zero]; exact ht.symm
      exact add_left_cancel h'
    · 
      intro hcon
      have hdir : (dartNext K e).dir = -rot90Fun e.dir := dartNext_left_dir K e hA hB
      rw [hcon] at hdir
      exact neg_rot90Fun_dartDir_ne_dartDir e hdir.symm












theorem dartNext_consecutive (K : Set (Site 2)) (e : Dart) :
    ((dartNext K e).head = e.head) ∨
    ((dartNext K e).tail = e.tail + (-rot90Fun e.dir) ∧
     (dartNext K e).head = e.head + (-rot90Fun e.dir)) ∨
    ((dartNext K e).tail = e.tail) := by
  classical
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · exact Or.inl (dartNext_front_head K e hA).1
  · by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · exact Or.inr (Or.inl ⟨dartNext_straight_tail K e hA hB, dartNext_straight_head K e hA hB⟩)
    · exact Or.inr (Or.inr (dartNext_left_tail K e hA hB))





noncomputable def dartNextSub (K : Set (Site 2)) :
    {e : Dart // IsBoundaryDart K e} → {e : Dart // IsBoundaryDart K e} :=
  fun e => ⟨dartNext K e.1, dartNext_isBoundaryDart K e.1 e.2⟩

@[simp] theorem dartNextSub_val (K : Set (Site 2)) (e : {e : Dart // IsBoundaryDart K e}) :
    (dartNextSub K e).1 = dartNext K e.1 := rfl



theorem dartNextSub_injective (K : Set (Site 2)) :
    Function.Injective (dartNextSub K) := by
  intro a b h
  exact Subtype.ext (dartNext_injOn K a.2 b.2 (congrArg Subtype.val h))



theorem dartNextSub_iterate_val (K : Set (Site 2)) (e : {e : Dart // IsBoundaryDart K e})
    (k : ℕ) : ((dartNextSub K)^[k] e).1 = (dartNext K)^[k] e.1 := by
  induction k generalizing e with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]; rfl



theorem dartNextSub_ne_self (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    dartNextSub K a ≠ a := by
  intro h
  exact dartNext_ne_self K a.1 a.2 (congrArg Subtype.val h)











theorem dartNext_periodic (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) :
    ∃ p > 0, (dartNext K)^[p] e = e := by
  have hfin : Finite {e : Dart // IsBoundaryDart K e} := (boundaryDarts_finite K hK).to_subtype
  have hmem := (dartNextSub_injective K).mem_periodicPts ⟨e, he⟩
  rw [Function.mem_periodicPts] at hmem
  obtain ⟨p, hp, hper⟩ := hmem
  refine ⟨p, hp, ?_⟩
  have := congrArg Subtype.val hper
  rwa [dartNextSub_iterate_val] at this






noncomputable def dartSuccGraph (K : Set (Site 2)) :
    SimpleGraph {e : Dart // IsBoundaryDart K e} where
  Adj a b := a ≠ b ∧ (dartNextSub K a = b ∨ dartNextSub K b = a)
  symm := by rintro a b ⟨hne, h⟩; exact ⟨hne.symm, h.symm⟩
  loopless := by refine ⟨?_⟩; rintro a ⟨hne, _⟩; exact hne rfl



theorem dartSuccGraph_adj_next (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (dartSuccGraph K).Adj a (dartNextSub K a) := by
  refine ⟨?_, Or.inl rfl⟩
  intro h
  exact dartNextSub_ne_self K a h.symm





noncomputable def orbitWalkAux (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (n : ℕ) → (dartSuccGraph K).Walk a ((dartNextSub K)^[n] a)
  | 0 => SimpleGraph.Walk.nil
  | (n+1) =>
      (orbitWalkAux K a n).concat (by
        rw [Function.iterate_succ_apply']
        exact dartSuccGraph_adj_next K ((dartNextSub K)^[n] a))


theorem orbitWalkAux_length (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (n : ℕ) : (orbitWalkAux K a n).length = n := by
  induction n with
  | zero => rfl
  | succ m ih => simp only [orbitWalkAux, SimpleGraph.Walk.length_concat, ih]



theorem orbitWalkAux_support (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (n : ℕ) :
    (orbitWalkAux K a n).support = (List.range (n + 1)).map (fun k => (dartNextSub K)^[k] a) := by
  induction n with
  | zero => simp [orbitWalkAux]
  | succ m ih =>
    show ((orbitWalkAux K a m).concat _).support = _
    rw [SimpleGraph.Walk.support_concat, ih, List.range_succ (n := m + 1), List.map_append]
    simp





noncomputable def dartOrbitPeriod (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    ℕ := Function.minimalPeriod (dartNextSub K) a


theorem dartOrbitPeriod_pos (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : 0 < dartOrbitPeriod K a := by
  have hfin : Finite {e : Dart // IsBoundaryDart K e} := (boundaryDarts_finite K hK).to_subtype
  exact Function.minimalPeriod_pos_of_mem_periodicPts
    ((dartNextSub_injective K).mem_periodicPts a)



theorem one_lt_dartOrbitPeriod (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : 1 < dartOrbitPeriod K a := by
  rcases Nat.lt_or_ge 1 (dartOrbitPeriod K a) with h | h
  · exact h
  · exfalso
    have hpos := dartOrbitPeriod_pos K hK a
    have heq : dartOrbitPeriod K a = 1 := le_antisymm h hpos
    have hfix : Function.IsFixedPt (dartNextSub K) a :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.mp heq
    exact dartNextSub_ne_self K a hfix


theorem dartOrbitPeriod_iterate (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (dartNextSub K)^[dartOrbitPeriod K a] a = a :=
  Function.iterate_minimalPeriod





noncomputable def dartOrbitWalk (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (dartSuccGraph K).Walk a a :=
  (orbitWalkAux K a (dartOrbitPeriod K a)).copy rfl (dartOrbitPeriod_iterate K a)


theorem dartOrbitWalk_length (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (dartOrbitWalk K a).length = dartOrbitPeriod K a := by
  unfold dartOrbitWalk
  rw [SimpleGraph.Walk.length_copy, orbitWalkAux_length]



theorem dartOrbitWalk_length_pos (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : 0 < (dartOrbitWalk K a).length := by
  rw [dartOrbitWalk_length]; exact dartOrbitPeriod_pos K hK a


theorem dartOrbitWalk_ne_nil (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : dartOrbitWalk K a ≠ SimpleGraph.Walk.nil := by
  intro h
  have := dartOrbitWalk_length_pos K hK a
  rw [h] at this
  simp at this




theorem dartOrbitWalk_support (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (dartOrbitWalk K a).support
      = (List.range (dartOrbitPeriod K a + 1)).map (fun k => (dartNextSub K)^[k] a) := by
  unfold dartOrbitWalk
  rw [SimpleGraph.Walk.support_copy, orbitWalkAux_support]










theorem iterate_inj_on_Icc_minimalPeriod {α : Type*} (f : α → α) (x : α) {j k : ℕ}
    (hpos : 0 < Function.minimalPeriod f x)
    (hj1 : 1 ≤ j) (hjp : j ≤ Function.minimalPeriod f x)
    (hk1 : 1 ≤ k) (hkp : k ≤ Function.minimalPeriod f x)
    (h : f^[j] x = f^[k] x) : j = k := by
  set p := Function.minimalPeriod f x with hp
  have hjk : f^[j % p] x = f^[k % p] x := by
    rw [Function.iterate_mod_minimalPeriod_eq, Function.iterate_mod_minimalPeriod_eq, h]
  have hjlt : j % p < p := Nat.mod_lt _ hpos
  have hklt : k % p < p := Nat.mod_lt _ hpos
  have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := f) (x := x)
    (Set.mem_Iio.mpr hjlt) (Set.mem_Iio.mpr hklt) hjk
  have hj : j % p = if j = p then 0 else j := by
    rcases eq_or_lt_of_le hjp with h' | h'
    · simp [h', Nat.mod_self]
    · rw [if_neg (by omega), Nat.mod_eq_of_lt h']
  have hk : k % p = if k = p then 0 else k := by
    rcases eq_or_lt_of_le hkp with h' | h'
    · simp [h', Nat.mod_self]
    · rw [if_neg (by omega), Nat.mod_eq_of_lt h']
  rw [hj, hk] at hinj
  split_ifs at hinj <;> omega





theorem dartOrbitWalk_support_tail_nodup (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    (dartOrbitWalk K a).support.tail.Nodup := by
  rw [dartOrbitWalk_support]
  have hpe : dartOrbitPeriod K a = Function.minimalPeriod (dartNextSub K) a := rfl
  set p := dartOrbitPeriod K a with hp
  have hpos : 0 < Function.minimalPeriod (dartNextSub K) a := dartOrbitPeriod_pos K hK a
  rw [List.range_succ_eq_map, List.map_cons, List.tail_cons, List.map_map]
  apply List.Nodup.map_on (l := List.range p) (f := (fun k => (dartNextSub K)^[k] a) ∘ Nat.succ)
  · intro j hj k hk h
    simp only [List.mem_range] at hj hk
    simp only [Function.comp_apply] at h
    have := iterate_inj_on_Icc_minimalPeriod (dartNextSub K) a (j := j + 1) (k := k + 1)
      hpos (by omega) (by omega) (by omega) (by omega) h
    omega
  · exact List.nodup_range

end Lattice

end StatMech
