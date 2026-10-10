/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Sort.InsertionCost
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Vector.Basic
public import Mathlib.Order.Interval.Set.Defs

import Mathlib.Tactic.NormNum

/-!
# Saved-bucket sort

CLRS, fourth edition, section8.4 (printed pages215-218). Source entries are visited
in order and prepended to a saved Vector of floor buckets. Only the canonical
`TimeM.insertionSort` sorts; sorted buckets are concatenated in increasing index order.

The metric charges five phase events per entry and the actual insertion comparisons.
Pure persistent-container construction, erased witnesses, physical allocation, bit/word
complexity and native running time are not included. Equal values are allowed; stability
is not claimed. Empty input returns the empty array at zero cost.
-/

open Set Cslib.Algorithms.Lean
open scoped BigOperators

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.TimeM

private lemma classifier_lt_generic {R : Type u} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] {n : ℕ} (hn : 0 < n) {x : R} (hx : x ∈ Ico 0 1) :
    Nat.floor ((n : R) * x) < n := by
  have hn' : 0 < (n : R) := by exact_mod_cast hn
  apply (Nat.floor_lt (mul_nonneg (le_of_lt hn') hx.1)).2
  simpa using mul_lt_mul_of_pos_left hx.2 hn'

@[no_expose] private def placeBuckets {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] (xs : Array R)
    (hx : ∀ x ∈ xs.toList, x ∈ Ico (0 : R) 1) (hn : 0 < xs.size)
    (initial : _root_.Vector (List R) xs.size) :
    TimeM Nat (_root_.Vector (List R) xs.size) :=
  xs.attach.foldlM (m := TimeM Nat)
    (fun (buckets : _root_.Vector (List R) xs.size) x => do
      ✓
      let i : Fin xs.size := ⟨Nat.floor ((xs.size : R) * x.val),
        classifier_lt_generic hn (hx x.val (Array.mem_toList_iff.mpr x.property))⟩
      return buckets.set i.val (x.val :: buckets.get i) i.isLt) initial

@[no_expose] private def flattenBuckets {R : Type} {n : Nat}
    (buckets : _root_.Vector (List R) n) : TimeM Nat (Array R) :=
  buckets.foldlM (m := TimeM Nat) (fun (output : Array R) bucket => do
    ✓
    bucket.foldlM (m := TimeM Nat) (fun (output : Array R) x => do
      ✓
      return output.push x) output) #[]

/-- Prepend into saved floor buckets, insertion-sort each bucket, then concatenate them. -/
public def bucketSort {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] (xs : Array R)
    (hx : ∀ x ∈ xs.toList, x ∈ Ico (0 : R) 1) : TimeM Nat (Array R) :=
  if hn : 0 < xs.size then do
    let initial : _root_.Vector (List R) xs.size := _root_.Vector.replicate xs.size []
    ✓[xs.size]
    let buckets ← placeBuckets xs hx hn initial
    let sorted ← buckets.mapM (m := TimeM Nat) (fun bucket => do
      ✓
      TimeM.insertionSort bucket)
    flattenBuckets sorted
  else pure #[]



private lemma empty_computation {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    (hx : ∀ x ∈ (#[] : Array R).toList, x ∈ Ico (0 : R) 1) :
    bucketSort #[] hx = (pure #[] : TimeM Nat (Array R)) := by
  simp [bucketSort]

private lemma get_set_cons {α : Type} {n : Nat} (buckets : _root_.Vector (List α) n)
    (label : α → Fin n) (x : α) (i : Fin n) :
    (buckets.set (label x).val (x :: buckets.get (label x)) (label x).isLt).get i =
      if label x = i then x :: buckets.get i else buckets.get i := by
  change (buckets.set (label x).val (x :: buckets[(label x).val]) (label x).isLt)[i.val] =
    if label x = i then x :: buckets[i.val] else buckets[i.val]
  by_cases h : label x = i
  · subst i
    simp
  · have hval : (label x).val ≠ i.val := by
      intro heq
      exact h (Fin.ext heq)
    simp [hval, h]

private lemma fold_bucket_get {α β : Type} {n : Nat} (value : β → α)
    (label : β → Fin n) (xs : List β) (buckets : _root_.Vector (List α) n) (i : Fin n) :
    ((xs.foldlM (m := TimeM Nat) (fun buckets x => do
      ✓
      return buckets.set (label x).val (value x :: buckets.get (label x)) (label x).isLt)
      buckets).ret).get i =
        ((xs.filter (fun x => decide (label x = i))).map value).reverse ++ buckets.get i := by
  induction xs generalizing buckets with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldlM_cons, TimeM.ret_bind, TimeM.ret_pure]
      rw [ih, get_set_cons buckets (fun _ => label x) (value x) i]
      by_cases h : label x = i
      · simp [h, List.reverse_cons, List.append_assoc]
      · simp [h]

private lemma fold_bucket_time {α β : Type} {n : Nat} (value : β → α)
    (label : β → Fin n) (xs : List β) (buckets : _root_.Vector (List α) n) :
    (xs.foldlM (m := TimeM Nat) (fun buckets x => do
      ✓
      return buckets.set (label x).val (value x :: buckets.get (label x)) (label x).isLt)
      buckets).time = xs.length := by
  induction xs generalizing buckets with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldlM_cons, TimeM.time_bind, TimeM.time_tick]
      rw [ih]
      simp [Nat.add_comm]

private lemma place_bucket_get {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] (xs : Array R)
    (hx : ∀ x ∈ xs.toList, x ∈ Ico (0 : R) 1) (hn : 0 < xs.size)
    (initial : _root_.Vector (List R) xs.size) (i : Fin xs.size) :
    (placeBuckets xs hx hn initial).ret.get i =
      (xs.toList.filter (fun x => decide (Nat.floor ((xs.size : R) * x) = i.val))).reverse ++
        initial.get i := by
  let label : {x // x ∈ xs} → Fin xs.size := fun x =>
    ⟨Nat.floor ((xs.size : R) * x.val),
      classifier_lt_generic hn (hx x.val (Array.mem_toList_iff.mpr x.property))⟩
  have hfold := fold_bucket_get Subtype.val label xs.attach.toList initial i
  have hfilter :
      (xs.attach.toList.filter (fun x => decide (label x = i))).map Subtype.val =
        xs.toList.filter (fun x => decide (Nat.floor ((xs.size : R) * x) = i.val)) := by
    simp only [Fin.ext_iff, label]
    simpa only [Function.comp_def, Array.toList_attach, List.attachWith_map_subtype_val]
      using (List.filter_map (f := (Subtype.val : {x : R // x ∈ xs} → R))
        (p := fun x : R => decide (Nat.floor ((xs.size : R) * x) = i.val))
        (l := xs.attach.toList)).symm
  rw [hfilter] at hfold
  simpa only [placeBuckets, ← Array.foldlM_toList] using hfold

private lemma place_bucket_time {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] (xs : Array R)
    (hx : ∀ x ∈ xs.toList, x ∈ Ico (0 : R) 1) (hn : 0 < xs.size)
    (initial : _root_.Vector (List R) xs.size) :
    (placeBuckets xs hx hn initial).time = xs.size := by
  let label : {x // x ∈ xs} → Fin xs.size := fun x =>
    ⟨Nat.floor ((xs.size : R) * x.val),
      classifier_lt_generic hn (hx x.val (Array.mem_toList_iff.mpr x.property))⟩
  have hfold := fold_bucket_time Subtype.val label xs.attach.toList initial
  calc
    (placeBuckets xs hx hn initial).time = xs.attach.toList.length := by
      simpa only [placeBuckets, ← Array.foldlM_toList] using hfold
    _ = xs.size := by simp


private lemma table_update_perm {α : Type} (table : List (List α)) (x : α)
    (i : Nat) (hi : i < table.length) :
    (table.set i (x :: table[i])).flatten.Perm (x :: table.flatten) := by
  induction table generalizing i with
  | nil => simp at hi
  | cons bucket table ih =>
      cases i with
      | zero => simp
      | succ i =>
          have hi' : i < table.length := by simpa using hi
          simpa only [List.set_cons_succ, List.getElem_cons_succ, List.flatten_cons]
            using ((ih i hi').append_left bucket).trans List.perm_middle

private lemma vector_update_perm {α : Type} {n : Nat}
    (table : _root_.Vector (List α) n) (x : α) (i : Fin n) :
    (table.set i.val (x :: table.get i) i.isLt).toList.flatten.Perm
      (x :: table.toList.flatten) := by
  change (table.set i.val (x :: table[i.val]) i.isLt).toList.flatten.Perm
    (x :: table.toList.flatten)
  have h := table_update_perm table.toList x i.val (by simp)
  simpa only [Vector.toList_set, Vector.getElem_toList] using h

private lemma fold_bucket_perm {α β : Type} {n : Nat} (value : β → α)
    (label : β → Fin n) (xs : List β) (initial : _root_.Vector (List α) n) :
    ((xs.foldlM (m := TimeM Nat) (fun buckets x => do
      ✓
      return buckets.set (label x).val (value x :: buckets.get (label x)) (label x).isLt)
      initial).ret).toList.flatten.Perm (xs.map value ++ initial.toList.flatten) := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldlM_cons, TimeM.ret_bind, TimeM.ret_pure]
      exact (ih _).trans
        (((vector_update_perm initial (value x) (label x)).append_left (xs.map value)).trans
          (by simpa only [List.map_cons, List.cons_append] using
            (List.perm_middle (l₁ := xs.map value) (l₂ := initial.toList.flatten)
              (a := value x))))

private lemma place_bucket_perm {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] (xs : Array R)
    (hx : ∀ x ∈ xs.toList, x ∈ Ico (0 : R) 1) (hn : 0 < xs.size)
    (initial : _root_.Vector (List R) xs.size) :
    (placeBuckets xs hx hn initial).ret.toList.flatten.Perm
      (xs.toList ++ initial.toList.flatten) := by
  let label : {x // x ∈ xs} → Fin xs.size := fun x =>
    ⟨Nat.floor ((xs.size : R) * x.val),
      classifier_lt_generic hn (hx x.val (Array.mem_toList_iff.mpr x.property))⟩
  have hfold := fold_bucket_perm Subtype.val label xs.attach.toList initial
  simpa only [placeBuckets, ← Array.foldlM_toList, Array.toList_attach,
    List.attachWith_map_subtype_val] using hfold

private lemma vector_mapM_toList {α β : Type} {n : Nat}
    (f : α → TimeM Nat β) (xs : _root_.Vector α n) :
    Vector.toList <$> xs.mapM f = xs.toList.mapM f := by
  calc
    Vector.toList <$> xs.mapM f = Array.toList <$> (Vector.toArray <$> xs.mapM f) := rfl
    _ = Array.toList <$> xs.toArray.mapM f := by rw [Vector.toArray_mapM]
    _ = xs.toList.mapM f := Array.toList_mapM

private lemma list_mapM_ret {α β : Type} (f : α → TimeM Nat β) (xs : List α) :
    (xs.mapM f).ret = xs.map (fun x => (f x).ret) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.mapM_cons, ih]

private lemma insertion_table_perm {R : Type} [LinearOrder R] (table : List (List R)) :
    (table.map (fun bucket => (TimeM.insertionSort bucket).ret)).flatten.Perm
      table.flatten := by
  induction table with
  | nil => simp
  | cons bucket table ih =>
      simpa only [List.map_cons, List.flatten_cons] using
        (TimeM.insertionSort_perm bucket).append ih

private lemma sorted_bucket_perm {R : Type} [LinearOrder R] {n : Nat}
    (table : _root_.Vector (List R) n) :
    ((table.mapM (m := TimeM Nat) (fun bucket => do
      ✓
      TimeM.insertionSort bucket)).ret).toList.flatten.Perm table.toList.flatten := by
  have h := congrArg TimeM.ret (vector_mapM_toList (fun bucket => do
    ✓
    TimeM.insertionSort bucket) table)
  simp only [TimeM.ret_map, list_mapM_ret, TimeM.ret_bind] at h
  rw [h]
  exact insertion_table_perm table.toList

private lemma push_fold_ret {α : Type} (xs : List α) (initial : Array α) :
    ((xs.foldlM (m := TimeM Nat) (fun output x => do
      ✓
      return output.push x) initial).ret).toList = initial.toList ++ xs := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldlM_cons, TimeM.ret_bind, TimeM.ret_pure]
      rw [ih]
      simp

private lemma flatten_fold_ret {α : Type} (table : List (List α)) (initial : Array α) :
    ((table.foldlM (m := TimeM Nat) (fun output bucket => do
      ✓
      bucket.foldlM (m := TimeM Nat) (fun output x => do
        ✓
        return output.push x) output) initial).ret).toList = initial.toList ++ table.flatten := by
  induction table generalizing initial with
  | nil => simp
  | cons bucket table ih =>
      simp only [List.foldlM_cons, TimeM.ret_bind]
      rw [ih, push_fold_ret]
      simp

private lemma flatten_bucket_ret {α : Type} {n : Nat}
    (table : _root_.Vector (List α) n) :
    (flattenBuckets table).ret.toList = table.toList.flatten := by
  simpa only [flattenBuckets, ← Vector.foldlM_toList, Array.toList_empty, List.nil_append]
    using flatten_fold_ret table.toList (#[] : Array α)

private lemma bucket_sort_perm {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] (xs : Array R)
    (hx : ∀ x ∈ xs.toList, x ∈ Ico (0 : R) 1) :
    (bucketSort xs hx).ret.toList.Perm xs.toList := by
  by_cases hn : 0 < xs.size
  · simp only [bucketSort, dite_eq_left hn, TimeM.ret_bind]
    rw [flatten_bucket_ret]
    refine (sorted_bucket_perm _).trans ?_
    simpa using place_bucket_perm xs hx hn (_root_.Vector.replicate xs.size [])
  · have hnil : xs = #[] := Array.size_eq_zero_iff.mp (by omega)
    subst xs
    simp [bucketSort]

private lemma place_bucket_mem {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] (xs : Array R)
    (hx : ∀ x ∈ xs.toList, x ∈ Ico (0 : R) 1) (hn : 0 < xs.size)
    (i : Fin xs.size) (x : R) :
    x ∈ (placeBuckets xs hx hn (_root_.Vector.replicate xs.size [])).ret.get i ↔
      x ∈ xs.toList ∧ Nat.floor ((xs.size : R) * x) = i.val := by
  rw [place_bucket_get]
  simp [Vector.get]

private lemma classifier_order {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] (n : Nat) {x y : R}
    (hfloor : Nat.floor ((n : R) * x) < Nat.floor ((n : R) * y)) : x ≤ y := by
  by_contra h
  have hyx : y ≤ x := (lt_of_not_ge h).le
  exact not_lt_of_ge (Nat.floor_mono (mul_le_mul_of_nonneg_left hyx (Nat.cast_nonneg n))) hfloor

private lemma sorted_bucket_cross {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] (xs : Array R)
    (hx : ∀ x ∈ xs.toList, x ∈ Ico (0 : R) 1) (hn : 0 < xs.size) :
    List.Pairwise (fun b₁ b₂ => ∀ x ∈ (TimeM.insertionSort b₁).ret,
      ∀ y ∈ (TimeM.insertionSort b₂).ret, x ≤ y)
      (placeBuckets xs hx hn (_root_.Vector.replicate xs.size [])).ret.toList := by
  let placed := (placeBuckets xs hx hn (_root_.Vector.replicate xs.size [])).ret
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij x hxi y hyj
  have hib : i < xs.size := by simpa using hi
  have hjb : j < xs.size := by simpa using hj
  have hxi' : x ∈ placed.get ⟨i, by simpa using hi⟩ := by
    change x ∈ placed[i]
    rw [← Vector.getElem_toList (xs := placed) (i := i) (by simpa using hib)]
    exact (TimeM.insertionSort_perm placed.toList[i]).mem_iff.mp hxi
  have hyj' : y ∈ placed.get ⟨j, by simpa using hj⟩ := by
    change y ∈ placed[j]
    rw [← Vector.getElem_toList (xs := placed) (i := j) (by simpa using hjb)]
    exact (TimeM.insertionSort_perm placed.toList[j]).mem_iff.mp hyj
  have hxfloor := ((place_bucket_mem xs hx hn ⟨i, by simpa using hi⟩ x).mp hxi').2
  have hyfloor := ((place_bucket_mem xs hx hn ⟨j, by simpa using hj⟩ y).mp hyj').2
  apply classifier_order xs.size
  simpa only [hxfloor, hyfloor] using hij

private lemma insertion_table_sorted {R : Type} [LinearOrder R] (table : List (List R))
    (hcross : List.Pairwise (fun b₁ b₂ => ∀ x ∈ (TimeM.insertionSort b₁).ret,
      ∀ y ∈ (TimeM.insertionSort b₂).ret, x ≤ y) table) :
    List.Pairwise (fun x y => x ≤ y)
      (table.map (fun bucket => (TimeM.insertionSort bucket).ret)).flatten := by
  apply List.pairwise_flatten.mpr
  refine ⟨?_, List.pairwise_map.mpr hcross⟩
  intro bucket hb
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp hb
  exact TimeM.insertionSort_sorted original

private lemma bucket_sort_sorted {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] (xs : Array R)
    (hx : ∀ x ∈ xs.toList, x ∈ Ico (0 : R) 1) :
    List.Pairwise (fun x y => x ≤ y) (bucketSort xs hx).ret.toList := by
  by_cases hn : 0 < xs.size
  · simp only [bucketSort, dite_eq_left hn, TimeM.ret_bind]
    rw [flatten_bucket_ret]
    have h := congrArg TimeM.ret (vector_mapM_toList (fun bucket => do
      ✓
      TimeM.insertionSort bucket)
        (placeBuckets xs hx hn (_root_.Vector.replicate xs.size [])).ret)
    simp only [TimeM.ret_map, list_mapM_ret, TimeM.ret_bind] at h
    rw [h]
    exact insertion_table_sorted _ (sorted_bucket_cross xs hx hn)
  · have hnil : xs = #[] := Array.size_eq_zero_iff.mp (by omega)
    subst xs
    simp [bucketSort]

private lemma list_mapM_time {α β : Type} (f : α → TimeM Nat β) (xs : List α) :
    (xs.mapM f).time = (xs.map (fun x => (f x).time)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.mapM_cons, ih]

private lemma push_fold_time {α : Type} (xs : List α) (initial : Array α) :
    (xs.foldlM (m := TimeM Nat) (fun output x => do
      ✓
      return output.push x) initial).time = xs.length := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldlM_cons, TimeM.time_bind, TimeM.time_tick]
      rw [ih]
      simp [Nat.add_comm]

private lemma flatten_fold_time {α : Type} (table : List (List α)) (initial : Array α) :
    (table.foldlM (m := TimeM Nat) (fun output bucket => do
      ✓
      bucket.foldlM (m := TimeM Nat) (fun output x => do
        ✓
        return output.push x) output) initial).time = table.length + table.flatten.length := by
  induction table generalizing initial with
  | nil => simp
  | cons bucket table ih =>
      simp only [List.foldlM_cons, TimeM.time_bind, TimeM.time_tick]
      rw [push_fold_time, ih]
      simp
      omega

private lemma flatten_bucket_time {α : Type} {n : Nat}
    (table : _root_.Vector (List α) n) :
    (flattenBuckets table).time = n + table.toList.flatten.length := by
  simpa only [flattenBuckets, ← Vector.foldlM_toList, Vector.length_toList]
    using flatten_fold_time table.toList (#[] : Array α)

private lemma sorted_bucket_time {R : Type} [LinearOrder R] {n : Nat}
    (table : _root_.Vector (List R) n) :
    (table.mapM (m := TimeM Nat) (fun bucket => do
      ✓
      TimeM.insertionSort bucket)).time =
        n + (table.toList.map (fun bucket => (TimeM.insertionSort bucket).time)).sum := by
  have h := congrArg TimeM.time (vector_mapM_toList (fun bucket => do
    ✓
    TimeM.insertionSort bucket) table)
  simp only [TimeM.time_map] at h
  rw [h, list_mapM_time]
  simp [List.sum_map_add]

private lemma bucket_sort_time_actual {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] (xs : Array R)
    (hx : ∀ x ∈ xs.toList, x ∈ Ico (0 : R) 1) (hn : 0 < xs.size) :
    (bucketSort xs hx).time = 5 * xs.size +
      ((placeBuckets xs hx hn (_root_.Vector.replicate xs.size [])).ret.toList.map
        (fun bucket => (TimeM.insertionSort bucket).time)).sum := by
  let placed := (placeBuckets xs hx hn (_root_.Vector.replicate xs.size [])).ret
  let sorted := placed.mapM (m := TimeM Nat) (fun bucket => do
    ✓
    TimeM.insertionSort bucket)
  have hperm : sorted.ret.toList.flatten.Perm xs.toList :=
    (sorted_bucket_perm placed).trans (by
      simpa using place_bucket_perm xs hx hn (_root_.Vector.replicate xs.size []))
  have hlength : sorted.ret.toList.flatten.length = xs.size := by
    simpa using hperm.length_eq
  simp only [bucketSort, dite_eq_left hn, TimeM.time_bind, TimeM.time_tick]
  rw [place_bucket_time, sorted_bucket_time, flatten_bucket_time, hlength]
  omega

/-- Exact cost of the accepted saved-bucket executor on every valid array. -/
public theorem bucketSort_time {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] (xs : Array R)
    (hx : ∀ x ∈ xs.toList, x ∈ Ico (0 : R) 1) :
    (bucketSort xs hx).time = 5 * xs.size +
      ∑ i : Fin xs.size, (insertionSort
        ((xs.toList.filter
          (fun x => decide (Nat.floor ((xs.size : R) * x) = i.val))).reverse)).time := by
  by_cases hn : 0 < xs.size
  · rw [bucket_sort_time_actual xs hx hn]
    have hv (table : _root_.Vector (List R) xs.size) :
        table.toList = List.ofFn (fun i => table.get i) := by
      change table.toList = List.ofFn (fun i => table[i.val])
      rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
    rw [hv, List.map_ofFn, List.sum_ofFn]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Function.comp_apply, place_bucket_get]
    simp [Vector.get]
  · have hnil : xs = #[] := Array.size_eq_zero_iff.mp (by omega)
    subst xs
    simp [bucketSort]

/-- Every valid array pays the five mandatory saved-bucket phase events per input. -/
public theorem bucketSort_time_lower {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] (xs : Array R)
    (hx : ∀ x ∈ xs.toList, x ∈ Ico (0 : R) 1) :
    5 * xs.size ≤ (bucketSort xs hx).time := by
  rw [bucketSort_time]
  exact Nat.le_add_right _ _

/-- Squared actual bucket occupancies bound the cost for arbitrary valid arrays. -/
public theorem bucketSort_time_le_sum_sq {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] (xs : Array R)
    (hx : ∀ x ∈ xs.toList, x ∈ Ico (0 : R) 1) :
    (bucketSort xs hx).time ≤ 5 * xs.size +
      ∑ i : Fin xs.size, (xs.toList.countP
        (fun x => decide (Nat.floor ((xs.size : R) * x) = i.val))) ^ 2 := by
  rw [bucketSort_time]
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum
  intro i _
  let bucket := (xs.toList.filter
    (fun x => decide (Nat.floor ((xs.size : R) * x) = i.val))).reverse
  have ht := insertionSort_time bucket
  have hs : bucket.length * (bucket.length - 1) / 2 ≤ bucket.length * bucket.length :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  simpa only [bucket, List.length_reverse, ← List.countP_eq_length_filter, pow_two]
    using ht.trans hs

/-- The empty saved-bucket computation returns the empty array with zero cost. -/
public theorem bucketSort_empty {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R]
    (hx : ∀ x ∈ (#[] : Array R).toList, x ∈ Ico (0 : R) 1) :
    bucketSort #[] hx = (pure #[] : TimeM Nat (Array R)) :=
  empty_computation hx

/-- The saved-bucket computation preserves every input occurrence. -/
public theorem bucketSort_perm {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] (xs : Array R)
    (hx : ∀ x ∈ xs.toList, x ∈ Ico (0 : R) 1) :
    (bucketSort xs hx).ret.toList.Perm xs.toList := bucket_sort_perm xs hx

/-- Sorting the saved buckets yields a globally nondecreasing array. -/
public theorem bucketSort_sorted {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] (xs : Array R)
    (hx : ∀ x ∈ xs.toList, x ∈ Ico (0 : R) 1) :
    List.Pairwise (fun x y => x ≤ y) (bucketSort xs hx).ret.toList :=
  bucket_sort_sorted xs hx

end Cslib.Algorithms.Lean.TimeM
