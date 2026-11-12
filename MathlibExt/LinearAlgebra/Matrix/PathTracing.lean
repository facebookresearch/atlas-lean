/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Path tracing for recursive linear systems

For a strictly lower triangular matrix `B` indexed by `Fin n` (a recursive linear structural
equation model `X = B X + e` on a directed acyclic graph ordered by `Fin n`, where `B i j` is
the coefficient of the edge `j → i`), the matrix `1 - B` is invertible and each entry of its
inverse is a sum over directed paths: `((1 - B)⁻¹) i j` is the sum, over the directed paths from
`j` to `i`, of the products of the edge coefficients along the path (Wright's path-tracing rule;
Evans, *Graphical Models*, §8.6).

## Main definitions

* `Matrix.pathWeight B p`: the product of the edge coefficients along a list of nodes `p`.
* `Matrix.increasingPaths j i`: the strictly increasing lists of nodes from `j` to `i`.

## Main results

* `Matrix.mem_increasingPaths_of_isChain` and `Matrix.isChain_of_mem_increasingPaths`: for a
  strictly lower triangular `B`, every directed path from `j` to `i` lies in
  `increasingPaths j i`, and the other lists there have weight `0`.
* `Matrix.inv_one_sub_apply_eq_sum_pathWeight`: **path tracing**,
  `((1 - B)⁻¹) i j = ∑ p ∈ increasingPaths j i, pathWeight B p`.

The causal reading of this entry as the total effect of `X_j` on `X_i` under the intervention
`do(X_j = a)` is in the linear structural equation model development (`LinearSEM.integral_doSolve`,
CA08.T03).

## References

* S. Wright, *The method of path coefficients*, Ann. Math. Statist. 5 (1934), 161–215.
* R. J. Evans, *Graphical Models*, lecture notes, University of Oxford, ch. 8, §8.6.
-/

@[expose] public section

namespace Matrix

private theorem pairwise_head_mem {α : Type*} {R S : α → α → Prop}
    (ofR : ∀ {a b : α}, R a b → S a b) (reflS : ∀ {a : α}, S a a)
    {p : List α} (hp : p.Pairwise R) {h : α} (hh : p.head? = some h)
    {x : α} (hx : x ∈ p) : S h x := by
  obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.mp hh
  rcases List.mem_cons.mp hx with rfl | hmem
  · exact reflS
  · exact ofR ((List.pairwise_cons.mp hp).1 x hmem)

private theorem pairwise_getLast_mem {α : Type*} {R S : α → α → Prop}
    (transRS : ∀ {a b c : α}, R a b → S b c → S a c) (reflS : ∀ {a : α}, S a a)
    {p : List α} : p.Pairwise R → ∀ {t x : α}, p.getLast? = some t → x ∈ p → S x t := by
  induction p with
  | nil => intro hp t x ht hx; simp at hx
  | cons a rest ih =>
    intro hp t x ht hx
    cases rest with
    | nil =>
      simp at hx; subst hx
      simp at ht; subst ht
      exact reflS
    | cons b rest' =>
      have hpair := List.pairwise_cons.mp hp
      have ht' : (b :: rest').getLast? = some t := by
        rwa [List.getLast?_cons_cons] at ht
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact transRS (hpair.1 b List.mem_cons_self) (ih hpair.2 ht' List.mem_cons_self)
      · exact ih hpair.2 ht' hmem

/-- The weight of a list of nodes `[v₀, v₁, …, vₘ]` read as the directed path
`v₀ → v₁ → ⋯ → vₘ` for the coefficient matrix `B`, where `B i j` is the coefficient of node
`j` in the equation of node `i` (the edge `j → i`): the product
`B v₁ v₀ * B v₂ v₁ * ⋯ * B vₘ vₘ₋₁` of the edge coefficients. A one-node list has weight `1`. -/
def pathWeight {n : ℕ} {R : Type*} [Monoid R] (B : Matrix (Fin n) (Fin n) R)
    (p : List (Fin n)) : R :=
  (List.zipWith (fun u v => B v u) p p.tail).prod

/-- The strictly increasing lists of nodes from `j` to `i`: for each subset `S` of the interval
`[j, i]` containing `j` and `i`, the list of the elements of `S` in increasing order. When `B`
is strictly lower triangular every directed path from `j` to `i` is one of these lists
(`mem_increasingPaths_of_isChain`), and a list here that is not a directed path has weight `0`
(`isChain_of_mem_increasingPaths`). -/
def increasingPaths {n : ℕ} (j i : Fin n) : Finset (List (Fin n)) :=
  ((Finset.Icc j i).powerset.filter fun S => j ∈ S ∧ i ∈ S).image fun S => S.sort

private theorem icc_powerset_filter_eq {n : ℕ} (j i : Fin n) :
    ((Finset.Icc j i).powerset.filter fun S => j ∈ S ∧ i ∈ S)
      = (Finset.univ : Finset (Finset (Fin n))).filter
        fun S => j ∈ S ∧ i ∈ S ∧ ∀ k ∈ S, j ≤ k ∧ k ≤ i := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hsub, hj, hi⟩
    exact ⟨hj, hi, fun k hk => Finset.mem_Icc.mp (hsub hk)⟩
  · rintro ⟨hj, hi, hb⟩
    refine ⟨?_, hj, hi⟩
    intro k hk
    exact Finset.mem_Icc.mpr (hb k hk)

/-- `increasingPaths j i` as the image of the subsets of all nodes that contain `j` and `i` and
lie in `[j, i]`. -/
theorem increasingPaths_eq_filter_univ {n : ℕ} (j i : Fin n) :
    increasingPaths j i
      = (((Finset.univ : Finset (Finset (Fin n))).filter
        fun S => j ∈ S ∧ i ∈ S ∧ ∀ k ∈ S, j ≤ k ∧ k ≤ i).image
        fun S => S.sort) := by
  unfold increasingPaths
  rw [icc_powerset_filter_eq]

private def pathSumMatrix {n : ℕ} {R : Type*} [CommRing R] (B : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => ∑ p ∈ increasingPaths j i, pathWeight B p

private theorem isChain_of_pathWeight_ne_zero {n : ℕ} {R : Type*} [MonoidWithZero R]
    {B : Matrix (Fin n) (Fin n) R} {p : List (Fin n)}
    (hw : pathWeight B p ≠ 0) :
    p.IsChain fun u v => B v u ≠ 0 := by
  revert hw
  induction p with
  | nil => intro hw; exact List.IsChain.nil
  | cons a rest ih =>
    intro hw
    cases rest with
    | nil => exact List.IsChain.singleton _
    | cons b rest' =>
      rw [List.isChain_cons_cons]
      simp only [pathWeight, List.tail_cons, List.zipWith_cons_cons, List.prod_cons] at hw
      constructor
      · intro hcon
        apply hw
        simp only [hcon, zero_mul]
      · apply ih
        change (List.zipWith (fun u v => B v u) (b :: rest') rest').prod ≠ 0
        intro hcon
        apply hw
        simp only [hcon, mul_zero]

/-- Every directed path from `j` to `i` in the graph of a strictly lower triangular `B` (a list
whose consecutive nodes `u, v` satisfy `B v u ≠ 0`) is one of `increasingPaths j i`. -/
theorem mem_increasingPaths_of_isChain {n : ℕ} {R : Type*} [Zero R]
    {B : Matrix (Fin n) (Fin n) R} (hB : ∀ i j, i ≤ j → B i j = 0) {j i : Fin n}
    {p : List (Fin n)} (hp : p.IsChain fun u v => B v u ≠ 0) (hj : p.head? = some j)
    (hi : p.getLast? = some i) :
    p ∈ increasingPaths j i := by
  have hlt : p.IsChain (· < ·) :=
    hp.imp (fun {a b} h => lt_of_not_ge (fun hle => h (hB _ _ hle)))
  have hpw : p.Pairwise (· < ·) := hlt.pairwise
  have hnodup : p.Nodup := hpw.nodup
  have hle : p.Pairwise (· ≤ ·) := hpw.imp (fun {a b} h => le_of_lt h)
  have hsort : p.toFinset.sort (fun a b => a ≤ b) = p :=
    (List.toFinset_sort _ hnodup).mpr hle
  rw [increasingPaths_eq_filter_univ]
  apply Finset.mem_image.mpr
  refine ⟨p.toFinset, ?_, hsort⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
  · exact List.mem_toFinset.mpr (List.mem_of_head? hj)
  · exact List.mem_toFinset.mpr (List.mem_of_getLast? hi)
  · intro k hk
    rw [List.mem_toFinset] at hk
    constructor
    · exact pairwise_head_mem (fun {a b} (h : a < b) => le_of_lt h) (fun {a} => le_rfl)
        hpw hj hk
    · exact pairwise_getLast_mem
        (fun {a b c} (h1 : a < b) (h2 : b ≤ c) => le_trans (le_of_lt h1) h2)
        (fun {a} => le_rfl) hpw hi hk

/-- A list of `increasingPaths j i` with nonzero weight is a directed path from `j` to `i`. -/
theorem isChain_of_mem_increasingPaths {n : ℕ} {R : Type*} [MonoidWithZero R]
    {B : Matrix (Fin n) (Fin n) R} {j i : Fin n} {p : List (Fin n)}
    (hp : p ∈ increasingPaths j i) (hw : pathWeight B p ≠ 0) :
    (p.IsChain fun u v => B v u ≠ 0) ∧ p.head? = some j ∧ p.getLast? = some i := by
  rw [increasingPaths_eq_filter_univ] at hp
  obtain ⟨S, hSmem, hsort⟩ := Finset.mem_image.mp hp
  have hsort' : S.sort (fun a b => a ≤ b) = p := hsort
  rw [Finset.mem_filter] at hSmem
  obtain ⟨-, hjS, hiS, hbS⟩ := hSmem
  have hpwS : (S.sort (fun a b => a ≤ b)).Pairwise (· ≤ ·) :=
    Finset.pairwise_sort S (fun a b => a ≤ b)
  have hsortne : S.sort (fun a b => a ≤ b) ≠ [] := by
    intro hnil
    have h := Finset.sort_toFinset S (fun a b => a ≤ b)
    rw [hnil] at h
    simp at h
    subst h
    exact Finset.notMem_empty j hjS
  have hchain : p.IsChain fun u v => B v u ≠ 0 := isChain_of_pathWeight_ne_zero hw
  have hhead : p.head? = some j := by
    have hne : (S.sort (fun a b => a ≤ b)).head? ≠ none :=
      fun hnone => hsortne (List.head?_eq_none_iff.mp hnone)
    obtain ⟨h', hh'⟩ := Option.ne_none_iff_exists'.mp hne
    have h'S : h' ∈ S := (Finset.mem_sort _).mp (List.mem_of_head? hh')
    have jmem : j ∈ S.sort (fun a b => a ≤ b) := (Finset.mem_sort _).mpr hjS
    have hjh' : j ≤ h' := (hbS h' h'S).1
    have hh'j : h' ≤ j :=
      pairwise_head_mem (fun {a b} (h : a ≤ b) => h) (fun {a} => le_rfl) hpwS hh' jmem
    have heq : h' = j := le_antisymm hh'j hjh'
    subst heq
    rwa [← hsort']
  have hlast : p.getLast? = some i := by
    have hne : (S.sort (fun a b => a ≤ b)).getLast? ≠ none :=
      fun hnone => hsortne (List.getLast?_eq_none_iff.mp hnone)
    obtain ⟨t', ht'⟩ := Option.ne_none_iff_exists'.mp hne
    have t'S : t' ∈ S := (Finset.mem_sort _).mp (List.mem_of_getLast? ht')
    have imem : i ∈ S.sort (fun a b => a ≤ b) := (Finset.mem_sort _).mpr hiS
    have ht'i : t' ≤ i := (hbS t' t'S).2
    have hit' : i ≤ t' :=
      pairwise_getLast_mem (fun {a b c} (h1 : a ≤ b) (h2 : b ≤ c) => le_trans h1 h2)
        (fun {a} => le_rfl) hpwS ht' imem
    have heq : t' = i := le_antisymm ht'i hit'
    subst heq
    rwa [← hsort']
  exact ⟨hchain, hhead, hlast⟩

private theorem pathWeight_cons_cons {n : ℕ} {R : Type*} [CommRing R]
    {B : Matrix (Fin n) (Fin n) R} (a b : Fin n) (M : List (Fin n)) :
    pathWeight B (a :: b :: M) = B b a * pathWeight B (b :: M) := by
  simp [pathWeight]

private theorem pathWeight_singleton {n : ℕ} {R : Type*} [CommRing R]
    {B : Matrix (Fin n) (Fin n) R} (x : Fin n) :
    pathWeight B [x] = 1 := by
  simp [pathWeight]

private theorem pathWeight_pair {n : ℕ} {R : Type*} [CommRing R]
    {B : Matrix (Fin n) (Fin n) R} (k x : Fin n) :
    pathWeight B [k, x] = B x k := by
  simp [pathWeight]

private theorem pathWeight_append_last {n : ℕ} {R : Type*} [CommRing R]
    {B : Matrix (Fin n) (Fin n) R} (L' : List (Fin n)) (k x : Fin n) :
    pathWeight B (L' ++ [k, x]) = pathWeight B (L' ++ [k]) * B x k := by
  induction L' with
  | nil => simp [pathWeight]
  | cons a L'' ih =>
    cases L'' with
    | nil => simp [pathWeight]
    | cons b L''' =>
      simp only [List.cons_append] at ih
      have h1 : (a :: b :: L''') ++ [k, x] = a :: b :: (L''' ++ [k, x]) := by simp
      have h2 : (a :: b :: L''') ++ [k] = a :: b :: (L''' ++ [k]) := by simp
      rw [h1, h2, pathWeight_cons_cons, pathWeight_cons_cons, ih, mul_assoc]

private theorem sort_insert_max {n : ℕ} (T' : Finset (Fin n)) (i : Fin n)
    (hlt : ∀ x ∈ T', x < i) (hni : i ∉ T') :
    (insert i T').sort (fun a b => a ≤ b) = T'.sort (fun a b => a ≤ b) ++ [i] := by
  have hLnodup : (T'.sort (fun a b => a ≤ b) ++ [i]).Nodup := by
    rw [List.nodup_append]
    refine ⟨Finset.sort_nodup _ _, List.nodup_singleton _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    have haT : a ∈ T' := (Finset.mem_sort _).mp ha
    intro heq
    rw [heq] at haT
    exact hni haT
  have hLpair : (T'.sort (fun a b => a ≤ b) ++ [i]).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨Finset.pairwise_sort _ _, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact le_of_lt (hlt a ((Finset.mem_sort _).mp ha))
  have hLfin : (T'.sort (fun a b => a ≤ b) ++ [i]).toFinset = insert i T' := by
    rw [List.toFinset_append, Finset.sort_toFinset, Finset.insert_eq, Finset.union_comm]
    simp
  have hsort := (List.toFinset_sort (fun a b => a ≤ b) hLnodup).mpr hLpair
  rw [hLfin] at hsort
  exact hsort

/-- There are no increasing paths from `j` to `i` when `i < j`. -/
theorem increasingPaths_empty_of_not_le {n : ℕ} {j i : Fin n} (h : ¬ j ≤ i) :
    increasingPaths j i = ∅ := by
  have hF : (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => j ∈ S ∧ i ∈ S ∧ ∀ k ∈ S, j ≤ k ∧ k ≤ i) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro T _ hT
    exact h (hT.2.2 j hT.1).2
  rw [increasingPaths_eq_filter_univ, hF, Finset.image_empty]

/-- The only increasing path from `j` to itself is `[j]`. -/
theorem increasingPaths_self {n : ℕ} (j : Fin n) :
    increasingPaths j j = {[j]} := by
  have hF : (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => j ∈ S ∧ j ∈ S ∧ ∀ k ∈ S, j ≤ k ∧ k ≤ j) = {{j}} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, Finset.mem_singleton_self j, Finset.mem_singleton_self j, ?_⟩
      intro k hk
      rw [Finset.mem_singleton] at hk
      subst hk
      exact ⟨le_rfl, le_rfl⟩
    · intro T hT
      rw [Finset.mem_filter] at hT
      obtain ⟨-, hjT, -, hbT⟩ := hT
      apply Finset.Subset.antisymm _ (Finset.singleton_subset_iff.mpr hjT)
      intro x hx
      rw [Finset.mem_singleton]
      exact le_antisymm (hbT x hx).2 (hbT x hx).1
  rw [increasingPaths_eq_filter_univ, hF, Finset.image_singleton, Finset.sort_singleton]

private theorem sum_increasingPaths_eq_sum_sort {n : ℕ} {R : Type*} [CommRing R]
    {B : Matrix (Fin n) (Fin n) R} (j i : Fin n) :
    (∑ p ∈ increasingPaths j i, pathWeight B p)
    = ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
        (fun S => j ∈ S ∧ i ∈ S ∧ ∀ k ∈ S, j ≤ k ∧ k ≤ i),
        pathWeight B (S.sort (fun a b => a ≤ b)) := by
  rw [increasingPaths_eq_filter_univ]
  apply Finset.sum_image
  intro S _ T _ hST
  have hST' : S.sort (fun a b => a ≤ b) = T.sort (fun a b => a ≤ b) := hST
  have hS := Finset.sort_toFinset S (fun a b => a ≤ b)
  have hT := Finset.sort_toFinset T (fun a b => a ≤ b)
  rw [hST'] at hS
  exact hS.symm.trans hT

private theorem pathWeight_append_of_getLast {n : ℕ} {R : Type*} [CommRing R]
    {B : Matrix (Fin n) (Fin n) R} {L : List (Fin n)} {x k : Fin n}
    (hL : L.getLast? = some k) :
    pathWeight B (L ++ [x]) = pathWeight B L * B x k := by
  obtain ⟨L', rfl⟩ := List.getLast?_eq_some_iff.mp hL
  have happ : (L' ++ [k]) ++ [x] = L' ++ [k, x] := by simp
  rw [happ]
  exact pathWeight_append_last L' k x

private theorem sort_getLast_eq_max {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    (S.sort (fun a b => a ≤ b)).getLast? = some (S.max' hS) := by
  have ⟨x0, hx0⟩ := hS
  have hsortne : S.sort (fun a b => a ≤ b) ≠ [] := by
    intro hnil
    have h := Finset.sort_toFinset S (fun a b => a ≤ b)
    rw [hnil] at h
    simp at h
    subst h
    exact Finset.notMem_empty x0 hx0
  have hne : (S.sort (fun a b => a ≤ b)).getLast? ≠ none :=
    fun hnone => hsortne (List.getLast?_eq_none_iff.mp hnone)
  obtain ⟨t', ht'⟩ := Option.ne_none_iff_exists'.mp hne
  have hpwS : (S.sort (fun a b => a ≤ b)).Pairwise (· ≤ ·) :=
    Finset.pairwise_sort S (fun a b => a ≤ b)
  have t'S : t' ∈ S := (Finset.mem_sort _).mp (List.mem_of_getLast? ht')
  have ht'max : t' ≤ S.max' hS := Finset.le_max' _ _ t'S
  have hmaxt' : S.max' hS ≤ t' :=
    pairwise_getLast_mem (fun {a b c} (h1 : a ≤ b) (h2 : b ≤ c) => le_trans h1 h2)
      (fun {a} => le_rfl) hpwS ht' ((Finset.mem_sort _).mpr (Finset.max'_mem _ _))
  have heq : t' = S.max' hS := le_antisymm ht'max hmaxt'
  subst heq
  exact ht'

private theorem pathsum_recurrence {n : ℕ} {R : Type*} [CommRing R]
    {B : Matrix (Fin n) (Fin n) R} (hB : ∀ i j, i ≤ j → B i j = 0) (i j : Fin n) :
    (∑ p ∈ increasingPaths j i, pathWeight B p)
    = (1 : Matrix (Fin n) (Fin n) R) i j
      + ∑ k, B i k * (∑ p ∈ increasingPaths j k, pathWeight B p) := by
  rcases lt_trichotomy j i with hji | heq | hij
  · -- Case j < i: main bijection
    have h1ij : (1 : Matrix (Fin n) (Fin n) R) i j = 0 := by
      simp [ne_of_gt hji]
    rw [h1ij, zero_add, sum_increasingPaths_eq_sum_sort]
    have hvan : ∀ k ∈ (Finset.univ : Finset (Fin n)), k ∉ Finset.Ico j i →
        B i k * (∑ p ∈ increasingPaths j k, pathWeight B p) = 0 := by
      intro k _ hkIco
      rw [Finset.mem_Ico] at hkIco
      by_cases hjk : j ≤ k
      · have hki : i ≤ k := le_of_not_gt (fun h => hkIco ⟨hjk, h⟩)
        rw [hB i k hki, zero_mul]
      · have hempty : increasingPaths j k = ∅ := increasingPaths_empty_of_not_le hjk
        rw [hempty, Finset.sum_empty, mul_zero]
    rw [← Finset.sum_subset (Finset.subset_univ _) hvan]
    have hexpand : ∀ k ∈ Finset.Ico j i, B i k * (∑ p ∈ increasingPaths j k, pathWeight B p)
        = ∑ T' ∈ ((Finset.univ : Finset (Finset (Fin n))).filter
            (fun S => j ∈ S ∧ k ∈ S ∧ ∀ x ∈ S, j ≤ x ∧ x ≤ k)),
          B i k * pathWeight B (T'.sort (fun a b => a ≤ b)) := by
      intro k _
      rw [sum_increasingPaths_eq_sum_sort, Finset.mul_sum]
    rw [Finset.sum_congr rfl hexpand]
    have hsigma : (∑ k ∈ Finset.Ico j i, ∑ T' ∈ ((Finset.univ : Finset (Finset (Fin n))).filter
            (fun S => j ∈ S ∧ k ∈ S ∧ ∀ x ∈ S, j ≤ x ∧ x ≤ k)),
          B i k * pathWeight B (T'.sort (fun a b => a ≤ b)))
        = ∑ x ∈ (Finset.Ico j i).sigma (fun k => ((Finset.univ : Finset (Finset (Fin n))).filter
            (fun S => j ∈ S ∧ k ∈ S ∧ ∀ x ∈ S, j ≤ x ∧ x ≤ k))),
          B i x.1 * pathWeight B (x.2.sort (fun a b => a ≤ b)) :=
      (Finset.sum_sigma _ _ (fun x : Sigma (fun _ : Fin n => Finset (Fin n)) =>
        B i x.1 * pathWeight B (x.2.sort (fun a b => a ≤ b)))).symm
    rw [hsigma]
    have herase_ne : ∀ T ∈ ((Finset.univ : Finset (Finset (Fin n))).filter
        (fun S => j ∈ S ∧ i ∈ S ∧ ∀ x ∈ S, j ≤ x ∧ x ≤ i)), (T.erase i).Nonempty := by
      intro T hT
      have hT' := Finset.mem_filter.mp hT
      exact ⟨j, Finset.mem_erase.mpr ⟨ne_of_lt hji, hT'.2.1⟩⟩
    refine Finset.sum_bij'
      (fun T hT => (⟨(T.erase i).max' (herase_ne T hT), T.erase i⟩ :
        Sigma (fun _ : Fin n => Finset (Fin n))))
      (fun x _ => insert i x.2) ?_ ?_ ?_ ?_ ?_
    · -- fwd maps into sigma
      intro T hT
      have hT' := Finset.mem_filter.mp hT
      obtain ⟨-, hjT, hiT, hbT⟩ := hT'
      have kmem : (T.erase i).max' (herase_ne T hT) ∈ T.erase i :=
        Finset.max'_mem _ _
      have kT : (T.erase i).max' (herase_ne T hT) ∈ T :=
        Finset.mem_of_mem_erase kmem
      simp only [Finset.mem_sigma]
      constructor
      · rw [Finset.mem_Ico]
        exact ⟨(hbT _ kT).1,
          lt_of_le_of_ne (hbT _ kT).2 (Finset.mem_erase.mp kmem).1⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
        · exact Finset.mem_erase.mpr ⟨ne_of_lt hji, hjT⟩
        · exact kmem
        · intro x hx
          exact ⟨(hbT x (Finset.mem_of_mem_erase hx)).1, Finset.le_max' _ _ hx⟩
    · -- bwd maps into F
      intro x hx
      have hx' := Finset.mem_sigma.mp hx
      obtain ⟨hkIco, hT'⟩ := hx'
      obtain ⟨hjk, hki⟩ := Finset.mem_Ico.mp hkIco
      have hT'' := Finset.mem_filter.mp hT'
      obtain ⟨-, hjT', hkT', hbT'⟩ := hT''
      change insert i x.2 ∈ _
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, Finset.mem_insert_of_mem hjT',
        Finset.mem_insert_self i x.2, ?_⟩
      intro y hy
      have hy' := Finset.mem_insert.mp hy
      rcases hy' with rfl | hyT'
      · exact ⟨le_trans hjk (le_of_lt hki), le_rfl⟩
      · exact ⟨(hbT' y hyT').1, le_trans (hbT' y hyT').2 (le_of_lt hki)⟩
    · -- bwd after fwd
      intro T hT
      have hT' := Finset.mem_filter.mp hT
      obtain ⟨-, -, hiT, -⟩ := hT'
      change insert i (T.erase i) = T
      exact Finset.insert_erase hiT
    · -- fwd after bwd
      intro x hx
      have hx' := Finset.mem_sigma.mp hx
      obtain ⟨hkIco, hT'⟩ := hx'
      obtain ⟨hjk, hki⟩ := Finset.mem_Ico.mp hkIco
      have hT'' := Finset.mem_filter.mp hT'
      obtain ⟨-, hjT', hkT', hbT'⟩ := hT''
      have hni : i ∉ x.2 := fun hiT' => absurd (hbT' i hiT').2 (not_le_of_gt hki)
      have herase : (insert i x.2).erase i = x.2 := Finset.erase_insert hni
      have hmax : ∀ h : ((insert i x.2).erase i).Nonempty,
          ((insert i x.2).erase i).max' h = x.1 := by
        intro h
        apply le_antisymm
        · exact Finset.max'_le _ _ _
            (fun y hy => (hbT' y (by rwa [herase] at hy)).2)
        · exact Finset.le_max' _ _
            (Finset.mem_erase.mpr ⟨ne_of_lt hki, Finset.mem_insert_of_mem hkT'⟩)
      change (⟨((insert i x.2).erase i).max' _, (insert i x.2).erase i⟩ :
        Sigma (fun _ : Fin n => Finset (Fin n))) = ⟨x.1, x.2⟩
      rw [hmax, herase]
    · -- values match
      intro T hT
      have hT' := Finset.mem_filter.mp hT
      obtain ⟨-, hjT, hiT, hbT⟩ := hT'
      have hlt : ∀ x ∈ T.erase i, x < i := by
        intro x hx
        have hx' := Finset.mem_erase.mp hx
        exact lt_of_le_of_ne (hbT x hx'.2).2 hx'.1
      have hni : i ∉ T.erase i := fun h => (Finset.mem_erase.mp h).1 rfl
      have hsortT : T.sort (fun a b => a ≤ b)
          = (T.erase i).sort (fun a b => a ≤ b) ++ [i] := by
        have h := sort_insert_max (T.erase i) i hlt hni
        rwa [Finset.insert_erase hiT] at h
      have hlast : ((T.erase i).sort (fun a b => a ≤ b)).getLast?
          = some ((T.erase i).max' (herase_ne T hT)) :=
        sort_getLast_eq_max _ (herase_ne T hT)
      have hwfactor : pathWeight B (T.sort (fun a b => a ≤ b))
          = B i ((T.erase i).max' (herase_ne T hT))
            * pathWeight B ((T.erase i).sort (fun a b => a ≤ b)) := by
        rw [hsortT, pathWeight_append_of_getLast hlast]
        exact mul_comm _ _
      change pathWeight B (T.sort (fun a b => a ≤ b))
        = B i ((T.erase i).max' (herase_ne T hT))
          * pathWeight B ((T.erase i).sort (fun a b => a ≤ b))
      exact hwfactor
  · -- Case j = i
    subst heq
    have hLHS : (∑ p ∈ increasingPaths j j, pathWeight B p) = 1 := by
      rw [increasingPaths_self, Finset.sum_singleton, pathWeight_singleton]
    have h1ii : (1 : Matrix (Fin n) (Fin n) R) j j = 1 := by
      simp
    have hsum0 : (∑ k, B j k * (∑ p ∈ increasingPaths j k, pathWeight B p)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hjk : j ≤ k
      · rw [hB j k hjk, zero_mul]
      · have hempty : increasingPaths j k = ∅ := increasingPaths_empty_of_not_le hjk
        rw [hempty, Finset.sum_empty, mul_zero]
    rw [hLHS, h1ii, hsum0, add_zero]
  · -- Case i < j
    have hLHS : (∑ p ∈ increasingPaths j i, pathWeight B p) = 0 := by
      rw [increasingPaths_empty_of_not_le (not_le_of_gt hij), Finset.sum_empty]
    have h1ij : (1 : Matrix (Fin n) (Fin n) R) i j = 0 := by
      simp [ne_of_lt hij]
    have hsum0 : (∑ k, B i k * (∑ p ∈ increasingPaths j k, pathWeight B p)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hik : i ≤ k
      · rw [hB i k hik, zero_mul]
      · have hjk : ¬ j ≤ k := fun h => hik (le_trans (le_of_lt hij) h)
        have hempty : increasingPaths j k = ∅ := increasingPaths_empty_of_not_le hjk
        rw [hempty, Finset.sum_empty, mul_zero]
    rw [hLHS, h1ij, hsum0, add_zero]

/-- **Path tracing** (Wright's rule for recursive linear systems): for a strictly lower
triangular coefficient matrix `B` (a recursive linear structural equation model
`X = B X + ε` on a finite DAG ordered by `Fin n`), the `(i, j)` entry of `(1 - B)⁻¹` is the
sum, over the directed paths from `j` to `i`, of the products of the edge coefficients. -/
theorem inv_one_sub_apply_eq_sum_pathWeight {n : ℕ} {R : Type*} [CommRing R]
    {B : Matrix (Fin n) (Fin n) R} (hB : ∀ i j, i ≤ j → B i j = 0) (i j : Fin n) :
    (1 - B)⁻¹ i j = ∑ p ∈ increasingPaths j i, pathWeight B p := by
  have hprod : (1 - B) * pathSumMatrix B = 1 := by
    ext a b
    simp only [pathSumMatrix, Matrix.mul_apply]
    have hrec := pathsum_recurrence hB a b
    have hkron : (∑ k, (1 : Matrix (Fin n) (Fin n) R) a k
        * (∑ p ∈ increasingPaths b k, pathWeight B p))
        = (∑ p ∈ increasingPaths b a, pathWeight B p) := by
      simp_rw [Matrix.one_apply, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp
    simp_rw [Matrix.sub_apply, sub_mul]
    rw [Finset.sum_sub_distrib, hkron, hrec, add_sub_cancel_right]
  have hinv := Matrix.inv_eq_right_inv hprod
  rw [hinv]
  rfl

end Matrix
