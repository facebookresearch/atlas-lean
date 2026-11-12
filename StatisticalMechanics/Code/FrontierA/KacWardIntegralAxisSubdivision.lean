/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardIntegralAxisWord
import Code.FrontierA.KacWardForwardSubdivision
import Code.FrontierA.KacWardRectilinearPolygonBridge
import Code.FrontierA.KacWardChordPhaseGlue
import Code.Onsager.PeriodicTurnClosure





namespace StatMech.FrontierA

open Set
open scoped BigOperators
open StatMech.Onsager.BaseCase


def kwRawHalfOpenEdge
    {n : ℕ} [NeZero n] (vertex : Fin n → ℂ) (i : Fin n) : Set ℂ :=
  {z | z = vertex i ∨ Sbtw ℝ (vertex i) z (vertex (i + 1))}

theorem KWRawNonbacktrackingSimpleData.halfOpenEdge_subset_closedEdge
    {n : ℕ} [NeZero n] {vertex : Fin n → ℂ}
    (h : KWRawNonbacktrackingSimpleData vertex) (i : Fin n) :
    kwRawHalfOpenEdge vertex i ⊆ kwRawClosedEdge vertex i := by
  rintro z (rfl | hz)
  · exact left_mem_segment ℝ _ _
  · exact mem_segment_iff_wbtw.mpr hz.1

private theorem KWRawNonbacktrackingSimpleData.halfOpenEdge_disjoint_succ
    {n : ℕ} [NeZero n] {vertex : Fin n → ℂ}
    (h : KWRawNonbacktrackingSimpleData vertex) (i : Fin n) :
    Disjoint (kwRawHalfOpenEdge vertex i)
      (kwRawHalfOpenEdge vertex (i + 1)) := by
  have hone : (1 : Fin n) + 1 = 2 := by
    apply Fin.ext
    change (1 % n + 1 % n) % n = 2 % n
    rw [← Nat.add_mod]
  have hi2 : i + 1 + 1 = i + 2 := by
    rw [add_assoc, hone]
  rw [Set.disjoint_left]
  rintro z (hzi | hzi) (hzj | hzj)
  · apply h.edge_ne_zero i
    unfold kwRawEdge
    rw [← hzi, hzj]
    exact sub_self _
  · subst z
    exact h.previous_not_between i (by simpa only [hi2] using hzj)
  · subst z
    exact hzi.ne_right rfl
  · exact Set.disjoint_left.mp (h.adjacent_disjoint i) hzi
      (by simpa only [hi2] using hzj)



theorem KWRawNonbacktrackingSimpleData.halfOpenEdge_disjoint
    {n : ℕ} [NeZero n] {vertex : Fin n → ℂ}
    (h : KWRawNonbacktrackingSimpleData vertex)
    {i j : Fin n} (hij : i ≠ j) :
    Disjoint (kwRawHalfOpenEdge vertex i)
      (kwRawHalfOpenEdge vertex j) := by
  by_cases hnon : KWEdgesNonincident i j
  · exact (h.nonincident_disjoint i j hnon).mono
      (h.halfOpenEdge_subset_closedEdge i)
      (h.halfOpenEdge_subset_closedEdge j)
  · have hadj : i = j + 1 ∨ i + 1 = j := by
      by_contra hnot
      apply hnon
      exact ⟨hij, (not_or.mp hnot).1, (not_or.mp hnot).2⟩
    rcases hadj with hprev | hnext
    · subst i
      exact (h.halfOpenEdge_disjoint_succ j).symm
    · subst j
      exact h.halfOpenEdge_disjoint_succ i


def kwPrefixPositions : List (Fin 4) → List (ℤ × ℤ)
  | [] => []
  | d :: tail => 0 :: (kwPrefixPositions tail).map (stepOf d + ·)

@[simp] theorem kwPrefixPositions_nil : kwPrefixPositions [] = [] := rfl

@[simp] theorem kwPrefixPositions_cons (d : Fin 4) (tail : List (Fin 4)) :
    kwPrefixPositions (d :: tail) =
      0 :: (kwPrefixPositions tail).map (stepOf d + ·) := rfl

@[simp] theorem kwPrefixPositions_length (word : List (Fin 4)) :
    (kwPrefixPositions word).length = word.length := by
  induction word with
  | nil => rfl
  | cons d tail ih => simp [ih]

theorem kwPrefixPositions_append (left right : List (Fin 4)) :
    kwPrefixPositions (left ++ right) =
      kwPrefixPositions left ++
        (kwPrefixPositions right).map
          (((left.map stepOf).sum) + ·) := by
  induction left with
  | nil => simp
  | cons d tail ih =>
      simp only [List.cons_append, kwPrefixPositions_cons, List.map_cons,
        List.sum_cons, ih, List.map_append, List.cons_append]
      simp only [List.map_map, Function.comp_def, add_assoc]

theorem kwPrefixPositions_get
    (word : List (Fin 4)) (k : Fin word.length) :
    (kwPrefixPositions word).get
        ⟨k.val, by simpa using k.isLt⟩ =
      ((word.take k.val).map stepOf).sum := by
  induction word with
  | nil => exact Fin.elim0 k
  | cons d tail ih =>
      refine Fin.cases ?_ (fun q ↦ ?_) k
      · simp
      · simp only [Fin.val_succ, List.take_succ_cons, List.map_cons,
          List.sum_cons, kwPrefixPositions_cons, List.get_eq_getElem,
          List.getElem_cons_succ, List.getElem_map]
        have hq := ih q
        simp only [List.get_eq_getElem] at hq
        rw [hq]


def kwListDirection (word : List (Fin 4)) : Fin word.length → Fin 4 :=
  word.get

@[simp] theorem kwListDirection_ofFn (word : List (Fin 4)) :
    List.ofFn (kwListDirection word) = word := List.ofFn_get word

theorem kwListDirection_pos_eq_prefixPosition
    (word : List (Fin 4)) [NeZero word.length]
    (k : Fin word.length) :
    pos (kwListDirection word) k =
      (kwPrefixPositions word).get
        ⟨k.val, by simpa using k.isLt⟩ := by
  rw [kwPrefixPositions_get]
  unfold pos
  have hsum := List.sum_take_ofFn
    (f := fun i : Fin word.length ↦ stepOf (kwListDirection word i)) k.val
  have hofn : List.ofFn
      (fun i : Fin word.length ↦ stepOf (kwListDirection word i)) =
      word.map stepOf := by
    change List.ofFn (stepOf ∘ kwListDirection word) = word.map stepOf
    rw [← List.map_ofFn, kwListDirection_ofFn]
  rw [hofn] at hsum
  simpa only [Fin.mk_lt_mk, List.map_take] using hsum.symm

theorem kwListDirection_pos_injective_of_prefixPositions_nodup
    (word : List (Fin 4)) [NeZero word.length]
    (h : (kwPrefixPositions word).Nodup) :
    Function.Injective (pos (kwListDirection word)) := by
  intro i j hij
  have hget : (kwPrefixPositions word).get
      ⟨i.val, by simpa using i.isLt⟩ =
      (kwPrefixPositions word).get
      ⟨j.val, by simpa using j.isLt⟩ := by
    rw [← kwListDirection_pos_eq_prefixPosition,
      ← kwListDirection_pos_eq_prefixPosition]
    exact hij
  have hfin := h.injective_get hget
  apply Fin.ext
  exact congrArg
    (fun q : Fin (kwPrefixPositions word).length ↦ q.val) hfin

theorem kwPrefixPositions_replicate (d : Fin 4) (N : ℕ) :
    kwPrefixPositions (List.replicate N d) =
      (List.range N).map (fun k ↦ k • stepOf d) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [List.replicate_succ, kwPrefixPositions_cons, ih,
        List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      · simp
      · rw [List.map_map]
        apply List.map_congr_left
        intro k hk
        simp only [Function.comp_apply]
        rw [succ_nsmul]
        abel

theorem kwPrefixPositions_replicate_nodup (d : Fin 4) (N : ℕ) :
    (kwPrefixPositions (List.replicate N d)).Nodup := by
  rw [kwPrefixPositions_replicate]
  apply (List.nodup_range (n := N)).map
  intro a b hab
  fin_cases d <;> simp [stepOf, Prod.ext_iff] at hab <;> omega

theorem kwPrefixPositions_integralAxisWord_nodup
    {v : ℤ × ℤ} (haxis : v.1 = 0 ∨ v.2 = 0) :
    (kwPrefixPositions (kwIntegralAxisWord v)).Nodup := by
  rcases haxis with hx | hy
  · simp [kwIntegralAxisWord, hx,
      kwPrefixPositions_replicate_nodup]
  · simp [kwIntegralAxisWord, hy,
      kwPrefixPositions_replicate_nodup]

@[simp] theorem kwIntComplex_zero : kwIntComplex 0 = 0 := by
  simp [kwIntComplex]

theorem kwIntComplex_add (p q : ℤ × ℤ) :
    kwIntComplex (p + q) = kwIntComplex p + kwIntComplex q := by
  apply Complex.ext <;> simp [kwIntComplex]

theorem kwIntComplex_nsmul_stepOf (d : Fin 4) (k : ℕ) :
    kwIntComplex (k • stepOf d) =
      (k : ℝ) * kwRectilinearVector d := by
  fin_cases d <;>
    apply Complex.ext <;>
    simp [kwIntComplex, kwRectilinearVector, stepOf]

private theorem kw_replicate_prefix_mem_halfOpen
    (start : ℂ) (d : Fin 4) (N : ℕ) {q : ℤ × ℤ}
    (hq : q ∈ kwPrefixPositions (List.replicate N d)) :
    start + kwIntComplex q = start ∨
      Sbtw ℝ start (start + kwIntComplex q)
        (start + kwIntComplex (N • stepOf d)) := by
  rw [kwPrefixPositions_replicate, List.mem_map] at hq
  obtain ⟨k, hk, rfl⟩ := hq
  have hkN : k < N := List.mem_range.mp hk
  by_cases hk0 : k = 0
  · subst k
    simp
  · right
    have hN : 0 < N := Nat.pos_of_ne_zero (by omega)
    have hvec : (N : ℝ) * kwRectilinearVector d ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hN.ne') (kwRectilinearVector_ne_zero d)
    have hline : (k : ℝ) * kwRectilinearVector d =
        AffineMap.lineMap 0 ((N : ℝ) * kwRectilinearVector d)
          ((k : ℝ) / N) := by
      rw [AffineMap.lineMap_apply_module]
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      apply Complex.ext <;>
        simp only [Complex.add_re, Complex.add_im, Complex.real_smul,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.zero_re, Complex.zero_im,
          zero_mul, sub_zero] <;>
        field_simp [hNr] <;> ring
    have hs : Sbtw ℝ (0 : ℂ) ((k : ℝ) * kwRectilinearVector d)
        ((N : ℝ) * kwRectilinearVector d) := by
      rw [hline]
      apply sbtw_lineMap_iff.mpr
      refine ⟨hvec.symm, div_pos (by exact_mod_cast Nat.pos_of_ne_zero hk0) ?_, ?_⟩
      · exact_mod_cast hN
      · exact (div_lt_one (by exact_mod_cast hN)).mpr (by exact_mod_cast hkN)
    simpa only [kwIntComplex_nsmul_stepOf, zero_add, add_zero] using
      hs.const_add start

private theorem integralAxisWord_eq_replicate_of_axis
    {v : ℤ × ℤ} (haxis : v.1 = 0 ∨ v.2 = 0) :
    ∃ (d : Fin 4) (N : ℕ), kwIntegralAxisWord v = List.replicate N d ∧
      N • stepOf d = v := by
  rcases haxis with hx | hy
  · refine ⟨kwVerticalIntDirection v.2, v.2.natAbs, ?_, ?_⟩
    · simp [kwIntegralAxisWord, hx]
    · have hsum := sum_replicate_verticalDirection v.2
      calc
        v.2.natAbs • stepOf (kwVerticalIntDirection v.2) = (0, v.2) := by
          simpa only [List.sum_replicate] using hsum
        _ = v := Prod.ext hx.symm rfl
  · refine ⟨kwHorizontalIntDirection v.1, v.1.natAbs, ?_, ?_⟩
    · simp [kwIntegralAxisWord, hy]
    · have hsum := sum_replicate_horizontalDirection v.1
      calc
        v.1.natAbs • stepOf (kwHorizontalIntDirection v.1) = (v.1, 0) := by
          simpa only [List.sum_replicate] using hsum
        _ = v := Prod.ext rfl hy.symm


def kwIntegralPolygonEdgePoints
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) (i : Fin n) :
    List (ℤ × ℤ) :=
  (kwPrefixPositions (kwIntegralPolygonEdgeWord p i)).map (p i + ·)

@[simp] theorem kwIntegralPolygonEdgePoints_length
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) (i : Fin n) :
    (kwIntegralPolygonEdgePoints p i).length =
      (kwIntegralPolygonEdgeWord p i).length := by
  simp [kwIntegralPolygonEdgePoints]

theorem kwIntegralPolygonEdgePoints_nodup_of_axis
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) (i : Fin n)
    (haxis : (p (i + 1) - p i).1 = 0 ∨
      (p (i + 1) - p i).2 = 0) :
    (kwIntegralPolygonEdgePoints p i).Nodup := by
  unfold kwIntegralPolygonEdgePoints kwIntegralPolygonEdgeWord
  apply (kwPrefixPositions_integralAxisWord_nodup haxis).map
  intro a b hab
  exact add_left_cancel hab

theorem kwIntegralPolygonEdgePoints_complex_mem_halfOpen
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) (i : Fin n)
    (haxis : (p (i + 1) - p i).1 = 0 ∨
      (p (i + 1) - p i).2 = 0) {q : ℤ × ℤ}
    (hq : q ∈ kwIntegralPolygonEdgePoints p i) :
    kwIntComplex q ∈ kwRawHalfOpenEdge (fun j ↦ kwIntComplex (p j)) i := by
  rw [kwIntegralPolygonEdgePoints, List.mem_map] at hq
  obtain ⟨u, hu, rfl⟩ := hq
  obtain ⟨d, N, hword, hstep⟩ :=
    integralAxisWord_eq_replicate_of_axis haxis
  rw [kwIntegralPolygonEdgeWord, hword] at hu
  have hmem := kw_replicate_prefix_mem_halfOpen
    (kwIntComplex (p i)) d N hu
  have hend : p i + N • stepOf d = p (i + 1) := by
    rw [hstep]
    abel
  have hendC : kwIntComplex (p i) + kwIntComplex (N • stepOf d) =
      kwIntComplex (p (i + 1)) := by
    rw [← kwIntComplex_add, hend]
  rw [hendC] at hmem
  simpa only [kwRawHalfOpenEdge, kwIntComplex_add] using hmem



def kwIntegralPolygonPointList
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) : List (ℤ × ℤ) :=
  (List.ofFn (kwIntegralPolygonEdgePoints p)).flatten



def kwIndexedPrefixBlocks
    (start : ℕ → ℤ × ℤ) (blocks : List (List (Fin 4))) :
    List (ℤ × ℤ) :=
  (blocks.mapIdx fun k word ↦
    (kwPrefixPositions word).map (start k + ·)).flatten



theorem kwPrefixPositions_flatten_map
    (start : ℕ → ℤ × ℤ) (blocks : List (List (Fin 4)))
    (hstep : ∀ k (hk : k < blocks.length),
      (((blocks[k]'hk).map stepOf).sum) = start (k + 1) - start k) :
    (kwPrefixPositions blocks.flatten).map (start 0 + ·) =
      kwIndexedPrefixBlocks start blocks := by
  induction blocks generalizing start with
  | nil => simp [kwIndexedPrefixBlocks]
  | cons word tail ih =>
      have hzero : (word.map stepOf).sum = start 1 - start 0 := by
        simpa using hstep 0 (by simp)
      have htail : ∀ k (hk : k < tail.length),
          (((tail[k]'hk).map stepOf).sum) =
            start (k + 1 + 1) - start (k + 1) := by
        intro k hk
        simpa [Nat.add_assoc] using hstep (k + 1) (by simpa using hk)
      have hi := ih (fun k ↦ start (k + 1)) htail
      rw [List.flatten_cons, kwPrefixPositions_append, List.map_append]
      simp only [kwIndexedPrefixBlocks, List.mapIdx_cons,
        List.flatten_cons]
      congr 1
      rw [List.map_map]
      calc
        (kwPrefixPositions tail.flatten).map
              ((start 0 + ·) ∘ ((word.map stepOf).sum + ·)) =
            (kwPrefixPositions tail.flatten).map (start 1 + ·) := by
          apply List.map_congr_left
          intro q hq
          simp only [Function.comp_apply]
          rw [hzero]
          abel
        _ = (tail.mapIdx fun k word ↦
              (kwPrefixPositions word).map (start (k + 1) + ·)).flatten := by
          simpa [kwIndexedPrefixBlocks] using hi


def kwCyclicIntegralVertex
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) (k : ℕ) : ℤ × ℤ :=
  p ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩

@[simp] theorem kwCyclicIntegralVertex_fin
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) (i : Fin n) :
    kwCyclicIntegralVertex p i.val = p i := by
  unfold kwCyclicIntegralVertex
  congr
  exact Nat.mod_eq_of_lt i.isLt

@[simp] theorem kwCyclicIntegralVertex_succ
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) (i : Fin n) :
    kwCyclicIntegralVertex p (i.val + 1) = p (i + 1) := by
  unfold kwCyclicIntegralVertex
  congr 1
  apply Fin.ext
  rw [Fin.val_add, Fin.val_one']
  simpa [Nat.mod_eq_of_lt i.isLt] using Nat.add_mod i.val 1 n

theorem kwIndexedPrefixBlocks_integralPolygon
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) :
    kwIndexedPrefixBlocks (kwCyclicIntegralVertex p)
        (List.ofFn (kwIntegralPolygonEdgeWord p)) =
      kwIntegralPolygonPointList p := by
  unfold kwIndexedPrefixBlocks kwIntegralPolygonPointList
  rw [List.mapIdx_eq_ofFn]
  simp only [List.length_ofFn, List.get_ofFn]
  apply congrArg List.flatten
  rw [List.ofFn_inj]
  funext i
  simp [kwIntegralPolygonEdgePoints]



theorem kwIntegralPolygonPointList_eq_prefixPositions
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) :
    kwIntegralPolygonPointList p =
      (kwPrefixPositions (kwIntegralPolygonWord p)).map (p 0 + ·) := by
  symm
  rw [kwIntegralPolygonWord]
  have hstep : ∀ k
      (hk : k < (List.ofFn (kwIntegralPolygonEdgeWord p)).length),
      ((((List.ofFn (kwIntegralPolygonEdgeWord p))[k]'hk).map stepOf).sum) =
        kwCyclicIntegralVertex p (k + 1) -
          kwCyclicIntegralVertex p k := by
    intro k hk
    have hkn : k < n := by simpa using hk
    let i : Fin n := ⟨k, hkn⟩
    simp only [List.getElem_ofFn]
    change ((kwIntegralPolygonEdgeWord p i).map stepOf).sum = _
    rw [kwIntegralPolygonEdgeWord_step_sum]
    change p (i + 1) - p i = _
    rw [← kwCyclicIntegralVertex_succ p i,
      ← kwCyclicIntegralVertex_fin p i]
  have hzero : kwCyclicIntegralVertex p 0 = p 0 := by
    simpa using kwCyclicIntegralVertex_fin p (0 : Fin n)
  calc
    (kwPrefixPositions (List.ofFn
          (kwIntegralPolygonEdgeWord p)).flatten).map (p 0 + ·) =
        (kwPrefixPositions (List.ofFn
          (kwIntegralPolygonEdgeWord p)).flatten).map
            (kwCyclicIntegralVertex p 0 + ·) := by rw [hzero]
    _ = kwIndexedPrefixBlocks (kwCyclicIntegralVertex p)
          (List.ofFn (kwIntegralPolygonEdgeWord p)) :=
      kwPrefixPositions_flatten_map (kwCyclicIntegralVertex p)
        (List.ofFn (kwIntegralPolygonEdgeWord p)) hstep
    _ = kwIntegralPolygonPointList p :=
      kwIndexedPrefixBlocks_integralPolygon p




theorem kwIntegralPolygonPointList_nodup
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ)
    (haxis : ∀ i, (p (i + 1) - p i).1 = 0 ∨
      (p (i + 1) - p i).2 = 0)
    (hsimple : KWRawNonbacktrackingSimpleData
      (fun i ↦ kwIntComplex (p i))) :
    (kwIntegralPolygonPointList p).Nodup := by
  rw [kwIntegralPolygonPointList, List.nodup_flatten]
  constructor
  · intro points hpoints
    rw [List.mem_ofFn] at hpoints
    obtain ⟨i, rfl⟩ := hpoints
    exact kwIntegralPolygonEdgePoints_nodup_of_axis p i (haxis i)
  · rw [List.pairwise_ofFn]
    intro i j hij
    rw [List.disjoint_left]
    intro q hqi hqj
    have hi := kwIntegralPolygonEdgePoints_complex_mem_halfOpen
      p i (haxis i) hqi
    have hj := kwIntegralPolygonEdgePoints_complex_mem_halfOpen
      p j (haxis j) hqj
    exact Set.disjoint_left.mp
      (hsimple.halfOpenEdge_disjoint (Fin.ne_of_lt hij)) hi hj


theorem kwIntegralPolygonWord_vertexCount_le_length
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ)
    (hsimple : KWRawNonbacktrackingSimpleData
      (fun i ↦ kwIntComplex (p i))) :
    n ≤ (kwIntegralPolygonWord p).length := by
  have hedge (i : Fin n) :
      1 ≤ (kwIntegralPolygonEdgeWord p i).length := by
    apply Nat.one_le_iff_ne_zero.mpr
    apply Nat.ne_of_gt
    apply List.length_pos_of_ne_nil
    apply kwIntegralAxisWord_ne_nil
    rw [sub_ne_zero]
    intro hpi
    apply hsimple.edge_ne_zero i
    unfold kwRawEdge
    simpa [hpi]
  rw [kwIntegralPolygonWord, List.length_flatten, List.map_ofFn,
    List.sum_ofFn]
  calc
    n = ∑ _ : Fin n, 1 := by simp
    _ ≤ ∑ i : Fin n, (kwIntegralPolygonEdgeWord p i).length := by
      exact Finset.sum_le_sum fun i _ ↦ hedge i



theorem kwIntegralPolygonDirection_pos_injective
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ)
    [NeZero (kwIntegralPolygonWord p).length]
    (haxis : ∀ i, (p (i + 1) - p i).1 = 0 ∨
      (p (i + 1) - p i).2 = 0)
    (hsimple : KWRawNonbacktrackingSimpleData
      (fun i ↦ kwIntComplex (p i))) :
    Function.Injective (pos (kwIntegralPolygonDirection p)) := by
  have hpoints := kwIntegralPolygonPointList_nodup p haxis hsimple
  rw [kwIntegralPolygonPointList_eq_prefixPositions] at hpoints
  have hprefix :
      (kwPrefixPositions (kwIntegralPolygonWord p)).Nodup :=
    hpoints.of_map (p 0 + ·)
  change Function.Injective
    (pos (kwListDirection (kwIntegralPolygonWord p)))
  exact kwListDirection_pos_injective_of_prefixPositions_nodup _ hprefix



theorem kwIntegralPolygonDirection_phaseProduct_eq_neg_one
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ)
    [NeZero (kwIntegralPolygonWord p).length]
    (haxis : ∀ i, (p (i + 1) - p i).1 = 0 ∨
      (p (i + 1) - p i).2 = 0)
    (hsimple : KWRawNonbacktrackingSimpleData
      (fun i ↦ kwIntComplex (p i))) :
    (∏ k : Fin (kwIntegralPolygonWord p).length,
      kwVectorTurnPhase
        (kwRectilinearVector (kwIntegralPolygonDirection p k))
        (kwRectilinearVector
          (kwIntegralPolygonDirection p (k + 1)))) = -1 := by
  have hclosed := kwIntegralPolygonDirection_closed p
  have hinj := kwIntegralPolygonDirection_pos_injective p haxis hsimple
  have hlen : 3 ≤ (kwIntegralPolygonWord p).length :=
    hsimple.three_le.trans
      (kwIntegralPolygonWord_vertexCount_le_length p hsimple)
  have hnu := StatMech.Onsager.ons_nonUturn_of_pos_injective
    (kwIntegralPolygonDirection p) hclosed hinj hlen
  exact kwRectilinearVector_phaseProduct_eq_neg_one
    (kwIntegralPolygonDirection p) hclosed hinj hlen hnu



def kwExpandedRectilinearBlocks (blocks : List (Fin 4 × ℕ)) : List ℂ :=
  blocks.flatMap fun block ↦
    List.replicate block.2 (kwRectilinearVector block.1)


def kwCompressedRectilinearBlocks (blocks : List (Fin 4 × ℕ)) : List ℂ :=
  blocks.map fun block ↦ kwRectilinearVector block.1

@[simp] theorem kwVectorTurnPhase_self (z : ℂ) :
    kwVectorTurnPhase z z = 1 := by
  simp [kwVectorTurnPhase, kwAngleTurnPhase]

theorem kwVectorPhasePath_replicate (z : ℂ) (N : ℕ) :
    kwVectorPhasePath (List.replicate N z) = 1 := by
  induction N with
  | zero => rfl
  | succ N ih =>
      cases N with
      | zero => rfl
      | succ N =>
          rw [List.replicate_succ, List.replicate_succ,
            kwVectorPhasePath_cons_cons, kwVectorTurnPhase_self]
          simpa using ih

private theorem getLastD_eq_getLast_of_ne_nil
    {A : Type*} (l : List A) (default : A) (h : l ≠ []) :
    l.getLastD default = l.getLast h := by
  cases l with
  | nil => exact (h rfl).elim
  | cons x tail => rfl



theorem kwVectorPhasePath_expandedRectilinearBlocks
    (blocks : List (Fin 4 × ℕ))
    (hpos : ∀ block ∈ blocks, 0 < block.2) :
    kwVectorPhasePath (kwExpandedRectilinearBlocks blocks) =
      kwVectorPhasePath (kwCompressedRectilinearBlocks blocks) := by
  induction blocks with
  | nil => rfl
  | cons block tail ih =>
      cases tail with
      | nil =>
          simp [kwExpandedRectilinearBlocks,
            kwCompressedRectilinearBlocks,
            kwVectorPhasePath_replicate]
      | cons next rest =>
          rcases block with ⟨d, N⟩
          rcases next with ⟨e, K⟩
          have hb : 0 < N := hpos (d, N) (by simp)
          have hn : 0 < K := hpos (e, K) (by simp)
          obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
          obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
          have htail : ∀ x ∈ (e, c + 1) :: rest, 0 < x.2 := by
            intro x hx
            exact hpos x (by simp [hx])
          have hi := ih htail
          change kwVectorPhasePath
              ((kwRectilinearVector d ::
                List.replicate b (kwRectilinearVector d)) ++
                kwRectilinearVector e ::
                  (List.replicate c (kwRectilinearVector e) ++
                    kwExpandedRectilinearBlocks rest)) = _
          rw [kwVectorPhasePath_append_cons]
          have hbpath : kwVectorPhasePath
              (kwRectilinearVector d ::
                List.replicate b (kwRectilinearVector d)) = 1 := by
            rw [← List.replicate_succ]
            exact kwVectorPhasePath_replicate _ _
          have hblast :
              (kwRectilinearVector d ::
                List.replicate b (kwRectilinearVector d)).getLastD
                  (kwRectilinearVector d) = kwRectilinearVector d := by
            rw [← List.replicate_succ]
            rw [getLastD_eq_getLast_of_ne_nil _ _
                List.replicate_succ_ne_nil,
              List.getLast_replicate_succ]
          have hi' := hi
          change kwVectorPhasePath
              (kwRectilinearVector e ::
                (List.replicate c (kwRectilinearVector e) ++
                  kwExpandedRectilinearBlocks rest)) =
            kwVectorPhasePath
              (kwRectilinearVector e ::
                kwCompressedRectilinearBlocks rest) at hi'
          rw [hbpath, hblast, hi']
          simp only [one_mul]
          change kwVectorTurnPhase (kwRectilinearVector d)
              (kwRectilinearVector e) *
                kwVectorPhasePath
                  (kwRectilinearVector e ::
                    kwCompressedRectilinearBlocks rest) =
            kwVectorPhasePath
              (kwRectilinearVector d :: kwRectilinearVector e ::
                kwCompressedRectilinearBlocks rest)
          rfl

private theorem getLastD_append_of_right_ne_nil
    {A : Type*} (left right : List A) (default : A) (h : right ≠ []) :
    (left ++ right).getLastD default = right.getLastD default := by
  rw [getLastD_eq_getLast_of_ne_nil _ _
      (List.append_ne_nil_of_right_ne_nil left h),
    getLastD_eq_getLast_of_ne_nil _ _ h,
    List.getLast_append_of_right_ne_nil]

theorem kwExpandedRectilinearBlocks_getLastD
    (blocks : List (Fin 4 × ℕ))
    (hpos : ∀ block ∈ blocks, 0 < block.2) (default : ℂ) :
    (kwExpandedRectilinearBlocks blocks).getLastD default =
      (kwCompressedRectilinearBlocks blocks).getLastD default := by
  induction blocks with
  | nil => rfl
  | cons block tail ih =>
      rcases block with ⟨d, N⟩
      have hN : 0 < N := hpos (d, N) (by simp)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
      cases tail with
      | nil =>
          simp only [kwExpandedRectilinearBlocks,
            kwCompressedRectilinearBlocks, List.flatMap_cons,
            List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil]
          change (List.replicate (k + 1)
              (kwRectilinearVector d)).getLastD default =
            [kwRectilinearVector d].getLastD default
          rw [getLastD_eq_getLast_of_ne_nil _ _
              List.replicate_succ_ne_nil,
            List.getLast_replicate_succ]
          rfl
      | cons next rest =>
          have htail : ∀ x ∈ next :: rest, 0 < x.2 := by
            intro x hx
            exact hpos x (by simp [hx])
          have hexpNe :
              kwExpandedRectilinearBlocks (next :: rest) ≠ [] := by
            have hn : 0 < next.2 := htail next (by simp)
            intro hempty
            have hlen := congrArg List.length hempty
            simp [kwExpandedRectilinearBlocks] at hlen
            omega
          change (List.replicate (k + 1) (kwRectilinearVector d) ++
                kwExpandedRectilinearBlocks (next :: rest)).getLastD default =
              (kwRectilinearVector d ::
                kwCompressedRectilinearBlocks (next :: rest)).getLastD default
          rw [getLastD_append_of_right_ne_nil _ _ _ hexpNe]
          rw [ih htail]
          have hcompNe :
              kwCompressedRectilinearBlocks (next :: rest) ≠ [] := by
            simp [kwCompressedRectilinearBlocks]
          rw [getLastD_eq_getLast_of_ne_nil _ _ hcompNe,
            getLastD_eq_getLast_of_ne_nil _ _ (by simp),
            List.getLast_cons hcompNe]



theorem kwVectorPhaseCycle_expandedRectilinearBlocks
    (blocks : List (Fin 4 × ℕ))
    (hpos : ∀ block ∈ blocks, 0 < block.2) :
    kwVectorPhaseCycle (kwExpandedRectilinearBlocks blocks) =
      kwVectorPhaseCycle (kwCompressedRectilinearBlocks blocks) := by
  cases blocks with
  | nil => rfl
  | cons block tail =>
      rcases block with ⟨d, N⟩
      have hN : 0 < N := hpos (d, N) (by simp)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
      have hpath := kwVectorPhasePath_expandedRectilinearBlocks
        ((d, k + 1) :: tail) hpos
      have hlast := kwExpandedRectilinearBlocks_getLastD
        ((d, k + 1) :: tail) hpos (kwRectilinearVector d)
      change kwVectorPhaseCycle
          (kwRectilinearVector d ::
            (List.replicate k (kwRectilinearVector d) ++
              kwExpandedRectilinearBlocks tail)) =
        kwVectorPhaseCycle
          (kwRectilinearVector d ::
            kwCompressedRectilinearBlocks tail)
      rw [kwVectorPhaseCycle_cons, kwVectorPhaseCycle_cons]
      change kwVectorPhasePath
          (kwExpandedRectilinearBlocks ((d, k + 1) :: tail)) * _ =
        kwVectorPhasePath
          (kwCompressedRectilinearBlocks ((d, k + 1) :: tail)) * _
      rw [hpath]
      change kwVectorPhasePath
          (kwCompressedRectilinearBlocks ((d, k + 1) :: tail)) *
            kwVectorTurnPhase
              ((kwExpandedRectilinearBlocks
                ((d, k + 1) :: tail)).getLastD (kwRectilinearVector d))
              (kwRectilinearVector d) = _
      rw [hlast]
      change kwVectorPhasePath
          (kwCompressedRectilinearBlocks ((d, k + 1) :: tail)) *
            kwVectorTurnPhase
              ((kwRectilinearVector d ::
                kwCompressedRectilinearBlocks tail).getLastD
                  (kwRectilinearVector d))
              (kwRectilinearVector d) = _
      rfl



theorem kwIntegralAxisPolygon_phaseCycle_eq_neg_one
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ)
    (haxis : ∀ i, (p (i + 1) - p i).1 = 0 ∨
      (p (i + 1) - p i).2 = 0)
    (hsimple : KWRawNonbacktrackingSimpleData
      (fun i ↦ kwIntComplex (p i))) :
    kwVectorPhaseCycle
      (List.ofFn fun i : Fin n ↦ kwIntComplex (p (i + 1) - p i)) = -1 := by
  choose d N hword hstep using fun i : Fin n ↦
    integralAxisWord_eq_replicate_of_axis (haxis i)
  have hdisp (i : Fin n) : p (i + 1) - p i ≠ 0 := by
    rw [sub_ne_zero]
    intro hp
    apply hsimple.edge_ne_zero i
    unfold kwRawEdge
    simpa [hp]
  have hN (i : Fin n) : 0 < N i := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply hdisp i
    rw [← hstep i, hzero]
    simp
  let blocks : List (Fin 4 × ℕ) :=
    List.ofFn fun i : Fin n ↦ (d i, N i)
  have hblocksPos : ∀ block ∈ blocks, 0 < block.2 := by
    intro block hblock
    simp only [blocks, List.mem_ofFn] at hblock
    obtain ⟨i, rfl⟩ := hblock
    exact hN i
  have hexpanded : kwExpandedRectilinearBlocks blocks =
      (kwIntegralPolygonWord p).map kwRectilinearVector := by
    unfold kwExpandedRectilinearBlocks kwIntegralPolygonWord
    simp only [blocks, List.flatMap, List.map_ofFn,
      List.map_flatten]
    congr 2
    funext i
    simp only [Function.comp_apply, kwIntegralPolygonEdgeWord]
    rw [hword i, List.map_replicate]
  have hcompressed : kwCompressedRectilinearBlocks blocks =
      List.ofFn (fun i : Fin n ↦ kwRectilinearVector (d i)) := by
    simp [kwCompressedRectilinearBlocks, blocks, Function.comp_def]
  have hedgeScale (i : Fin n) :
      kwIntComplex (p (i + 1) - p i) =
        (N i : ℝ) * kwRectilinearVector (d i) := by
    rw [← hstep i, kwIntComplex_nsmul_stepOf]
  have horiginalCompressed :
      kwVectorPhaseCycle
          (List.ofFn fun i : Fin n ↦ kwIntComplex (p (i + 1) - p i)) =
        kwVectorPhaseCycle
          (List.ofFn fun i : Fin n ↦ kwRectilinearVector (d i)) := by
    rw [kwVectorPhaseCycle_ofFn, kwVectorPhaseCycle_ofFn]
    unfold kwLoopPhaseProduct
    apply Finset.prod_congr rfl
    intro i hi
    change kwVectorTurnPhase
        (kwIntComplex (p (i + 1) - p i))
        (kwIntComplex (p (i + 1 + 1) - p (i + 1))) = _
    rw [hedgeScale i, hedgeScale (i + 1)]
    exact kwVectorTurnPhase_pos_scales
      (N i) (N (i + 1)) (by exact_mod_cast hN i)
      (by exact_mod_cast hN (i + 1))
      (kwRectilinearVector (d i)) (kwRectilinearVector (d (i + 1)))
      (kwRectilinearVector_ne_zero _) (kwRectilinearVector_ne_zero _)
  have hlen : 3 ≤ (kwIntegralPolygonWord p).length :=
    hsimple.three_le.trans
      (kwIntegralPolygonWord_vertexCount_le_length p hsimple)
  letI : NeZero (kwIntegralPolygonWord p).length := ⟨by omega⟩
  have hunit := kwIntegralPolygonDirection_phaseProduct_eq_neg_one
    p haxis hsimple
  have hunitCycle : kwVectorPhaseCycle
      ((kwIntegralPolygonWord p).map kwRectilinearVector) = -1 := by
    have hlist : (kwIntegralPolygonWord p).map kwRectilinearVector =
        List.ofFn (fun k : Fin (kwIntegralPolygonWord p).length ↦
          kwRectilinearVector (kwIntegralPolygonDirection p k)) := by
      change (kwIntegralPolygonWord p).map kwRectilinearVector =
        List.ofFn (kwRectilinearVector ∘ kwIntegralPolygonDirection p)
      calc
        (kwIntegralPolygonWord p).map kwRectilinearVector =
            (List.ofFn (kwIntegralPolygonDirection p)).map
              kwRectilinearVector := by
          congr 1
          exact (List.ofFn_get (kwIntegralPolygonWord p)).symm
        _ = List.ofFn
            (kwRectilinearVector ∘ kwIntegralPolygonDirection p) :=
          List.map_ofFn
    rw [hlist, kwVectorPhaseCycle_ofFn]
    simpa only [kwLoopPhaseProduct] using hunit
  calc
    kwVectorPhaseCycle
        (List.ofFn fun i : Fin n ↦ kwIntComplex (p (i + 1) - p i)) =
        kwVectorPhaseCycle
          (List.ofFn fun i : Fin n ↦ kwRectilinearVector (d i)) :=
      horiginalCompressed
    _ = kwVectorPhaseCycle (kwCompressedRectilinearBlocks blocks) := by
      rw [hcompressed]
    _ = kwVectorPhaseCycle (kwExpandedRectilinearBlocks blocks) :=
      (kwVectorPhaseCycle_expandedRectilinearBlocks blocks hblocksPos).symm
    _ = kwVectorPhaseCycle
        ((kwIntegralPolygonWord p).map kwRectilinearVector) := by rw [hexpanded]
    _ = -1 := hunitCycle

end StatMech.FrontierA
