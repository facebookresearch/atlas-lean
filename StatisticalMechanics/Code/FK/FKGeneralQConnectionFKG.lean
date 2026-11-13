/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.FKGeneralQInfiniteFKG
import Code.TwoDim.ZhangBKData
import Code.FrontierB.BoxGraphPath

open MeasureTheory Set Filter Topology

namespace StatMech.FK

open StatMech.Lattice StatMech.TwoDim

noncomputable section



theorem fkg_iUnion_of_monotone
    {E : Type*} [Countable E]
    (mu : Measure (ConfigSpace E)) [IsProbabilityMeasure mu]
    (A B : Nat -> Set (ConfigSpace E))
    (hAmono : Monotone A) (hBmono : Monotone B)
    (hstage : forall n,
      mu.real (A n) * mu.real (B n) <= mu.real (A n ∩ B n)) :
    mu.real (⋃ n, A n) * mu.real (⋃ n, B n) <=
      mu.real ((⋃ n, A n) ∩ (⋃ n, B n)) := by
  have hAt : Tendsto (fun n => mu.real (A n)) atTop
      (nhds (mu.real (⋃ n, A n))) := by
    exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp
      (tendsto_measure_iUnion_atTop (μ := mu) hAmono)
  have hBt : Tendsto (fun n => mu.real (B n)) atTop
      (nhds (mu.real (⋃ n, B n))) := by
    exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp
      (tendsto_measure_iUnion_atTop (μ := mu) hBmono)
  have hImono : Monotone (fun n => A n ∩ B n) := fun n m hnm =>
    inter_subset_inter (hAmono hnm) (hBmono hnm)
  have hIt : Tendsto (fun n => mu.real (A n ∩ B n)) atTop
      (nhds (mu.real (⋃ n, A n ∩ B n))) := by
    exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp
      (tendsto_measure_iUnion_atTop (μ := mu) hImono)
  have hdiag : (⋃ n, A n ∩ B n) = (⋃ n, A n) ∩ (⋃ n, B n) := by
    apply Set.Subset.antisymm
    · exact iUnion_subset fun n => inter_subset_inter
        (subset_iUnion A n) (subset_iUnion B n)
    · rintro omega ⟨hA, hB⟩
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hA
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hB
      exact Set.mem_iUnion.mpr ⟨max n m,
        hAmono (Nat.le_max_left n m) hn,
        hBmono (Nat.le_max_right n m) hm⟩
  rw [← hdiag]
  exact le_of_tendsto_of_tendsto (hAt.mul hBt) hIt
    (Filter.Eventually.of_forall hstage)



theorem connectedWithinBox_eq_boxConnEvent
    {d : Nat} {x y : Site d} {n : Nat}
    (hx : x ∈ box d n) (hy : y ∈ box d n) :
    zbd_connectedWithinBox x y n =
      boxConnEvent d n (⟨x, hx⟩ : boxVerts d n) ⟨y, hy⟩ := by
  ext omega
  simp only [zbd_connectedWithinBox, boxConnEvent, Set.mem_setOf_eq,
    Set.mem_preimage, connEvent]
  constructor
  · rintro ⟨hx', hy', hconn⟩
    simpa [ConnectedWithin, openSubgraphInduce, openSubgraph,
      openSub, boxGraph, boxRestrict] using hconn
  · intro hconn
    refine ⟨hx, hy, ?_⟩
    simpa [ConnectedWithin, openSubgraphInduce, openSubgraph,
      openSub, boxGraph, boxRestrict] using hconn



theorem fkgq_freeInfiniteVolume_boxConnEvent_pos
    {d : Nat} {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (n : Nat) (x y : boxVerts d n) :
    0 < (freeInfiniteVolume d hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxConnEvent d n x y) := by
  let f : Nat -> Real := fun m =>
    (freeFiniteMeasure d m hp hp1
      (zero_lt_one.trans_le hq) : Measure _).real (boxConnEvent d n x y)
  have hlim : Tendsto f atTop
      (nhds ((freeInfiniteVolume d hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          (boxConnEvent d n x y))) := by
    exact fkgq_free_infinite_measure n hp hp1 hq
      (connEvent_isIncreasing (boxGraph d n) x y)
  have hmono : Monotone (fun k => f (n + k)) := by
    apply monotone_nat_of_le_succ
    intro k
    exact fkgq_free_succ n (n + k) (Nat.le_add_right n k)
      hp hp1 hq (connEvent_isIncreasing (boxGraph d n) x y)
  have hshift : Tendsto (fun k => f (n + k)) atTop
      (nhds ((freeInfiniteVolume d hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          (boxConnEvent d n x y))) := by
    simpa [Nat.add_comm] using hlim.comp (tendsto_add_atTop_nat n)
  have hlower : f n <=
      (freeInfiniteVolume d hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          (boxConnEvent d n x y) := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hshift
    exact Filter.Eventually.of_forall fun k => hmono (Nat.zero_le k)
  exact (freeFiniteMeasure_apply_boxConnEvent_pos d n hp hp1
    (zero_lt_one.trans_le hq)
    (StatMech.FrontierB.boxGraph_preconnected d n x y)).trans_le hlower



theorem fkgq_freeInfiniteVolume_connection_pos
    {d : Nat} {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (x y : Site d) :
    0 < (freeInfiniteVolume d hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real
        {omega | StatMech.Lattice.Connected d omega x y} := by
  obtain ⟨n, hn⟩ := StatMech.Percolation.finite_subset_box
    ({x, y} : Set (Site d)) ((Set.finite_singleton y).insert x)
  have hx : x ∈ box d n := hn (Set.mem_insert x {y})
  have hy : y ∈ box d n := hn (Set.mem_insert_iff.mpr (Or.inr rfl))
  have hpos := fkgq_freeInfiniteVolume_boxConnEvent_pos hp hp1 hq n
    (⟨x, hx⟩ : boxVerts d n) ⟨y, hy⟩
  rw [← connectedWithinBox_eq_boxConnEvent hx hy] at hpos
  exact hpos.trans_le (measureReal_mono
    (zbd_connectedWithinBox_subset_connected x y n))



theorem fkgq_freeInfiniteVolume_connectedWithinBox_fkg
    {d : Nat} {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (x y u v : Site d) (n : Nat) :
    let mu := (freeInfiniteVolume d hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d))))
    mu.real (zbd_connectedWithinBox x y n) *
        mu.real (zbd_connectedWithinBox u v n) <=
      mu.real (zbd_connectedWithinBox x y n ∩
        zbd_connectedWithinBox u v n) := by
  classical
  let mu := (freeInfiniteVolume d hp hp1
    (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d))))
  by_cases hx : x ∈ box d n
  · by_cases hy : y ∈ box d n
    · by_cases hu : u ∈ box d n
      · by_cases hv : v ∈ box d n
        · let xb : boxVerts d n := ⟨x, hx⟩
          let yb : boxVerts d n := ⟨y, hy⟩
          let ub : boxVerts d n := ⟨u, hu⟩
          let vb : boxVerts d n := ⟨v, hv⟩
          have hxy := connectedWithinBox_eq_boxConnEvent hx hy
          have huv := connectedWithinBox_eq_boxConnEvent hu hv
          rw [hxy, huv]
          exact fkgq_freeInfiniteVolume_fkg n hp hp1 hq
            (connEvent_isIncreasing (boxGraph d n) xb yb)
            (connEvent_isIncreasing (boxGraph d n) ub vb)
        · have hempty : zbd_connectedWithinBox u v n = ∅ := by
            ext omega
            simp [zbd_connectedWithinBox, hv]
          simp [hempty]
      · have hempty : zbd_connectedWithinBox u v n = ∅ := by
          ext omega
          simp [zbd_connectedWithinBox, hu]
        simp [hempty]
    · have hempty : zbd_connectedWithinBox x y n = ∅ := by
        ext omega
        simp [zbd_connectedWithinBox, hy]
      simp [hempty]
  · have hempty : zbd_connectedWithinBox x y n = ∅ := by
      ext omega
      simp [zbd_connectedWithinBox, hx]
    simp [hempty]



theorem fkgq_freeInfiniteVolume_connection_fkg
    {d : Nat} {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (x y u v : Site d) :
    let mu := (freeInfiniteVolume d hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d))))
    mu.real {omega | StatMech.Lattice.Connected d omega x y} *
        mu.real {omega | StatMech.Lattice.Connected d omega u v} <=
      mu.real ({omega | StatMech.Lattice.Connected d omega x y} ∩
        {omega | StatMech.Lattice.Connected d omega u v}) := by
  let mu := (freeInfiniteVolume d hp hp1
    (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d))))
  have h := fkg_iUnion_of_monotone mu
    (zbd_connectedWithinBox x y) (zbd_connectedWithinBox u v)
    (zbd_connectedWithinBox_mono x y) (zbd_connectedWithinBox_mono u v)
    (fkgq_freeInfiniteVolume_connectedWithinBox_fkg hp hp1 hq x y u v)
  simpa only [zbd_iUnion_connectedWithinBox] using h

end

end StatMech.FK
