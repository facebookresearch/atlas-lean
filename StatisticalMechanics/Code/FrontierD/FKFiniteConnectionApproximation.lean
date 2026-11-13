/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKQgt4DiagonalRate
import Code.FrontierD.FKRectTorusRandomCluster
import Code.FK.FKGeneralQConsumer
import Code.FK.FKGeneralQConnectionFKG



open Filter MeasureTheory Set Topology

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.TwoDim

noncomputable section





theorem exists_freeBox_twoPoint_gt_infinite_sub
    {d : Nat} {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (x y : Site d) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ (m : Nat) (hx : x ∈ box d m) (hy : y ∈ box d m),
      (FK.freeInfiniteVolume d hp hp1
          (zero_lt_one.trans_le hq) :
            Measure (ConfigSpace (Sym2 (Site d)))).real
            {omega | StatMech.Lattice.Connected d omega x y} - epsilon <
        FK.twoPointFun (FK.boxGraph d m) p q
          (⟨x, hx⟩ : FK.boxVerts d m) ⟨y, hy⟩ := by
  let mu : Measure (ConfigSpace (Sym2 (Site d))) :=
    FK.freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)
  have hwithin : Tendsto (fun n =>
      mu.real (zbd_connectedWithinBox x y n)) atTop
      (nhds (mu.real {omega | StatMech.Lattice.Connected d omega x y})) := by
    have hmeasure := tendsto_measure_iUnion_atTop (μ := mu)
      (zbd_connectedWithinBox_mono x y)
    have hreal := (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure
    simpa only [zbd_iUnion_connectedWithinBox] using hreal
  obtain ⟨N0, hN0⟩ := StatMech.Percolation.finite_subset_box
    ({x, y} : Set (Site d)) ((Set.finite_singleton y).insert x)
  have hx0 : x ∈ box d N0 := hN0 (Set.mem_insert x {y})
  have hy0 : y ∈ box d N0 :=
    hN0 (Set.mem_insert_iff.mpr (Or.inr rfl))
  have hinnerEventually : ∀ᶠ N in atTop,
      mu.real {omega | StatMech.Lattice.Connected d omega x y} -
          epsilon / 2 < mu.real (zbd_connectedWithinBox x y N) :=
    (tendsto_order.1 hwithin).1 _ (by linarith)
  obtain ⟨N, hinner, hN0N⟩ :=
    (hinnerEventually.and (eventually_ge_atTop N0)).exists
  have hxN : x ∈ box d N := box_mono d hN0N hx0
  have hyN : y ∈ box d N := box_mono d hN0N hy0
  let xbN : FK.boxVerts d N := ⟨x, hxN⟩
  let ybN : FK.boxVerts d N := ⟨y, hyN⟩
  have houterLimit : Tendsto (fun m =>
      (FK.freeFiniteMeasure d m hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          (FK.boxConnEvent d N xbN ybN)) atTop
      (nhds (mu.real (FK.boxConnEvent d N xbN ybN))) := by
    simpa [mu] using FK.fkgq_free_infinite_measure N hp hp1 hq
      (FK.connEvent_isIncreasing (FK.boxGraph d N) xbN ybN)
  have houterEventually : ∀ᶠ m in atTop,
      mu.real (FK.boxConnEvent d N xbN ybN) - epsilon / 2 <
        (FK.freeFiniteMeasure d m hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
            (FK.boxConnEvent d N xbN ybN) :=
    (tendsto_order.1 houterLimit).1 _ (by linarith)
  obtain ⟨m, houter, hNm⟩ :=
    (houterEventually.and (eventually_ge_atTop N)).exists
  have hxM : x ∈ box d m := box_mono d hNm hxN
  have hyM : y ∈ box d m := box_mono d hNm hyN
  let xbM : FK.boxVerts d m := ⟨x, hxM⟩
  let ybM : FK.boxVerts d m := ⟨y, hyM⟩
  have hinnerEvent :
      FK.boxConnEvent d N xbN ybN ⊆ FK.boxConnEvent d m xbM ybM := by
    rw [← FK.connectedWithinBox_eq_boxConnEvent hxN hyN,
      ← FK.connectedWithinBox_eq_boxConnEvent hxM hyM]
    exact zbd_connectedWithinBox_mono x y hNm
  have hfiniteMono := measureReal_mono (μ :=
      (FK.freeFiniteMeasure d m hp hp1
        (zero_lt_one.trans_le hq) : Measure _)) hinnerEvent
  refine ⟨m, hxM, hyM, ?_⟩
  calc
    mu.real {omega | StatMech.Lattice.Connected d omega x y} - epsilon <
        mu.real (FK.boxConnEvent d N xbN ybN) - epsilon / 2 := by
      rw [← FK.connectedWithinBox_eq_boxConnEvent hxN hyN]
      linarith
    _ < (FK.freeFiniteMeasure d m hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
            (FK.boxConnEvent d N xbN ybN) := houter
    _ <= (FK.freeFiniteMeasure d m hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
            (FK.boxConnEvent d m xbM ybM) := hfiniteMono
    _ = FK.twoPointFun (FK.boxGraph d m) p q xbM ybM :=
      FK.freeFiniteMeasure_real_boxConnEvent d m hp hp1
        (zero_lt_one.trans_le hq) xbM ybM


theorem exists_criticalFreeBox_exactDiagonalTwoPoint_gt_sub
    {q : Real} (hq : 4 < q) (scale : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ (m : Nat)
        (hx : origin 2 ∈ box 2 m)
        (hy : fkQgt4ExactDiagonalSite (scale + 1) ∈ box 2 m),
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1) - epsilon <
        FK.twoPointFun (FK.boxGraph 2 m) (fkRectCriticalP q) q
          (⟨origin 2, hx⟩ : FK.boxVerts 2 m)
          ⟨fkQgt4ExactDiagonalSite (scale + 1), hy⟩ := by
  simpa [fkQgt4CriticalFreeExactDiagonalTwoPoint, FK.infiniteTwoPointReal]
    using exists_freeBox_twoPoint_gt_infinite_sub
      (fkRectCriticalP_pos (by linarith : (0 : Real) < q))
      (fkRectCriticalP_lt_one (by linarith : (0 : Real) < q))
      (by linarith : (1 : Real) <= q)
      (origin 2) (fkQgt4ExactDiagonalSite (scale + 1)) hepsilon

end

end StatMech.FrontierD
