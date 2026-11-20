/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.FKGeneralQConnectionFKG
import Code.FK.FiniteVolumeShift
import Code.FK.FreeTailTriviality
import Code.FK.PottsInfiniteVolumeTwoPoint

open Filter Finset MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK

open StatMech.Lattice

noncomputable section



theorem connProb_equiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (sigma : V ≃ V)
    (hsigma : ∀ x y, G.Adj (sigma x) (sigma y) ↔ G.Adj x y)
    (p q : Real) (x y : V) :
    connProb G p q (sigma x) (sigma y) = connProb G p q x y := by
  classical
  unfold connProb
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← Equiv.sum_comp (reCfgIsoEquiv sigma.symm)
    (fun omega : ConfigSpace (Sym2 V) =>
      if Connected G omega (sigma x) (sigma y) then
        fkProb G p q omega
      else 0)]
  apply Finset.sum_congr rfl
  intro omega _
  have hsigmaSymm : ∀ a b,
      G.Adj (sigma.symm a) (sigma.symm b) ↔ G.Adj a b := by
    intro a b
    rw [← hsigma (sigma.symm a) (sigma.symm b)]
    simp
  have hsigmaInv : ∀ a b,
      G.Adj a b ↔ G.Adj (sigma.symm a) (sigma.symm b) :=
    fun a b => (hsigmaSymm a b).symm
  have hconn :
      Connected G (reCfgIso sigma.symm omega) (sigma x) (sigma y) ↔
        Connected G omega x y := by
    have hiff : Connected G omega x y ↔
        Connected G (reCfgIso sigma.symm omega) (sigma x) (sigma y) := by
      have h :=
        (fvs_openSubIso G G sigma.symm hsigmaInv omega).reachable_iff
          (u := sigma x) (v := sigma y)
      change Connected G omega (sigma.symm (sigma x))
          (sigma.symm (sigma y)) ↔
        Connected G (reCfgIso sigma.symm omega) (sigma x) (sigma y) at h
      simpa using h
    exact hiff.symm
  change (if Connected G (reCfgIso sigma.symm omega) (sigma x) (sigma y) then
      fkProb G p q (reCfgIso sigma.symm omega) else 0) = _
  rw [if_congr hconn rfl rfl]
  split
  · exact fvs_fkProb_reCfgIso G G sigma.symm hsigmaInv p q omega
  · rfl



theorem connProb_boxSym
    {d : Nat} (S : BoxSym d) (n : Nat)
    (p q : Real) (x y : boxVerts d n) :
    connProb (boxGraph d n) p q (S.lift n x) (S.lift n y) =
      connProb (boxGraph d n) p q x y :=
  connProb_equiv (boxGraph d n) (S.lift n) (S.lift_adj n) p q x y



theorem fkgq_freeInfiniteVolume_connection_boxSym
    {d : Nat} (hd : 1 ≤ d) (S : BoxSym d)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (x y : Site d) :
    (freeInfiniteVolume d hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real
        {omega | StatMech.Lattice.Connected d omega (S.τ x) (S.τ y)} =
      (freeInfiniteVolume d hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real
        {omega | StatMech.Lattice.Connected d omega x y} := by
  let mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
    freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)
  obtain ⟨phi, hphi, hweak⟩ :=
    freeInfiniteVolume_isLimit d hp hp1 (zero_lt_one.trans_le hq)
  have hunique : (mu : Measure _) (StatMech.Percolation.atLeastTwoInfinite d) = 0 := by
    exact (freeInfinite_canonical_uniqueness_all_parameters
      hd hp hp1 hq).2.1
  have hleft : Tendsto
      (fun n => (freeFiniteMeasure d (phi n) hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          {omega | StatMech.Lattice.Connected d omega (S.τ x) (S.τ y)})
      atTop (nhds ((mu : Measure _).real
        {omega | StatMech.Lattice.Connected d omega (S.τ x) (S.τ y)})) := by
    apply StatMech.FrontierB.WeakConvergesTo.tendsto_real_of_null_frontier
      hweak
    exact measure_frontier_connectedEvent_eq_zero mu hunique (S.τ x) (S.τ y)
  have hright : Tendsto
      (fun n => (freeFiniteMeasure d (phi n) hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          {omega | StatMech.Lattice.Connected d omega x y})
      atTop (nhds ((mu : Measure _).real
        {omega | StatMech.Lattice.Connected d omega x y})) := by
    apply StatMech.FrontierB.WeakConvergesTo.tendsto_real_of_null_frontier
      hweak
    exact measure_frontier_connectedEvent_eq_zero mu hunique x y
  obtain ⟨N, hN⟩ := StatMech.Percolation.finite_subset_box
    ({x, y, S.τ x, S.τ y} : Set (Site d)) (Set.toFinite _)
  have hphiTop : Tendsto phi atTop atTop := hphi.tendsto_atTop
  have heq : ∀ᶠ n in atTop,
      (freeFiniteMeasure d (phi n) hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          {omega | StatMech.Lattice.Connected d omega (S.τ x) (S.τ y)} =
      (freeFiniteMeasure d (phi n) hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          {omega | StatMech.Lattice.Connected d omega x y} := by
    filter_upwards [hphiTop.eventually (eventually_ge_atTop N)] with n hn
    have hx : x ∈ box d (phi n) := box_mono d hn (hN (by simp))
    have hy : y ∈ box d (phi n) := box_mono d hn (hN (by simp))
    have hsx : S.τ x ∈ box d (phi n) := (S.box_mem (phi n) x).2 hx
    have hsy : S.τ y ∈ box d (phi n) := (S.box_mem (phi n) y).2 hy
    rw [freeFiniteMeasure_real_connectedEvent d (phi n) hp hp1
      (zero_lt_one.trans_le hq) (S.τ x) (S.τ y) hsx hsy,
      freeFiniteMeasure_real_connectedEvent d (phi n) hp hp1
        (zero_lt_one.trans_le hq) x y hx hy]
    simpa using connProb_boxSym S (phi n) p q
      (⟨x, hx⟩ : boxVerts d (phi n)) ⟨y, hy⟩
  have hleft' := Filter.Tendsto.congr' heq hleft
  exact tendsto_nhds_unique hleft' hright

end

end StatMech.FK
