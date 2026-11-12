/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.CrossingParity
import Code.Lattice.JordanContour
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.JordanCycleSpace
import Code.Lattice.JordanLeftRegionInterior
import Code.Lattice.FloodFillConnected
import Code.Lattice.InsideConnected
import Code.Lattice.OutsideConnected
import Code.Lattice.InsideCoveringClose
import Code.Lattice.FaceComponentBijection
import Code.Lattice.MinimalPeriodLoop
import Code.Ising.PeierlsPlanarAssembly

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

variable {a : Site 2}















def jsl_InteriorConnected (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      s ∉ Vc.support → t ∉ Vc.support →
    ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support





theorem jsl_interiorConnected_of_covers (Vc : (hypercubicLattice 2).Walk a a)
    (hoff : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    {sIn : Site 2} (hcov : jec_leftRegion Vc ⊆ offSupportComponent Vc sIn) :
    jsl_InteriorConnected Vc :=
  fun s t hs ht _ _ => hInOff_of_covers Vc hoff hcov s t hs ht



















theorem jsl_outside_connected_of_reachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (hFlood : oc_OutsideReachesExterior Vc R) :
    ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
      ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support := by
  intro s t hs ht _ _
  exact oc_hOutOff_of_reachesExterior Vc R hsupp hFlood s t hs ht

























theorem jsl_offComplComponentCount_eq_two (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support)
    (hin : jsl_InteriorConnected Vc)
    (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
      ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 :=
  fcb_two_components_of_sides Vc hxin hxoff hyout hyoff hin hout











theorem jsl_offComplComponentCount_eq_two_of_floodFill (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support)
    (hin : jsl_InteriorConnected Vc) (hFlood : oc_OutsideReachesExterior Vc R) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 :=
  jsl_offComplComponentCount_eq_two Vc hxin hxoff hyout hyoff hin
    (jsl_outside_connected_of_reachesExterior Vc R hsupp hFlood)






















theorem jsl_offComplComponentCount_eq_faceCount (Vc : (hypercubicLattice 2).Walk a a)
    {V : Type*} {G : SimpleGraph V} {v : V} (c : G.Walk v v) (hc : c.IsCycle)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support)
    (hin : jsl_InteriorConnected Vc)
    (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
      ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = faceCount c.toSubgraph.coe := by
  rw [jsl_offComplComponentCount_eq_two Vc hxin hxoff hyout hyoff hin hout,
    jcs_cycle_faceCount_eq_two c hc]





theorem jsl_offComplComponentCount_eq_faceCount_of_floodFill (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {V : Type*} {G : SimpleGraph V} {v : V} (c : G.Walk v v) (hc : c.IsCycle)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support)
    (hin : jsl_InteriorConnected Vc) (hFlood : oc_OutsideReachesExterior Vc R) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = faceCount c.toSubgraph.coe := by
  rw [jsl_offComplComponentCount_eq_two_of_floodFill Vc R hsupp hxin hxoff hyout hyoff hin hFlood,
    jcs_cycle_faceCount_eq_two c hc]

















theorem jsl_fcb_eq_icc (Vc : (hypercubicLattice 2).Walk a a) :
    fcb_offComplGraph Vc = icc_offComplGraph Vc := rfl





theorem jsl_iccCount_of_floodFill (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support)
    (hin : jsl_InteriorConnected Vc) (hFlood : oc_OutsideReachesExterior Vc R) :
    Nat.card (icc_offComplGraph Vc).ConnectedComponent = 2 := by
  rw [← jsl_fcb_eq_icc Vc]
  exact jsl_offComplComponentCount_eq_two_of_floodFill Vc R hsupp hxin hxoff hyout hyoff hin hFlood










theorem jsl_interiorCovers_of_floodFill (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {sIn sOut : Site 2}
    (hInMem : sIn ∈ jec_leftRegion Vc) (hInOff : sIn ∉ Vc.support)
    (hOutMem : sOut ∉ jec_leftRegion Vc) (hOutOff : sOut ∉ Vc.support)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    (hin : jsl_InteriorConnected Vc) (hFlood : oc_OutsideReachesExterior Vc R) :
    jec_leftRegion Vc ⊆ offSupportComponent Vc sIn :=
  icc_covers_of_two_components Vc
    (jsl_iccCount_of_floodFill Vc R hsupp hInMem hInOff hOutMem hOutOff hin hFlood)
    hInMem hInOff hOutMem hOutOff hoffIn




















theorem jsl_two_components_of_floodFill (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    (hoffOut : ∀ s ∉ jec_leftRegion Vc, s ∉ Vc.support)
    (hin : jsl_InteriorConnected Vc) (hFlood : oc_OutsideReachesExterior Vc R) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
  refine jlri_two_components_of_offSupport_connected Vc hp hq ?_ ?_
  · 
    intro s t hs ht
    exact hin s t hs ht (hoffIn s hs) (hoffIn t ht)
  · 
    intro s t hs ht
    exact jsl_outside_connected_of_reachesExterior Vc R hsupp hFlood s t hs ht
      (hoffOut s hs) (hoffOut t ht)







theorem jsl_peierls_long_range_order_of_planarConnectivity
    (hConn : ∀ n : ℕ, Ising.PlanarConnectivity n) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      Ising.plusMeasure 2 n β 0 ≠ Ising.minusMeasure 2 n β 0 :=
  Ising.peierls_long_range_order_of_planarConnectivity hConn

















theorem jsl_components_distinct (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support) :
    (fcb_offComplGraph Vc).connectedComponentMk ⟨x, hxoff⟩ ≠
      (fcb_offComplGraph Vc).connectedComponentMk ⟨y, hyoff⟩ := by
  rw [Ne, ConnectedComponent.eq]
  intro hreach
  exact hyout ((fcb_offCompl_sameSide Vc hreach).mp hxin)








theorem jsl_count_ge_two (Vc : (hypercubicLattice 2).Walk a a)
    [Finite (fcb_offComplGraph Vc).ConnectedComponent]
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support) :
    2 ≤ Nat.card (fcb_offComplGraph Vc).ConnectedComponent := by
  classical
  have hne := jsl_components_distinct Vc hxin hxoff hyout hyoff
  have hfin : Fintype (fcb_offComplGraph Vc).ConnectedComponent := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card (α := (fcb_offComplGraph Vc).ConnectedComponent)]
  have : 1 < Fintype.card (fcb_offComplGraph Vc).ConnectedComponent :=
    Fintype.one_lt_card_iff.mpr ⟨_, _, hne⟩
  omega












theorem jsl_minimalLoop_offComplComponentCount_eq_two (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hsupp : oc_supportSet (mpl_orbitLoop K a) ⊆ box 2 R)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion (mpl_orbitLoop K a))
    (hxoff : x ∉ (mpl_orbitLoop K a).support)
    (hyout : y ∉ jec_leftRegion (mpl_orbitLoop K a)) (hyoff : y ∉ (mpl_orbitLoop K a).support)
    (hin : jsl_InteriorConnected (mpl_orbitLoop K a))
    (hFlood : oc_OutsideReachesExterior (mpl_orbitLoop K a) R) :
    Nat.card (fcb_offComplGraph (mpl_orbitLoop K a)).ConnectedComponent = 2 :=
  jsl_offComplComponentCount_eq_two_of_floodFill (mpl_orbitLoop K a) R hsupp hxin hxoff hyout hyoff
    hin hFlood





theorem jsl_minimalLoop_interiorCovers_of_floodFill (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hsupp : oc_supportSet (mpl_orbitLoop K a) ⊆ box 2 R)
    {sIn sOut : Site 2}
    (hInMem : sIn ∈ jec_leftRegion (mpl_orbitLoop K a)) (hInOff : sIn ∉ (mpl_orbitLoop K a).support)
    (hOutMem : sOut ∉ jec_leftRegion (mpl_orbitLoop K a))
    (hOutOff : sOut ∉ (mpl_orbitLoop K a).support)
    (hoffIn : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
    (hin : jsl_InteriorConnected (mpl_orbitLoop K a))
    (hFlood : oc_OutsideReachesExterior (mpl_orbitLoop K a) R) :
    jec_leftRegion (mpl_orbitLoop K a) ⊆ offSupportComponent (mpl_orbitLoop K a) sIn :=
  jsl_interiorCovers_of_floodFill (mpl_orbitLoop K a) R hsupp hInMem hInOff hOutMem hOutOff hoffIn
    hin hFlood







theorem jsl_minimalLoop_two_components_of_floodFill (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hsupp : oc_supportSet (mpl_orbitLoop K a) ⊆ box 2 R)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p (mpl_orbitLoop K a)))
    (hq : ∀ w ∈ (mpl_orbitLoop K a).support, w 0 ≤ q 0 - 1)
    (hoffIn : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
    (hoffOut : ∀ s ∉ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
    (hin : jsl_InteriorConnected (mpl_orbitLoop K a))
    (hFlood : oc_OutsideReachesExterior (mpl_orbitLoop K a) R) :
    Nat.card (latticeMinusBarrier (jec_leftRegion (mpl_orbitLoop K a))).ConnectedComponent = 2 :=
  jsl_two_components_of_floodFill (mpl_orbitLoop K a) R hsupp hp hq hoffIn hoffOut hin hFlood













theorem jsl_floodFill_nonvacuous (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {z : Site 2} (hz : z ∈ exterior 2 R) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e :=
  oc_exterior_reachesExterior Vc R hz






theorem jsl_exterior_hub_nonvacuous (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {x y : Site 2}
    (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) :
    (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y :=
  oc_exterior_reachable_offSupport Vc R hsupp hx hy




















theorem jsl_offComplComponentCount_eq_two_of_reachesTop (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support)
    (hin : jsl_InteriorConnected Vc) (hTop : oc_OutsideReachesTop Vc R) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 :=
  jsl_offComplComponentCount_eq_two_of_floodFill Vc R hsupp hxin hxoff hyout hyoff hin
    (oc_outsideReachesExterior_of_reachesTop Vc R hsupp hTop)






theorem jsl_two_components_of_reachesTop (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    (hoffOut : ∀ s ∉ jec_leftRegion Vc, s ∉ Vc.support)
    (hin : jsl_InteriorConnected Vc) (hTop : oc_OutsideReachesTop Vc R) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  jsl_two_components_of_floodFill Vc R hsupp hp hq hoffIn hoffOut hin
    (oc_outsideReachesExterior_of_reachesTop Vc R hsupp hTop)

end Lattice

end StatMech
