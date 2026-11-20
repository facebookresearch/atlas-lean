/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.ContourLinksExits
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.OrbitLoopBridge
import Code.Lattice.OrbitExteriorEven
import Code.Lattice.OrbitWindingWitness
import Code.Lattice.WindingWitness
import Code.Lattice.NoDiagTouchClose

open Set SimpleGraph Function

namespace StatMech

namespace Lattice


















theorem ral_oddRay_iff_oddCross_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z₀ q : Site 2} (hq : ∀ p ∈ Vc.support, q 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk z₀ q) :
    (¬ Even (jec_rayCount z₀ Vc)) ↔ (¬ Even (crossCount (jec_leftRegion Vc) γ)) := by
  
  have hqout : ¬ ¬ Even (jec_rayCount q Vc) :=
    not_not.mpr (by rw [jec_rayCount_eq_zero_of_right q Vc hq]; exact Nat.even_iff.mpr rfl)
  
  have hpar := crossCount_parity (jec_leftRegion Vc) γ
  simp only [jec_mem_leftRegion] at hpar
  
  constructor
  · intro hodd heven
    exact hqout ((hpar.mp heven).mp hodd)
  · intro hcrossOdd hray
    apply hcrossOdd
    rw [hpar]
    exact ⟨fun h => absurd h (not_not.mpr hray), fun h => absurd h hqout⟩





















theorem ral_inRegion_rayCount_odd {K : Set (Site 2)} {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (hmatch : pww_BdEdgeMatch K Vc)
    {z₀ q : Site 2} (hz₀K : z₀ ∈ K) (hqK : q ∉ K)
    (hqfar : ∀ p ∈ Vc.support, q 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk z₀ q) :
    ¬ Even (jec_rayCount z₀ Vc) := by
  
  have hoddK : ¬ Even (crossCount K γ) :=
    crossCount_odd_of_separated K hz₀K hqK γ
  
  have heq : crossCount (jec_leftRegion Vc) γ = crossCount K γ :=
    pww_crossCount_eq_of_bdEdge_match (jec_leftRegion Vc) K (fun e => (hmatch e).symm) γ
  have hoddL : ¬ Even (crossCount (jec_leftRegion Vc) γ) := by rw [heq]; exact hoddK
  
  exact (ral_oddRay_iff_oddCross_leftRegion Vc hqfar γ).mpr hoddL
























theorem ral_tailOdd_of_bdEdgeMatch (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK a.1 a.2))
    {q : Site 2} (hqK : q ∉ K)
    (hqfar : ∀ p ∈ (olb_orbitLoop K hK a.1 a.2).support, q 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk a.1.tail q) :
    wwit_TailOdd K hK a := by
  refine ⟨0, ?_⟩
  
  simp only [Function.iterate_zero, id_eq]
  exact ral_inRegion_rayCount_odd (olb_orbitLoop K hK a.1 a.2) hmatch a.2.tail_mem hqK hqfar γ



















theorem ral_starHull_tailOdd_of_bdEdgeMatch (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hmatch : pww_BdEdgeMatch (ndt_StarHull K) (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2))
    {q : Site 2} (hqK : q ∉ ndt_StarHull K)
    (hqfar : ∀ p ∈ (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2).support, q 0 ≤ p 0)
    (γ : (hypercubicLattice 2).Walk a.1.tail q) :
    wwit_TailOdd (ndt_StarHull K) hSK a :=
  ral_tailOdd_of_bdEdgeMatch (ndt_StarHull K) hSK a hmatch hqK hqfar γ















theorem ral_unitSquare_inside_odd :
    ¬ Even (jec_rayCount (![1, 1] : Site 2) wwit_unitSquareLoop) :=
  wwit_unitSquareLoop_inside_odd




















































end Lattice

end StatMech
