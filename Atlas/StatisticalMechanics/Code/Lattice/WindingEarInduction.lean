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
import Code.Lattice.DartOrbit
import Code.Lattice.ContourLinksExits
import Code.Lattice.TurningNumber
import Code.Lattice.OrbitEncloses
import Code.Lattice.JordanSingleCycle
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.OrbitExteriorEven
import Code.Lattice.OrbitInteriorOdd
import Code.Lattice.ClosedContourSeparation
import Code.Lattice.BdEdgeMatchStarHull
import Code.Lattice.CornerBalance
import Code.Lattice.EarRemoval
import Code.Lattice.EarExistence
import Code.Lattice.EarContraction
import Code.Lattice.BalancePreservingContraction
import Code.Lattice.JordanSeparationFull
import Code.Lattice.NoDiagTouchClose

open Set SimpleGraph Function

namespace StatMech

namespace Lattice














theorem wei_mpl_orbitLoop_edges_eq (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (mpl_orbitLoop K a).edges
      = (List.range (dartOrbitPeriod K a)).map
          (fun k => s(dartFace ((dartNext K)^[k] a.1), dartFace ((dartNext K)^[k + 1] a.1))) := by
  rw [mpl_orbitLoop_edges, mpl_orbitFaceLoop, SimpleGraph.Walk.edges_copy, orbitFaceWalk_edges]





theorem wei_rayCount_of_perm {a b : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (Vc' : (hypercubicLattice 2).Walk b b) (z : Site 2)
    (hperm : List.Perm Vc.edges Vc'.edges) :
    jec_rayCount z Vc = jec_rayCount z Vc' := by
  classical
  rw [jec_rayCount, jec_rayCount]
  exact List.Perm.countP_eq _ hperm





theorem wei_rayCount_congr (K K' : Set (Site 2)) (hKK : K = K')
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart K' e})
    (ha : a.1 = a'.1) (z : Site 2) :
    jec_rayCount z (mpl_orbitLoop K a) = jec_rayCount z (mpl_orbitLoop K' a') := by
  subst hKK
  rw [Subtype.ext ha]
















theorem wei_loop_edges_diff_singleton (K : Set (Site 2)) (c : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart (K \ {c}) e})
    (hval : a'.1 = a.1)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) :
    (mpl_orbitLoop (K \ {c}) a').edges = (mpl_orbitLoop K a).edges := by
  rw [wei_mpl_orbitLoop_edges_eq, wei_mpl_orbitLoop_edges_eq]
  rw [bpc_dartOrbitPeriod_diff_singleton K c a a' hval hnp]
  apply List.map_congr_left
  intro k _
  rw [hval, bpc_iterate_dartNext_diff_singleton K c a.1 hnp k,
      bpc_iterate_dartNext_diff_singleton K c a.1 hnp (k + 1)]




theorem wei_rayCount_diff_singleton (K : Set (Site 2)) (c : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart (K \ {c}) e})
    (hval : a'.1 = a.1)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) (z : Site 2) :
    jec_rayCount z (mpl_orbitLoop (K \ {c}) a') = jec_rayCount z (mpl_orbitLoop K a) := by
  classical
  rw [jec_rayCount, jec_rayCount, wei_loop_edges_diff_singleton K c a a' hval hnp]






def wei_WindingWitness (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∃ z ∈ K, ¬ Even (jec_rayCount z (mpl_orbitLoop K a))






theorem wei_windingWitness_transfer_diff_singleton (K : Set (Site 2)) (c : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart (K \ {c}) e})
    (hval : a'.1 = a.1)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1))
    (hw : wei_WindingWitness (K \ {c}) a') :
    wei_WindingWitness K a := by
  obtain ⟨z, hzK', hzodd⟩ := hw
  refine ⟨z, ((Set.mem_diff _).mp hzK').1, ?_⟩
  rwa [wei_rayCount_diff_singleton K c a a' hval hnp z] at hzodd













theorem wei_dartFace_trans (w : Site 2) (e : Dart) :
    dartFace (transDart w e) = dartFace e + w := by
  unfold dartFace
  rw [transDart_tail, transDart_dir]
  funext i
  fin_cases i
  · show e.tail 0 + w 0 + negPart (e.dir 0) + negPart (rot90Fun e.dir 0)
      = (e.tail 0 + negPart (e.dir 0) + negPart (rot90Fun e.dir 0)) + w 0
    ring
  · show e.tail 1 + w 1 + negPart (e.dir 1) + negPart (rot90Fun e.dir 1)
      = (e.tail 1 + negPart (e.dir 1) + negPart (rot90Fun e.dir 1)) + w 1
    ring




theorem wei_rayEdge_trans (w z x y : Site 2) :
    jec_rayEdge (z + w) s(x + w, y + w) ↔ jec_rayEdge z s(x, y) := by
  rw [jec_rayEdge_mk, jec_rayEdge_mk]; simp only [Pi.add_apply]; omega






theorem wei_rayCount_trans (K : Set (Site 2)) (w : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2) :
    jec_rayCount (z + w) (mpl_orbitLoop (transSet w K) (transSub K w a))
      = jec_rayCount z (mpl_orbitLoop K a) := by
  classical
  rw [jec_rayCount, jec_rayCount, wei_mpl_orbitLoop_edges_eq, wei_mpl_orbitLoop_edges_eq]
  rw [transSub_val, dartOrbitPeriod_trans]
  have hmap : (List.range (dartOrbitPeriod K a)).map
        (fun k => s(dartFace ((dartNext (transSet w K))^[k] (transDart w a.1)),
          dartFace ((dartNext (transSet w K))^[k + 1] (transDart w a.1))))
      = (List.range (dartOrbitPeriod K a)).map
        (fun k => s(dartFace ((dartNext K)^[k] a.1) + w,
          dartFace ((dartNext K)^[k + 1] a.1) + w)) := by
    apply List.map_congr_left
    intro k _
    rw [iterate_dartNext_trans, iterate_dartNext_trans, wei_dartFace_trans, wei_dartFace_trans]
  rw [hmap, List.countP_map, List.countP_map]
  apply List.countP_congr
  intro k _
  simp only [Function.comp_apply, decide_eq_true_eq]
  exact wei_rayEdge_trans w z _ _













theorem wei_ucBase1_edges :
    (mpl_orbitLoop unitCell ucBase1).edges
      = [s((![0, -1] : Site 2), ![-1, -1]), s((![-1, -1] : Site 2), ![-1, 0]),
          s((![-1, 0] : Site 2), ![0, 0]), s((![0, 0] : Site 2), ![0, -1])] := by
  rw [wei_mpl_orbitLoop_edges_eq, ucBase1_orbitPeriod]
  show ((List.range 4).map (fun k => s(dartFace ((dartNext unitCell)^[k] ucDart1),
      dartFace ((dartNext unitCell)^[k + 1] ucDart1)))) = _
  rw [show (List.range 4) = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [show ((dartNext unitCell)^[0] ucDart1) = ucDart1 from rfl, it1_1, it1_2, it1_3, it1_4]
  rw [mpl_dartFace_ucDart1, mpl_dartFace_ucDart2, mpl_dartFace_ucDart3, mpl_dartFace_ucDart0]


theorem wei_ucBase2_edges :
    (mpl_orbitLoop unitCell ucBase2).edges
      = [s((![-1, -1] : Site 2), ![-1, 0]), s((![-1, 0] : Site 2), ![0, 0]),
          s((![0, 0] : Site 2), ![0, -1]), s((![0, -1] : Site 2), ![-1, -1])] := by
  rw [wei_mpl_orbitLoop_edges_eq, ucBase2_orbitPeriod]
  show ((List.range 4).map (fun k => s(dartFace ((dartNext unitCell)^[k] ucDart2),
      dartFace ((dartNext unitCell)^[k + 1] ucDart2)))) = _
  rw [show (List.range 4) = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [show ((dartNext unitCell)^[0] ucDart2) = ucDart2 from rfl, it2_1, it2_2, it2_3, it2_4]
  rw [mpl_dartFace_ucDart2, mpl_dartFace_ucDart3, mpl_dartFace_ucDart0, mpl_dartFace_ucDart1]


theorem wei_ucBase3_edges :
    (mpl_orbitLoop unitCell ucBase3).edges
      = [s((![-1, 0] : Site 2), ![0, 0]), s((![0, 0] : Site 2), ![0, -1]),
          s((![0, -1] : Site 2), ![-1, -1]), s((![-1, -1] : Site 2), ![-1, 0])] := by
  rw [wei_mpl_orbitLoop_edges_eq, ucBase3_orbitPeriod]
  show ((List.range 4).map (fun k => s(dartFace ((dartNext unitCell)^[k] ucDart3),
      dartFace ((dartNext unitCell)^[k + 1] ucDart3)))) = _
  rw [show (List.range 4) = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [show ((dartNext unitCell)^[0] ucDart3) = ucDart3 from rfl, it3_1, it3_2, it3_3, it3_4]
  rw [mpl_dartFace_ucDart3, mpl_dartFace_ucDart0, mpl_dartFace_ucDart1, mpl_dartFace_ucDart2]





theorem wei_unitCell_basepoint_rayCount (b : {e : Dart // IsBoundaryDart unitCell e})
    (hb : b.1 = ucDart0 ∨ b.1 = ucDart1 ∨ b.1 = ucDart2 ∨ b.1 = ucDart3) :
    jec_rayCount (![0, 0] : Site 2) (mpl_orbitLoop unitCell b) = 1 := by
  rcases hb with h | h | h | h
  · have hb0 : b = ucBase := Subtype.ext h
    rw [hb0]; exact mpl_unitCell_rayCount_eq_one
  · have hb1 : b = ucBase1 := Subtype.ext h
    rw [hb1, wei_rayCount_of_perm (mpl_orbitLoop unitCell ucBase1) (mpl_orbitLoop unitCell ucBase)
        (![0, 0] : Site 2) ?_]
    · exact mpl_unitCell_rayCount_eq_one
    · rw [wei_ucBase1_edges, jsf_unitCell_loop_edges]; decide
  · have hb2 : b = ucBase2 := Subtype.ext h
    rw [hb2, wei_rayCount_of_perm (mpl_orbitLoop unitCell ucBase2) (mpl_orbitLoop unitCell ucBase)
        (![0, 0] : Site 2) ?_]
    · exact mpl_unitCell_rayCount_eq_one
    · rw [wei_ucBase2_edges, jsf_unitCell_loop_edges]; decide
  · have hb3 : b = ucBase3 := Subtype.ext h
    rw [hb3, wei_rayCount_of_perm (mpl_orbitLoop unitCell ucBase3) (mpl_orbitLoop unitCell ucBase)
        (![0, 0] : Site 2) ?_]
    · exact mpl_unitCell_rayCount_eq_one
    · rw [wei_ucBase3_edges, jsf_unitCell_loop_edges]; decide






theorem wei_singleton_windingWitness (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}) :
    wei_WindingWitness ({v} : Set (Site 2)) a := by
  refine ⟨v, Set.mem_singleton _, ?_⟩
  
  obtain ⟨b, hbU, hval⟩ : ∃ b : {e : Dart // IsBoundaryDart unitCell e},
      (b.1 = ucDart0 ∨ b.1 = ucDart1 ∨ b.1 = ucDart2 ∨ b.1 = ucDart3) ∧
        a.1 = transDart v b.1 := by
    rcases singleton_boundaryDart_eq_transDart v a.1 a.2 with
      ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
    · exact ⟨ucBase, Or.inl rfl, he⟩
    · exact ⟨ucBase2, Or.inr (Or.inr (Or.inl rfl)), he⟩
    · exact ⟨ucBase3, Or.inr (Or.inr (Or.inr rfl)), he⟩
    · exact ⟨ucBase1, Or.inr (Or.inl rfl), he⟩
  
  have hset : ({v} : Set (Site 2)) = transSet v unitCell := (transSet_unitCell v).symm
  
  have hcongr : jec_rayCount v (mpl_orbitLoop ({v} : Set (Site 2)) a)
      = jec_rayCount v (mpl_orbitLoop (transSet v unitCell) (transSub unitCell v b)) := by
    apply wei_rayCount_congr ({v} : Set (Site 2)) (transSet v unitCell) hset
    rw [hval, transSub_val]
  rw [hcongr]
  
  have hv0 : ((![0, 0] : Site 2) + v) = v := by funext i; fin_cases i <;> simp
  have htrans := wei_rayCount_trans unitCell v b (![0, 0] : Site 2)
  rw [hv0] at htrans
  rw [htrans, wei_unitCell_basepoint_rayCount b hbU]
  decide
















def wei_WindingSaturatingWitness : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
    ∀ (a : {e : Dart // IsBoundaryDart K e}),
      K ⊆ bpc_orbitFootprint K a → wei_WindingWitness K a








theorem wei_windingWitness_of_descent (hres : wei_WindingSaturatingWitness)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) : wei_WindingWitness K a := by
  generalize hn : K.ncard = n
  induction n using Nat.strong_induction_on generalizing K with
  | _ n IH =>
    subst hn
    rcases Nat.lt_or_ge K.ncard 2 with hlt | hge
    · 
      have h1 : K.ncard = 1 := by
        have hpos : 0 < K.ncard := (Set.ncard_pos hK).mpr hne
        omega
      obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp h1
      subst hv
      exact wei_singleton_windingWitness v a
    · 
      by_cases hsat : K ⊆ bpc_orbitFootprint K a
      · exact hres K hK hge a hsat
      · 
        rw [Set.not_subset] at hsat
        obtain ⟨c, hcK, hc⟩ := hsat
        have hne_tail : c ≠ a.1.tail := bpc_ne_tail_of_not_footprint K a c hc
        have hbd : IsBoundaryDart (K \ {c}) a.1 :=
          bpc_isBoundaryDart_diff_singleton K c a.1 a.2 hne_tail
        set a' : {e : Dart // IsBoundaryDart (K \ {c}) e} := ⟨a.1, hbd⟩ with ha'
        have hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1) :=
          bpc_notProbed_of_not_footprint K a c hc
        have hK' : (K \ {c}).Finite := hK.subset Set.diff_subset
        
        have hcard_eq : (K \ {c}).ncard = K.ncard - 1 := Set.ncard_diff_singleton_of_mem hcK
        have hne' : (K \ {c}).Nonempty := by
          rw [← Set.ncard_pos hK', hcard_eq]; omega
        have hncard_lt : (K \ {c}).ncard < K.ncard := by rw [hcard_eq]; omega
        have hw' : wei_WindingWitness (K \ {c}) a' :=
          IH (K \ {c}).ncard hncard_lt (K \ {c}) hK' hne' a' rfl
        exact wei_windingWitness_transfer_diff_singleton K c a a' (by rw [ha']) hnp hw'














theorem wei_starHull_windingWitness_of_residue (hres : wei_WindingSaturatingWitness)
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    wei_WindingWitness (ndt_StarHull K) a :=
  wei_windingWitness_of_descent hres (ndt_StarHull K) hSK hne a








theorem wei_insideHalf_of_windingWitness (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {z0 : Site 2} (_hz0 : z0 ∈ K)
    (hodd0 : ¬ Even (jec_rayCount z0 (mpl_orbitLoop K a)))
    (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support)) :
    ∀ z, z ∈ K → ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) := by
  intro z hz
  obtain ⟨p, hp⟩ := hInt z hz
  exact ooi_odd_of_connected_to_odd (mpl_orbitLoop K a) p hp hodd0
















theorem wei_starHull_bdEdgeMatch_of_residue (hres : wei_WindingSaturatingWitness)
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hInt : ∀ z0, z0 ∈ ndt_StarHull K →
      ∀ z, z ∈ ndt_StarHull K → ∃ p : (hypercubicLattice 2).Walk z z0,
        (∀ w ∈ p.support, w ∉ (mpl_orbitLoop (ndt_StarHull K) a).support))
    (hout : ∀ z, z ∉ ndt_StarHull K →
      Even (jec_rayCount z (mpl_orbitLoop (ndt_StarHull K) a))) :
    pww_BdEdgeMatch (ndt_StarHull K) (mpl_orbitLoop (ndt_StarHull K) a) := by
  obtain ⟨z0, hz0K, hz0odd⟩ := wei_starHull_windingWitness_of_residue hres K hSK hne a
  have hin : ∀ z, z ∈ ndt_StarHull K →
      ¬ Even (jec_rayCount z (mpl_orbitLoop (ndt_StarHull K) a)) :=
    wei_insideHalf_of_windingWitness (ndt_StarHull K) a hz0K hz0odd (hInt z0 hz0K)
  exact jsf_starHull_bdEdgeMatch_of_rayParity K a hin hout











theorem wei_unitCell_windingWitness : wei_WindingWitness unitCell ucBase := by
  refine ⟨![0, 0], ?_, ?_⟩
  · simp only [unitCell, Set.mem_singleton_iff]
  · rw [mpl_unitCell_rayCount_eq_one]; decide


























































end Lattice

end StatMech
