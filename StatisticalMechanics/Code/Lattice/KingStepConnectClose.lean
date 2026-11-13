/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.JordanInteriorLib
import Code.Lattice.InteriorWindingClose
import Code.Lattice.SegmentDownClose
import Code.Lattice.MatchedConnectivityInterior
import Code.Lattice.RowLinkedClose
import Code.Lattice.KingSegmentDownClose
import Code.Lattice.KingDescentAgnosticClose

open Set SimpleGraph Function

namespace StatMech

namespace Lattice













def ksc_KingSaturated {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (T : Set (Site 2)) : Prop :=
  ∀ u v : Site 2, u ∈ T → v ∈ jil_offSupportInterior Vc → mci_kingGraph.Adj u v → v ∈ T









def ksc_NoKingSeparation {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) : Prop :=
  ∀ T : Set (Site 2), seed ∈ T → T ⊆ jil_offSupportInterior Vc →
    ksc_KingSaturated Vc T → jil_offSupportInterior Vc ⊆ T











theorem ksc_reachableSet_saturated {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc) :
    ksc_KingSaturated Vc
      {v | ∃ hv : v ∈ jil_offSupportInterior Vc,
        (mci_interiorKingGraph Vc).Reachable ⟨v, hv⟩ ⟨seed, hseedI⟩} := by
  rintro u v ⟨hu, hru⟩ hvI hadj
  refine ⟨hvI, ?_⟩
  have hadjI : (mci_interiorKingGraph Vc).Adj ⟨v, hvI⟩ ⟨u, hu⟩ := by
    rw [mci_interiorKingGraph, SimpleGraph.induce_adj]; exact hadj.symm
  exact (hadjI.reachable).trans hru





theorem ksc_kingStepReachable_of_noKingSeparation {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {seed : Site 2}
    (hseedI : seed ∈ jil_offSupportInterior Vc) (hns : ksc_NoKingSeparation Vc seed) :
    ∀ z : jil_offSupportInterior Vc, (mci_interiorKingGraph Vc).Reachable z ⟨seed, hseedI⟩ := by
  set T : Set (Site 2) := {v | ∃ hv : v ∈ jil_offSupportInterior Vc,
      (mci_interiorKingGraph Vc).Reachable ⟨v, hv⟩ ⟨seed, hseedI⟩} with hT
  have hseedT : seed ∈ T := ⟨hseedI, Reachable.refl _⟩
  have hTsub : T ⊆ jil_offSupportInterior Vc := by rintro v ⟨hv, _⟩; exact hv
  have hsat : ksc_KingSaturated Vc T := ksc_reachableSet_saturated Vc hseedI
  have hfull := hns T hseedT hTsub hsat
  intro z
  obtain ⟨hzI, hzr⟩ := hfull z.2
  exact hzr







theorem ksc_kingRowLinked_of_noKingSeparation {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc)
    (hns : ksc_NoKingSeparation Vc seed) :
    mci_KingRowLinked Vc seed :=
  mci_kingRowLinked_of_kingStepReachable Vc hseedI
    (ksc_kingStepReachable_of_noKingSeparation Vc hseedI hns)




theorem ksc_kingInteriorConnected_of_noKingSeparation {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {seed : Site 2}
    (hseedI : seed ∈ jil_offSupportInterior Vc) (hns : ksc_NoKingSeparation Vc seed) :
    mci_KingInteriorConnected Vc :=
  ⟨seed, hseedI, ksc_kingRowLinked_of_noKingSeparation Vc hseedI hns⟩












theorem ksc_saturated_absorbs_walk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T)
    {s t : jil_offSupportInterior Vc} (hsT : (s : Site 2) ∈ T)
    (w : (mci_interiorKingGraph Vc).Walk s t) : (t : Site 2) ∈ T := by
  induction w with
  | nil => exact hsT
  | @cons u v r hadj q ih =>
    have hadj' : mci_kingGraph.Adj (u : Site 2) (v : Site 2) := by
      rw [mci_interiorKingGraph, SimpleGraph.induce_adj] at hadj; exact hadj
    exact ih (hsat u v hsT v.2 hadj')







theorem ksc_noKingSeparation_of_kingStepReachable {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {seed : Site 2}
    (hseedI : seed ∈ jil_offSupportInterior Vc)
    (hreach : ∀ z : jil_offSupportInterior Vc,
      (mci_interiorKingGraph Vc).Reachable z ⟨seed, hseedI⟩) :
    ksc_NoKingSeparation Vc seed := by
  intro T hseedT _hTsub hsat z hz
  obtain ⟨w⟩ := (hreach ⟨z, hz⟩).symm
  exact ksc_saturated_absorbs_walk Vc hsat hseedT w




theorem ksc_noKingSeparation_iff_kingStepReachable {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {seed : Site 2}
    (hseedI : seed ∈ jil_offSupportInterior Vc) :
    ksc_NoKingSeparation Vc seed ↔
      ∀ z : jil_offSupportInterior Vc,
        (mci_interiorKingGraph Vc).Reachable z ⟨seed, hseedI⟩ :=
  ⟨ksc_kingStepReachable_of_noKingSeparation Vc hseedI,
   ksc_noKingSeparation_of_kingStepReachable Vc hseedI⟩










theorem ksc_saturated_axial {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) {u v : Site 2} (hu : u ∈ T)
    (hvI : v ∈ jil_offSupportInterior Vc) (hadj : (hypercubicLattice 2).Adj u v) : v ∈ T :=
  hsat u v hu hvI (mci_hyper_le_king hadj)






theorem ksc_saturated_diag {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) {x y sx sy : ℤ}
    (hsx : sx = 1 ∨ sx = -1) (hsy : sy = 1 ∨ sy = -1)
    (hxy : (![x, y] : Site 2) ∈ T)
    (hdI : (![x + sx, y + sy] : Site 2) ∈ jil_offSupportInterior Vc) :
    (![x + sx, y + sy] : Site 2) ∈ T :=
  hsat _ _ hxy hdI (mci_kingAdj_diag x y sx sy hsx hsy)





theorem ksc_saturated_diagBridge {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) {x y : ℤ}
    (hxy : (![x, y] : Site 2) ∈ T) (hxyI : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hdiag : (![x + 1, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (helb_off : (![x + 1, y] : Site 2) ∉ Vc.support) :
    (![x + 1, y + 1] : Site 2) ∈ T := by
  obtain ⟨helb, h1, h2⟩ := mci_diagonal_king_bridge Vc hxyI hdiag helb_off
  have hadj1 : mci_kingGraph.Adj (![x, y] : Site 2) (![x + 1, y] : Site 2) := by
    rw [mci_interiorKingGraph, SimpleGraph.induce_adj] at h1; exact h1
  have helbT : (![x + 1, y] : Site 2) ∈ T := hsat _ _ hxy helb hadj1
  have hadj2 : mci_kingGraph.Adj (![x + 1, y] : Site 2) (![x + 1, y + 1] : Site 2) := by
    rw [mci_interiorKingGraph, SimpleGraph.induce_adj] at h2; exact h2
  exact hsat _ _ helbT hdiag hadj2

















theorem ksc_separated_midOnSupport_horiz {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {x y : ℤ} (hL : (![x - 1, y] : Site 2) ∈ T)
    (hR : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hRnT : (![x + 1, y] : Site 2) ∉ T) :
    (![x, y] : Site 2) ∈ Vc.support := by
  by_contra hmid
  have hLI : (![x - 1, y] : Site 2) ∈ jil_offSupportInterior Vc := hTsub hL
  have hadjLM : (hypercubicLattice 2).Adj (![x - 1, y] : Site 2) (![x, y] : Site 2) := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  have hmidI : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc :=
    mci_offSupport_neighbor_interior Vc hLI hadjLM hmid
  have hmidT : (![x, y] : Site 2) ∈ T := ksc_saturated_axial Vc hsat hL hmidI hadjLM
  have hadjMR : (hypercubicLattice 2).Adj (![x, y] : Site 2) (![x + 1, y] : Site 2) := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  exact hRnT (ksc_saturated_axial Vc hsat hmidT hR hadjMR)




theorem ksc_separated_midOnSupport_vert {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {x y : ℤ} (hD : (![x, y - 1] : Site 2) ∈ T)
    (hU : (![x, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (hUnT : (![x, y + 1] : Site 2) ∉ T) :
    (![x, y] : Site 2) ∈ Vc.support := by
  by_contra hmid
  have hDI : (![x, y - 1] : Site 2) ∈ jil_offSupportInterior Vc := hTsub hD
  have hadjDM : (hypercubicLattice 2).Adj (![x, y - 1] : Site 2) (![x, y] : Site 2) := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  have hmidI : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc :=
    mci_offSupport_neighbor_interior Vc hDI hadjDM hmid
  have hmidT : (![x, y] : Site 2) ∈ T := ksc_saturated_axial Vc hsat hD hmidI hadjDM
  have hadjMU : (hypercubicLattice 2).Adj (![x, y] : Site 2) (![x, y + 1] : Site 2) := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  exact hUnT (ksc_saturated_axial Vc hsat hmidT hU hadjMU)












theorem ksc_interiorKing_reachable_of_kingWalk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    ∀ {z seed : Site 2} (p : mci_kingGraph.Walk z seed)
      (_hp : ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc)
      (hzI : z ∈ jil_offSupportInterior Vc) (hseedI : seed ∈ jil_offSupportInterior Vc),
        (mci_interiorKingGraph Vc).Reachable ⟨z, hzI⟩ ⟨seed, hseedI⟩ := by
  intro z seed p
  induction p with
  | nil => intro _ _ _; exact Reachable.refl _
  | @cons u v t hadj r ih =>
    intro hp hzI hseedI
    have hvI : v ∈ jil_offSupportInterior Vc := hp v (by
      rw [SimpleGraph.Walk.support_cons]; right; exact r.start_mem_support)
    have htail : ∀ w ∈ r.support, w ∈ jil_offSupportInterior Vc := fun w hw =>
      hp w (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hw)
    have hstep : (mci_interiorKingGraph Vc).Adj ⟨u, hzI⟩ ⟨v, hvI⟩ := by
      rw [mci_interiorKingGraph, SimpleGraph.induce_adj]; exact hadj
    exact (hstep.reachable).trans (ih htail hvI hseedI)






theorem ksc_noKingSeparation_of_kingRowLinked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc)
    (hrl : mci_KingRowLinked Vc seed) :
    ksc_NoKingSeparation Vc seed := by
  refine ksc_noKingSeparation_of_kingStepReachable Vc hseedI ?_
  intro z
  obtain ⟨p, hp⟩ := hrl z z.2
  exact ksc_interiorKing_reachable_of_kingWalk Vc p hp z.2 hseedI





theorem ksc_noKingSeparation_singleton {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hsingle : jil_offSupportInterior Vc = {seed}) :
    ksc_NoKingSeparation Vc seed := by
  intro T hseedT _ _
  rw [hsingle]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  exact hz ▸ hseedT

















theorem ksc_ksd_noKingSeparation : ksc_NoKingSeparation ksd_stair (![1, 1] : Site 2) :=
  ksc_noKingSeparation_of_kingRowLinked ksd_stair ksd_mem_interior_11 ksd_kingRowLinked






theorem ksc_kda_noKingSeparation : ksc_NoKingSeparation kda_stairDR (![3, 1] : Site 2) :=
  ksc_noKingSeparation_of_kingRowLinked kda_stairDR kda_mem_interior_31 kda_stairDR_kingRowLinked


theorem ksc_fjord_col4 (r : ℤ) (h1 : 0 ≤ r) (h2 : r ≤ 3) :
    (![4, r] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; left; exact sdc_vsegUp_mem' 4 0 3 r h1 h2


theorem ksc_fjord_col7 (r : ℤ) (h1 : 0 ≤ r) (h2 : r ≤ 4) :
    (![7, r] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; right; right; left; exact sdc_vsegUp_mem' 7 0 4 r h1 h2


theorem ksc_fjord_row0 (c : ℤ) (h1 : 4 ≤ c) (h2 : c ≤ 7) :
    (![c, 0] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; right; left; exact sdc_hsegRight_mem' 0 4 3 c h1 h2


theorem ksc_fjord_row4 (c : ℤ) (h1 : 0 ≤ c) (h2 : c ≤ 7) :
    (![c, 4] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; right; right; right; left; exact sdc_hsegRight_mem' 4 0 7 c h1 h2







theorem ksc_fjord_rp_king_step {u v : Site 2} (hu : u ∈ iwc_RightPocket)
    (hadj : mci_kingGraph.Adj u v) (hv : v ∉ sdc_fjord.support) :
    v ∈ iwc_RightPocket := by
  rw [iwc_mem_rightPocket] at hu ⊢
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨h0, h1, hne⟩ := hadj
  by_contra hvnot
  apply hv
  have hveq : v = ![v 0, v 1] := by ext i; fin_cases i <;> simp
  have hb0 : v 0 = 4 ∨ v 0 = 5 ∨ v 0 = 6 ∨ v 0 = 7 := by
    rcases hu0 with h | h <;> simp only [h] at h0 ⊢ <;> omega
  have hb1 : v 1 = 0 ∨ v 1 = 1 ∨ v 1 = 2 ∨ v 1 = 3 ∨ v 1 = 4 := by
    rcases hu1 with h | h | h <;> simp only [h] at h1 ⊢ <;> omega
  simp only [not_and_or] at hvnot
  rw [hveq]
  rcases hb0 with e0 | e0 | e0 | e0 <;> rcases hb1 with e1 | e1 | e1 | e1 | e1 <;> rw [e0, e1] <;>
    first
      | exact ksc_fjord_row0 _ (by norm_num) (by norm_num)
      | exact ksc_fjord_row4 _ (by norm_num) (by norm_num)
      | exact ksc_fjord_col4 _ (by norm_num) (by norm_num)
      | exact ksc_fjord_col7 _ (by norm_num) (by norm_num)
      | (exfalso; omega)




theorem ksc_fjord_rp_interior (z : Site 2) (hz : z ∈ iwc_RightPocket) :
    z ∈ jil_offSupportInterior sdc_fjord := by
  have hoff : z ∉ sdc_fjord.support := by
    intro h
    have hl := sdc_fjord_support_locus z h
    rw [iwc_mem_rightPocket] at hz
    obtain ⟨h0, h1⟩ := hz
    rcases h0 with e0 | e0 <;> rcases h1 with e1 | e1 | e1 <;>
      simp only [e0, e1] at hl <;> omega
  refine (jil_mem_offSupportInterior sdc_fjord z).mpr ⟨hoff, ?_⟩
  rw [jec_mem_leftRegion, sdc_fjord_raycount]
  rw [iwc_mem_rightPocket] at hz
  obtain ⟨h0, h1⟩ := hz
  rcases h0 with e0 | e0 <;> rcases h1 with e1 | e1 | e1 <;> simp only [e0, e1] <;> decide










theorem ksc_fjord_noKingSeparation_false :
    ¬ ksc_NoKingSeparation sdc_fjord (![5, 1] : Site 2) := by
  intro hns
  have hsub := hns iwc_RightPocket iwc_mem_rightPocket_51 ksc_fjord_rp_interior
    (fun u v hu hvI hadj => ksc_fjord_rp_king_step hu hadj
      (jil_mem_offSupportInterior sdc_fjord v |>.mp hvI).1)
  exact iwc_not_rightPocket_11 (hsub sdc_fjord_mem_interior_11)









theorem ksc_fjord_rp_is_king_separation :
    iwc_RightPocket ⊆ jil_offSupportInterior sdc_fjord ∧
    ksc_KingSaturated sdc_fjord iwc_RightPocket ∧
    ¬ jil_offSupportInterior sdc_fjord ⊆ iwc_RightPocket :=
  ⟨ksc_fjord_rp_interior,
   fun _u v hu hvI hadj => ksc_fjord_rp_king_step hu hadj
     (jil_mem_offSupportInterior sdc_fjord v |>.mp hvI).1,
   fun hsub => iwc_not_rightPocket_11 (hsub sdc_fjord_mem_interior_11)⟩






theorem ksc_saturated_absorbs_kingWalk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) :
    ∀ {x y : Site 2} (q : mci_kingGraph.Walk x y),
      (∀ w ∈ q.support, w ∈ jil_offSupportInterior Vc) → x ∈ T → y ∈ T := by
  intro x y q
  induction q with
  | nil => intro _ hx; exact hx
  | @cons u v t hadj r ih =>
    intro hq hu
    have hvI : v ∈ jil_offSupportInterior Vc := hq v (by
      rw [SimpleGraph.Walk.support_cons]; right; exact r.start_mem_support)
    have hvT : v ∈ T := hsat u v hu hvI hadj
    have htail : ∀ w ∈ r.support, w ∈ jil_offSupportInterior Vc := fun w hw =>
      hq w (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hw)
    exact ih htail hvT










theorem ksc_fjord_kingRowLinked_false :
    ¬ mci_KingRowLinked sdc_fjord (![5, 1] : Site 2) := by
  intro hrl
  obtain ⟨p, hp⟩ := hrl (![1, 1] : Site 2) sdc_fjord_mem_interior_11
  have hRPsat : ksc_KingSaturated sdc_fjord iwc_RightPocket :=
    (ksc_fjord_rp_is_king_separation).2.1
  have hrev : ∀ w ∈ p.reverse.support, w ∈ jil_offSupportInterior sdc_fjord := by
    intro w hw; rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw; exact hp w hw
  have h11RP : (![1, 1] : Site 2) ∈ iwc_RightPocket :=
    ksc_saturated_absorbs_kingWalk sdc_fjord hRPsat p.reverse hrev iwc_mem_rightPocket_51
  exact iwc_not_rightPocket_11 h11RP












theorem ksc_kingRowLinked_iff_summary {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc) :
    ksc_NoKingSeparation Vc seed →
      mci_KingRowLinked Vc seed :=
  ksc_kingRowLinked_of_noKingSeparation Vc hseedI

end Lattice

end StatMech
