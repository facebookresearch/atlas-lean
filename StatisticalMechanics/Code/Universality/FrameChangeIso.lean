/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Mathlib
import Code.RSW.Defs
import Code.RSW.SelfDuality
import Code.Lattice.CrossingParity
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters
import Code.Lattice.FaceRegion
import Code.Lattice.JordanContour
import Code.Universality.BoxCrossingDichotomy
import Code.Universality.DualCircuitToWalk
import Code.Universality.FaceDualDichotomy
import Code.Lattice.JordanFaithfulCount
import Code.Universality.G3PercDualityFull

open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}
















theorem fci_faceBoundaryGraph_le_dualLattice (S : Set (Site 2)) :
    faceBoundaryGraph S ≤ dualLattice :=
  faceBoundaryGraph_le S




def fci_faceWalk_to_dualWalk (S : Set (Site 2)) {u v : Site 2}
    (c : (faceBoundaryGraph S).Walk u v) : dualLattice.Walk u v :=
  c.mapLe (fci_faceBoundaryGraph_le_dualLattice S)


theorem fci_faceWalk_to_dualWalk_support (S : Set (Site 2)) {u v : Site 2}
    (c : (faceBoundaryGraph S).Walk u v) :
    (fci_faceWalk_to_dualWalk S c).support = c.support := by
  rw [fci_faceWalk_to_dualWalk, SimpleGraph.Walk.support_mapLe_eq_support]




theorem fci_faceCycle_to_dualCycle (S : Set (Site 2)) {u : Site 2}
    (c : (faceBoundaryGraph S).Walk u u) (hc : c.IsCycle) :
    (fci_faceWalk_to_dualWalk S c).IsCycle :=
  hc.mapLe (fci_faceBoundaryGraph_le_dualLattice S)

















def fci_faceOpenDual (ω : ConfigSpace (Sym2 (Site 2))) : SimpleGraph (Site 2) where
  Adj f g := (hypercubicLattice 2).Adj f g ∧ ω (sharedPrimalEdge f g) = false
  symm := by
    rintro f g ⟨hadj, hcl⟩
    exact ⟨hadj.symm, by rw [← sharedPrimalEdge_comm_of_adj hadj]; exact hcl⟩
  loopless := ⟨fun f h => (hypercubicLattice 2).irrefl h.1⟩

@[simp] theorem fci_faceOpenDual_adj (ω : ConfigSpace (Sym2 (Site 2))) (f g : Site 2) :
    (fci_faceOpenDual ω).Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧ ω (sharedPrimalEdge f g) = false := Iff.rfl


theorem fci_faceOpenDual_le_dualLattice (ω : ConfigSpace (Sym2 (Site 2))) :
    fci_faceOpenDual ω ≤ dualLattice := fun _ _ h => h.1




theorem fci_faceBoundaryGraph_cluster_le (o : Site 2) :
    faceBoundaryGraph (cluster 2 ω o) ≤ fci_faceOpenDual ω := by
  rintro f g ⟨hlat, hbd⟩
  refine ⟨hlat, ?_⟩
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge hlat
  rw [hpq] at hbd ⊢
  rw [bdEdge_mk] at hbd
  exact cluster_edgeBoundary_isClosed o ⟨hadj, hbd⟩







theorem fci_cluster_faceOpenDual_circuit (o : Site 2) (hfin : (cluster 2 ω o).Finite)
    {z : Site 2} (w : (hypercubicLattice 2).Walk o z) (hz : z ∉ cluster 2 ω o) :
    ∃ (u : Site 2) (c : (fci_faceOpenDual ω).Walk u u), c.IsCycle := by
  obtain ⟨u, c, hcyc, _⟩ := fdd_cluster_dualCircuit_open o hfin w hz
  exact ⟨u, c.mapLe (fci_faceBoundaryGraph_cluster_le o),
    hcyc.mapLe (fci_faceBoundaryGraph_cluster_le o)⟩








theorem fci_leftReach_faceOpenDual_adj_of_closed (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {f g : Site 2} (h : (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g)
    (hcl : ω (sharedPrimalEdge f g) = false) :
    (fci_faceOpenDual ω).Adj f g :=
  ⟨h.1, hcl⟩







theorem fci_leftReach_faceOpenDual_cycle (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle :=
  fdd_leftReach_dualCircuit ω n hn hnoH






















def fci_FrameCompat (Φ : Site 2 → Site 2) : Prop :=
  ∀ f g : Site 2, (hypercubicLattice 2).Adj f g →
    crossEdge (sharedPrimalEdge f g) = s(Φ f, Φ g)

theorem fci_face_adj_left (a b : ℤ) :
    (hypercubicLattice 2).Adj ![a, b] ![a - 1, b] := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]

theorem fci_face_adj_right (a b : ℤ) :
    (hypercubicLattice 2).Adj ![a, b] ![a + 1, b] := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]












theorem fci_no_frameChangeIso : ¬ ∃ Φ : Site 2 → Site 2, fci_FrameCompat Φ := by
  rintro ⟨Φ, hΦ⟩
  have hL := hΦ ![0, 0] ![0 - 1, 0] (fci_face_adj_left 0 0)
  rw [fdd_dualEdge_leftSide] at hL
  have hR := hΦ ![0, 0] ![0 + 1, 0] (fci_face_adj_right 0 0)
  rw [fdd_dualEdge_rightSide] at hR
  have hmemL : Φ ![0, 0] ∈ s(![(-0 : ℤ), 0], ![-(0 + 1), 0]) := by
    rw [hL]; exact Sym2.mem_mk_left _ _
  have hmemR : Φ ![0, 0] ∈ s(![(-0 : ℤ), 0 + 1], ![-(0 + 1), 0 + 1]) := by
    rw [hR]; exact Sym2.mem_mk_left _ _
  have h1 : (Φ ![0, 0]) 1 = 0 := by
    rw [Sym2.mem_iff] at hmemL
    rcases hmemL with h | h <;> rw [h] <;> simp
  have h2 : (Φ ![0, 0]) 1 = 1 := by
    rw [Sym2.mem_iff] at hmemR
    rcases hmemR with h | h <;> rw [h] <;> simp
  rw [h1] at h2; exact absurd h2 (by norm_num)














theorem fci_no_open_dual_relabel :
    ¬ ∃ Φ : Site 2 → Site 2, ∀ (f g : Site 2), (hypercubicLattice 2).Adj f g →
      sharedPrimalEdge f g = s(rot90Inv (Φ f), rot90Inv (Φ g)) := by
  rintro ⟨Φ, hΦ⟩
  refine fci_no_frameChangeIso ⟨fun x => Φ x, ?_⟩
  intro f g hadj
  rw [hΦ f g hadj, crossEdge_mk]
  
  rw [show rot90Fun (rot90Inv (Φ f)) = Φ f from rot90Equiv.right_inv (Φ f),
     show rot90Fun (rot90Inv (Φ g)) = Φ g from rot90Equiv.right_inv (Φ g)]











noncomputable def fci_sharedEdgeRaw : Sym2 (Site 2) → Sym2 (Site 2) :=
  Sym2.lift <| ⟨fun f g => if h : (hypercubicLattice 2).Adj f g then
      sharedPrimalEdge f g else s(f, g), by
    intro f g
    dsimp
    by_cases h : (hypercubicLattice 2).Adj f g
    · rw [if_pos h, if_pos h.symm]
      exact sharedPrimalEdge_comm_of_adj h
    · rw [if_neg h, if_neg (fun h' => h h'.symm), Sym2.eq_swap] ⟩

@[simp] theorem fci_sharedEdgeRaw_mk_of_adj {f g : Site 2}
    (h : (hypercubicLattice 2).Adj f g) :
    fci_sharedEdgeRaw s(f, g) = sharedPrimalEdge f g := by
  change (if _h : (hypercubicLattice 2).Adj f g then
    sharedPrimalEdge f g else s(f, g)) = sharedPrimalEdge f g
  split <;> simp_all

private theorem fci_sym2_exists (e : Sym2 (Site 2)) : ∃ f g : Site 2, e = s(f, g) := by
  induction e using Sym2.inductionOn with
  | _ f g => exact ⟨f, g, rfl⟩


noncomputable def fci_sharedEdgeMap : (hypercubicLattice 2).edgeSet →
    (hypercubicLattice 2).edgeSet := fun e => ⟨fci_sharedEdgeRaw e.1, by
  obtain ⟨f, g, hval⟩ := fci_sym2_exists e.1
  have hfg : (hypercubicLattice 2).Adj f g :=
    (SimpleGraph.mem_edgeSet _).mp (hval ▸ e.2)
  rw [hval, fci_sharedEdgeRaw_mk_of_adj hfg]
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge hfg
  rw [hpq, SimpleGraph.mem_edgeSet]
  exact hadj ⟩

theorem fci_sharedEdgeMap_injective : Function.Injective fci_sharedEdgeMap := by
  intro e e' heq
  apply Subtype.ext
  obtain ⟨f, g, hval⟩ := fci_sym2_exists e.1
  obtain ⟨f', g', hval'⟩ := fci_sym2_exists e'.1
  have hfg : (hypercubicLattice 2).Adj f g :=
    (SimpleGraph.mem_edgeSet _).mp (hval ▸ e.2)
  have hfg' : (hypercubicLattice 2).Adj f' g' :=
    (SimpleGraph.mem_edgeSet _).mp (hval' ▸ e'.2)
  have hshared : sharedPrimalEdge f g = sharedPrimalEdge f' g' := by
    have heq' := congrArg Subtype.val heq
    change fci_sharedEdgeRaw e.1 = fci_sharedEdgeRaw e'.1 at heq'
    rwa [hval, hval', fci_sharedEdgeRaw_mk_of_adj hfg,
      fci_sharedEdgeRaw_mk_of_adj hfg'] at heq'
  rw [hval, hval']
  exact (jce_sharedPrimalEdge_inj hfg hfg').mpr hshared

theorem fci_sharedEdgeMap_surjective : Function.Surjective fci_sharedEdgeMap := by
  intro e
  obtain ⟨p, q, hval⟩ := fci_sym2_exists e.1
  have hpq : (hypercubicLattice 2).Adj p q :=
    (SimpleGraph.mem_edgeSet _).mp (hval ▸ e.2)
  obtain ⟨f, g, hfg, hshared⟩ := jfc_flankingFaces hpq
  let d : (hypercubicLattice 2).edgeSet :=
    ⟨s(f, g), (SimpleGraph.mem_edgeSet _).mpr hfg⟩
  refine ⟨d, Subtype.ext ?_⟩
  change fci_sharedEdgeRaw s(f, g) = e.1
  rw [fci_sharedEdgeRaw_mk_of_adj hfg, hshared, ← hval]


noncomputable def fci_latticeEdgeEquiv : (hypercubicLattice 2).edgeSet ≃
    (hypercubicLattice 2).edgeSet :=
  Equiv.ofBijective fci_sharedEdgeMap
    ⟨fci_sharedEdgeMap_injective, fci_sharedEdgeMap_surjective⟩


noncomputable def fci_extendLatticeEdgeEquiv
    (e : (hypercubicLattice 2).edgeSet ≃ (hypercubicLattice 2).edgeSet) :
    Sym2 (Site 2) ≃ Sym2 (Site 2) where
  toFun x := if hx : x ∈ (hypercubicLattice 2).edgeSet then (e ⟨x, hx⟩ : Sym2 (Site 2)) else x
  invFun x := if hx : x ∈ (hypercubicLattice 2).edgeSet then (e.symm ⟨x, hx⟩ : Sym2 (Site 2)) else x
  left_inv x := by
    by_cases hx : x ∈ (hypercubicLattice 2).edgeSet
    · simp only [hx, dite_true]
      rw [dif_pos (e ⟨x, hx⟩).2]
      exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
    · change (if _ : (if _ : x ∈ (hypercubicLattice 2).edgeSet then _ else x) ∈
          (hypercubicLattice 2).edgeSet then _ else _) = x
      simp [hx]
  right_inv x := by
    by_cases hx : x ∈ (hypercubicLattice 2).edgeSet
    · simp only [hx, dite_true]
      rw [dif_pos (e.symm ⟨x, hx⟩).2]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
    · change (if _ : (if _ : x ∈ (hypercubicLattice 2).edgeSet then _ else x) ∈
          (hypercubicLattice 2).edgeSet then _ else _) = x
      simp [hx]


noncomputable def fci_faceEdgeEquiv : Sym2 (Site 2) ≃ Sym2 (Site 2) :=
  fci_extendLatticeEdgeEquiv fci_latticeEdgeEquiv

theorem fci_faceEdgeEquiv_mk_of_adj {f g : Site 2}
    (h : (hypercubicLattice 2).Adj f g) :
    fci_faceEdgeEquiv s(f, g) = sharedPrimalEdge f g := by
  change (if _h : s(f, g) ∈ (hypercubicLattice 2).edgeSet then
    (fci_latticeEdgeEquiv ⟨s(f, g), _h⟩ : Sym2 (Site 2)) else s(f, g)) = _
  rw [dif_pos ((SimpleGraph.mem_edgeSet _).mpr h)]
  change fci_sharedEdgeRaw s(f, g) = sharedPrimalEdge f g
  exact fci_sharedEdgeRaw_mk_of_adj h


noncomputable def fci_faceDualConfig (w : ConfigSpace (Sym2 (Site 2))) :
    ConfigSpace (Sym2 (Site 2)) := fun e => !(w (fci_faceEdgeEquiv e))


theorem fci_faceOpenDual_eq_openSubgraph (w : ConfigSpace (Sym2 (Site 2))) :
    fci_faceOpenDual w = openSubgraph 2 (fci_faceDualConfig w) := by
  ext f g
  constructor
  · rintro ⟨h, hclosed⟩
    refine ⟨h, ?_⟩
    rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj h]
    simpa using hclosed
  · rintro ⟨h, hopen⟩
    refine ⟨h, ?_⟩
    rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj h] at hopen
    simpa using hopen


theorem fci_faceDualConfig_measurePreserving :
    MeasurePreserving
      (fci_faceDualConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)))
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) := by
  let reindex := Equiv.piCongrLeft (fun _ => Bool) fci_faceEdgeEquiv.symm
  have hreindex : MeasurePreserving reindex
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) := by
    refine ⟨(MeasurableEquiv.piCongrLeft (fun _ => Bool) fci_faceEdgeEquiv.symm).measurable, ?_⟩
    unfold bernoulliProductMeasure
    exact Measure.infinitePi_map_piCongrLeft
      (fun _ : Sym2 (Site 2) => bernoulliMeasure (2⁻¹ : ℝ≥0) half_le_one)
      fci_faceEdgeEquiv.symm
  have hcompl : MeasurePreserving
      (fun (eta : ConfigSpace (Sym2 (Site 2))) e => !(eta e))
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) := by
    refine ⟨measurable_complement, ?_⟩
    rw [map_complement (2⁻¹ : ℝ≥0) half_le_one]
    congr 1
    exact one_sub_half_eq
  have hcomp := hcompl.comp hreindex
  convert hcomp using 1 <;> funext w e <;>
    simp [fci_faceDualConfig, reindex, Equiv.piCongrLeft_apply]




























theorem fci_square_dichotomy (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    (bcd_leftReach ω n).Finite ∧
      (∀ {v w : Site 2}, v ∈ bcd_leftReach ω n → w ∈ rect 0 n 0 n →
        (hypercubicLattice 2).Adj v w → w ∉ bcd_leftReach ω n →
        (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w)) ∧
      (∃ f g : Site 2, (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g) ∧
      (∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u),
        c.IsCycle ∧ (fci_faceWalk_to_dualWalk (bcd_leftReach ω n) c).IsCycle) := by
  obtain ⟨hfin, hbar, hne, ⟨u, c, hcyc⟩⟩ := fdd_square_dichotomy ω n hn hnoH
  exact ⟨hfin, hbar, hne, u, c, hcyc, fci_faceCycle_to_dualCycle _ c hcyc⟩

end Universality

end StatMech
