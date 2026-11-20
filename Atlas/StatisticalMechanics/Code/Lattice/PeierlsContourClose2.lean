/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Mathlib
import Code.Lattice.PeierlsSingleCircuit
import Code.Lattice.PeierlsAnchorEncode
import Code.Lattice.PeierlsEulerParity

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch)

attribute [local instance] Classical.propDecidable










noncomputable def symPrimal (f g : Site 2) : Sym2 (Site 2) := by
  classical
  exact if f 0 = g 0 then
    s(![f 0, max (f 1) (g 1)], ![f 0 + 1, max (f 1) (g 1)])
  else
    s(![max (f 0) (g 0), min (f 1) (g 1)], ![max (f 0) (g 0), min (f 1) (g 1) + 1])


theorem symPrimal_comm (f g : Site 2) : symPrimal f g = symPrimal g f := by
  classical
  unfold symPrimal
  by_cases h0 : f 0 = g 0
  · rw [if_pos h0, if_pos h0.symm, h0, max_comm]
  · rw [if_neg h0, if_neg (fun hc => h0 hc.symm), max_comm (f 0), min_comm (f 1)]



theorem symPrimal_eq_shared {f g : Site 2} (h : (hypercubicLattice 2).Adj f g) :
    symPrimal f g = sharedPrimalEdge f g := by
  classical
  unfold symPrimal sharedPrimalEdge
  by_cases h0 : f 0 = g 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    have hadj := h
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    have h1 : f 1 = g 1 := by
      by_contra hne
      have hb1 : (f 1 - g 1).natAbs ≥ 1 := by omega
      have hb0 : (f 0 - g 0).natAbs ≥ 1 := by
        rcases Int.natAbs_eq (f 0 - g 0) with he | he <;> omega
      omega
    rw [h1, min_self]


noncomputable def symPrimalSym : Sym2 (Site 2) → Sym2 (Site 2) :=
  Sym2.lift ⟨symPrimal, symPrimal_comm⟩

@[simp] theorem symPrimalSym_mk (f g : Site 2) : symPrimalSym s(f, g) = symPrimal f g := rfl




noncomputable def flankFaces (p q : Site 2) : Sym2 (Site 2) := by
  classical
  exact if p 0 = q 0 then
    s(![p 0 - 1, min (p 1) (q 1)], ![p 0, min (p 1) (q 1)])
  else
    s(![min (p 0) (q 0), min (p 1) (q 1) - 1], ![min (p 0) (q 0), min (p 1) (q 1)])


theorem flankFaces_comm (p q : Site 2) : flankFaces p q = flankFaces q p := by
  classical
  unfold flankFaces
  by_cases h0 : p 0 = q 0
  · rw [if_pos h0, if_pos h0.symm, h0, min_comm]
  · rw [if_neg h0, if_neg (fun hc => h0 hc.symm), min_comm (p 0), min_comm (p 1)]


noncomputable def flankFacesSym : Sym2 (Site 2) → Sym2 (Site 2) :=
  Sym2.lift ⟨flankFaces, flankFaces_comm⟩

@[simp] theorem flankFacesSym_mk (p q : Site 2) : flankFacesSym s(p, q) = flankFaces p q := rfl



theorem adj_cases {f g : Site 2} (h : (hypercubicLattice 2).Adj f g) :
    (f 0 = g 0 ∧ (f 1 = g 1 + 1 ∨ g 1 = f 1 + 1)) ∨
    (f 1 = g 1 ∧ (f 0 = g 0 + 1 ∨ g 0 = f 0 + 1)) := by
  have hadj := h
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  by_cases h0 : f 0 = g 0
  · left; refine ⟨h0, ?_⟩
    have : (f 1 - g 1).natAbs = 1 := by omega
    rcases Int.natAbs_eq_iff.mp this with he | he <;> omega
  · right
    have h1 : f 1 = g 1 := by
      by_contra hne
      have hb1 : (f 1 - g 1).natAbs ≥ 1 := by omega
      have hb0 : (f 0 - g 0).natAbs ≥ 1 := by
        rcases Int.natAbs_eq (f 0 - g 0) with he | he <;> omega
      omega
    refine ⟨h1, ?_⟩
    have : (f 0 - g 0).natAbs = 1 := by omega
    rcases Int.natAbs_eq_iff.mp this with he | he <;> omega


theorem cons_eq_site {f : Site 2} {a b : ℤ} (ha : a = f 0) (hb : b = f 1) : ![a, b] = f := by
  subst ha hb; funext i; fin_cases i <;> simp




theorem flankFacesSym_symPrimal {f g : Site 2} (h : (hypercubicLattice 2).Adj f g) :
    flankFacesSym (symPrimal f g) = s(f, g) := by
  classical
  rcases adj_cases h with ⟨h0, hy⟩ | ⟨h1, hx⟩
  · have hsp : symPrimal f g = s(![f 0, max (f 1) (g 1)], ![f 0 + 1, max (f 1) (g 1)]) := by
      unfold symPrimal; rw [if_pos h0]
    rw [hsp, flankFacesSym_mk]
    unfold flankFaces
    rw [if_neg (by simp only [Matrix.cons_val_zero]; omega)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show min (f 0) (f 0 + 1) = f 0 by omega, min_self]
    rcases hy with hfg | hgf
    · rw [show max (f 1) (g 1) = f 1 by omega, show f 1 - 1 = g 1 by omega, Sym2.eq_swap]
      rw [cons_eq_site rfl rfl, cons_eq_site h0 (by omega)]
    · rw [show max (f 1) (g 1) = g 1 by omega, show g 1 - 1 = f 1 by omega]
      rw [cons_eq_site rfl rfl, cons_eq_site h0 rfl]
  · have hsp : symPrimal f g
        = s(![max (f 0) (g 0), min (f 1) (g 1)], ![max (f 0) (g 0), min (f 1) (g 1) + 1]) := by
      unfold symPrimal; rw [if_neg (by rw [h1] at *; intro hc; omega)]
    rw [hsp, flankFacesSym_mk]
    unfold flankFaces
    rw [if_pos (by simp only [Matrix.cons_val_zero])]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show min (min (f 1) (g 1)) (min (f 1) (g 1) + 1) = min (f 1) (g 1) by omega, h1, min_self]
    rcases hx with hfg | hgf
    · rw [show max (f 0) (g 0) = f 0 by omega, show f 0 - 1 = g 0 by omega, Sym2.eq_swap]
      rw [cons_eq_site rfl h1.symm, cons_eq_site rfl rfl]
    · rw [show max (f 0) (g 0) = g 0 by omega, show g 0 - 1 = f 0 by omega]
      rw [cons_eq_site rfl h1.symm, cons_eq_site rfl rfl]




theorem symPrimalSym_flankFaces {p q : Site 2} (h : (hypercubicLattice 2).Adj p q) :
    symPrimalSym (flankFaces p q) = s(p, q) := by
  classical
  rcases adj_cases h with ⟨h0, hy⟩ | ⟨h1, hx⟩
  · have hfl : flankFaces p q = s(![p 0 - 1, min (p 1) (q 1)], ![p 0, min (p 1) (q 1)]) := by
      unfold flankFaces; rw [if_pos h0]
    rw [hfl, symPrimalSym_mk]; unfold symPrimal
    rw [if_neg (by simp only [Matrix.cons_val_zero]; omega)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show max (p 0 - 1) (p 0) = p 0 by omega, min_self]
    rcases hy with hpq | hqp
    · rw [show min (p 1) (q 1) = q 1 by omega, show q 1 + 1 = p 1 by omega, Sym2.eq_swap]
      rw [cons_eq_site rfl rfl, cons_eq_site h0 rfl]
    · rw [show min (p 1) (q 1) = p 1 by omega, show p 1 + 1 = q 1 by omega]
      rw [cons_eq_site rfl rfl, cons_eq_site h0 rfl]
  · have hfl : flankFaces p q
        = s(![min (p 0) (q 0), min (p 1) (q 1) - 1], ![min (p 0) (q 0), min (p 1) (q 1)]) := by
      unfold flankFaces; rw [if_neg (by rw [h1] at *; intro hc; omega)]
    rw [hfl, symPrimalSym_mk]; unfold symPrimal
    rw [if_pos (by simp only [Matrix.cons_val_zero])]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show max (min (p 1) (q 1) - 1) (min (p 1) (q 1)) = min (p 1) (q 1) by omega, h1, min_self]
    rcases hx with hpq | hqp
    · rw [show min (p 0) (q 0) = q 0 by omega, show q 0 + 1 = p 0 by omega, Sym2.eq_swap]
      rw [cons_eq_site rfl h1.symm, cons_eq_site rfl rfl]
    · rw [show min (p 0) (q 0) = p 0 by omega, show p 0 + 1 = q 0 by omega]
      rw [cons_eq_site rfl h1.symm, cons_eq_site rfl rfl]



theorem flankFaces_latAdj {p q : Site 2} (h : (hypercubicLattice 2).Adj p q) :
    ∃ f g : Site 2, flankFaces p q = s(f, g) ∧ (hypercubicLattice 2).Adj f g := by
  classical
  rcases adj_cases h with ⟨h0, _⟩ | ⟨h1, _⟩
  · refine ⟨![p 0 - 1, min (p 1) (q 1)], ![p 0, min (p 1) (q 1)], ?_, ?_⟩
    · unfold flankFaces; rw [if_pos h0]
    · have h2 := (latAdj_left (p 0) (min (p 1) (q 1))).symm
      convert h2 using 2
  · refine ⟨![min (p 0) (q 0), min (p 1) (q 1) - 1], ![min (p 0) (q 0), min (p 1) (q 1)], ?_, ?_⟩
    · unfold flankFaces; rw [if_neg (by rw [h1] at *; intro hc; omega)]
    · have h2 := (latAdj_bottom (min (p 0) (q 0)) (min (p 1) (q 1))).symm
      convert h2 using 2





theorem flankFacesSym_mem_edgeSet {K : Set (Site 2)} {e : Sym2 (Site 2)}
    (he : e ∈ boundaryEdgeSet K) :
    flankFacesSym e ∈ (faceBoundaryGraph K).edgeSet ∧ symPrimalSym (flankFacesSym e) = e := by
  classical
  obtain ⟨hedge, hstr⟩ := he
  induction e with
  | h p q =>
    rw [SimpleGraph.mem_edgeSet] at hedge
    obtain ⟨f, g, hfg, hfgadj⟩ := flankFaces_latAdj hedge
    rw [flankFacesSym_mk]
    have hsps : symPrimalSym (flankFaces p q) = s(p, q) := symPrimalSym_flankFaces hedge
    refine ⟨?_, hsps⟩
    rw [hfg, SimpleGraph.mem_edgeSet, faceBoundaryGraph_adj_iff_boundaryEdgeSet]
    refine ⟨hfgadj, ?_⟩
    
    have : sharedPrimalEdge f g = s(p, q) := by
      rw [← symPrimal_eq_shared hfgadj, ← symPrimalSym_mk, ← hfg, hsps]
    rw [this]
    exact ⟨hedge, hstr⟩



theorem symPrimalSym_mem_boundaryEdgeSet {K : Set (Site 2)} {e : Sym2 (Site 2)}
    (he : e ∈ (faceBoundaryGraph K).edgeSet) : symPrimalSym e ∈ boundaryEdgeSet K := by
  classical
  induction e with
  | h f g =>
    rw [SimpleGraph.mem_edgeSet] at he
    rw [symPrimalSym_mk, symPrimal_eq_shared he.1]
    rw [faceBoundaryGraph_adj_iff_boundaryEdgeSet] at he
    exact he.2




theorem symPrimalSym_injOn_edges (K : Set (Site 2)) :
    Set.InjOn symPrimalSym ((faceBoundaryGraph K).edgeSet) := by
  intro e1 he1 e2 he2 heq
  induction e1 with
  | h f1 g1 => induction e2 with
    | h f2 g2 =>
      rw [SimpleGraph.mem_edgeSet] at he1 he2
      have hl1 : flankFacesSym (symPrimal f1 g1) = s(f1, g1) := flankFacesSym_symPrimal he1.1
      have hl2 : flankFacesSym (symPrimal f2 g2) = s(f2, g2) := flankFacesSym_symPrimal he2.1
      rw [symPrimalSym_mk, symPrimalSym_mk] at heq
      rw [← hl1, ← hl2, heq]










noncomputable def dualWalkContour (W : Σ v : Site 2, (hypercubicLattice 2).Walk v v) :
    Finset (Sym2 (Site 2)) :=
  (W.2.edges.map symPrimalSym).toFinset






theorem circuit_image_eq_crossEdges {K : Finset (Site 2)} {n : ℕ}
    (hKbox : (↑K : Set (Site 2)) ⊆ box 2 n) {u : Site 2}
    (c : (faceBoundaryGraph (↑K : Set (Site 2))).Walk u u)
    (hcov : ∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet, e ∈ c.edges) :
    Finset.image symPrimalSym c.edges.toFinset
      = crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n) := by
  classical
  apply Finset.ext
  intro pe
  rw [Finset.mem_image, ← Finset.mem_coe, coe_crossEdges_eq_boundaryEdgeSet hKbox]
  constructor
  · rintro ⟨de, hde, rfl⟩
    rw [List.mem_toFinset] at hde
    exact symPrimalSym_mem_boundaryEdgeSet (c.edges_subset_edgeSet hde)
  · intro hpe
    obtain ⟨hedgemem, hsps⟩ := flankFacesSym_mem_edgeSet hpe
    exact ⟨flankFacesSym pe, by rw [List.mem_toFinset]; exact hcov _ hedgemem, hsps⟩





theorem circuit_decode_eq_contour {K : Finset (Site 2)} {n : ℕ}
    (hKbox : (↑K : Set (Site 2)) ⊆ box 2 n) {u : Site 2}
    (c : (faceBoundaryGraph (↑K : Set (Site 2))).Walk u u)
    (hcov : ∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet, e ∈ c.edges) :
    dualWalkContour ⟨u, c.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2)))⟩
      = crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n) := by
  classical
  unfold dualWalkContour
  simp only
  rw [(c.edges_mapLe_eq_edges (faceBoundaryGraph_le (↑K : Set (Site 2))))]
  rw [show (c.edges.map symPrimalSym).toFinset = Finset.image symPrimalSym c.edges.toFinset by
    ext x; simp [List.mem_toFinset, List.mem_map]]
  exact circuit_image_eq_crossEdges hKbox c hcov





theorem circuit_length_eq_contourLen {K : Finset (Site 2)} {n : ℕ}
    (hKbox : (↑K : Set (Site 2)) ⊆ box 2 n) {u : Site 2}
    (c : (faceBoundaryGraph (↑K : Set (Site 2))).Walk u u) (htrail : c.IsTrail)
    (hcov : ∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet, e ∈ c.edges) :
    (c.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2)))).length
      = contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) := by
  classical
  
  have hml : (c.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2)))).length = c.length := by
    unfold SimpleGraph.Walk.mapLe
    exact SimpleGraph.Walk.length_map (Hom.ofLE _) c
  rw [hml]
  
  rw [← SimpleGraph.Walk.length_edges, ← List.toFinset_card_of_nodup htrail.edges_nodup]
  
  rw [StatMech.Ising.contourLen, ← circuit_image_eq_crossEdges hKbox c hcov]
  symm
  apply Finset.card_image_of_injOn
  
  refine (symPrimalSym_injOn_edges (↑K : Set (Site 2))).mono ?_
  intro e he
  rw [Finset.mem_coe, List.mem_toFinset] at he
  exact c.edges_subset_edgeSet he






















def PeierlsContourCircuitData (n ℓ : ℕ) : Prop :=
  ∀ F ∈ realisedContours 2 n ℓ,
    ∃ K : Finset (Site 2), (↑K : Set (Site 2)) ⊆ box 2 n ∧
      crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = F ∧
      contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ ∧
      ∃ hfin : (↑K : Set (Site 2)).Finite,
        FaceBoundaryConnected (↑K : Set (Site 2)) (boundarySupport hfin) ∧
        ∃ j : ℕ, j < ℓ ∧ axisVertex 2 j ∈ (boundarySupport hfin : Set (Site 2))






theorem axisContourDualCircuit_of_circuitData {n ℓ : ℕ}
    (h : PeierlsContourCircuitData n ℓ) : AxisContourDualCircuit 2 n ℓ := by
  classical
  refine ⟨dualWalkContour, ?_⟩
  intro F hF
  obtain ⟨K, hKbox, hKcross, hKlen, hfin, hconn, j, hj, haxis⟩ := h F hF
  obtain ⟨c, htrail, hcov⟩ := exists_single_dualCircuit_of_connected hfin hconn haxis
  refine ⟨j, hj, c.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2))), ?_, ?_⟩
  · rw [circuit_length_eq_contourLen hKbox c htrail hcov, hKlen]
  · rw [circuit_decode_eq_contour hKbox c hcov, hKcross]





theorem realisedContourWalkEncoding_of_circuitData {n ℓ : ℕ}
    (h : PeierlsContourCircuitData n ℓ) : RealisedContourWalkEncoding 2 n ℓ :=
  realisedContourWalkEncoding_of_axisCircuit (axisContourDualCircuit_of_circuitData h)






theorem contourSubsetCountBound_of_circuitData {n ℓ : ℕ}
    (h : PeierlsContourCircuitData n ℓ) : ContourSubsetCountBound 2 n ℓ :=
  contourSubsetCountBound_of_walkEncoding (realisedContourWalkEncoding_of_circuitData h)





theorem connFamily_fixedLen_card_le_peierls_of_circuitData {n ℓ : ℕ}
    (h : PeierlsContourCircuitData n ℓ) :
    ((connClusterFamily (d := 2) n).filter
        (fun K : Finset (Site 2) => contourLen (↑K) (bondFinsetTouch 2 n) = ℓ)).card
      ≤ ℓ * (2 * 2) ^ ℓ :=
  connFamily_fixedLen_card_le_peierls n ℓ (contourSubsetCountBound_of_circuitData h)
















theorem realisedContour_has_cluster {n ℓ : ℕ} {F : Finset (Sym2 (Site 2))}
    (hF : F ∈ realisedContours 2 n ℓ) :
    ∃ K : Finset (Site 2), K ∈ connClusterFamily (d := 2) n ∧
      (↑K : Set (Site 2)) ⊆ box 2 n ∧
      crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = F ∧
      contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ := by
  classical
  unfold realisedContours at hF
  rw [Finset.mem_image] at hF
  obtain ⟨K, hKmem, hKeq⟩ := hF
  rw [Finset.mem_filter, StatMech.Ising.pcc_mem_connClusterFamily] at hKmem
  exact ⟨K, StatMech.Ising.pcc_mem_connClusterFamily.mpr hKmem.1,
    StatMech.Ising.clusterFamily_subset_box hKmem.1.1, hKeq, hKmem.2⟩








def ContourGeometryResidue (n ℓ : ℕ) : Prop :=
  ∀ K : Finset (Site 2), K ∈ connClusterFamily (d := 2) n →
    contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ →
    ∃ hfin : (↑K : Set (Site 2)).Finite,
      FaceBoundaryConnected (↑K : Set (Site 2)) (boundarySupport hfin) ∧
      ∃ j : ℕ, j < ℓ ∧ axisVertex 2 j ∈ (boundarySupport hfin : Set (Site 2))



theorem peierlsContourCircuitData_of_geometryResidue {n ℓ : ℕ}
    (h : ContourGeometryResidue n ℓ) : PeierlsContourCircuitData n ℓ := by
  intro F hF
  obtain ⟨K, hKconn, hKbox, hKcross, hKlen⟩ := realisedContour_has_cluster hF
  obtain ⟨hfin, hconn, j, hj, haxis⟩ := h K hKconn hKlen
  exact ⟨K, hKbox, hKcross, hKlen, hfin, hconn, j, hj, haxis⟩




theorem axisContourDualCircuit_of_geometryResidue {n ℓ : ℕ}
    (h : ContourGeometryResidue n ℓ) : AxisContourDualCircuit 2 n ℓ :=
  axisContourDualCircuit_of_circuitData (peierlsContourCircuitData_of_geometryResidue h)




theorem contourSubsetCountBound_of_geometryResidue {n ℓ : ℕ}
    (h : ContourGeometryResidue n ℓ) : ContourSubsetCountBound 2 n ℓ :=
  contourSubsetCountBound_of_circuitData (peierlsContourCircuitData_of_geometryResidue h)



theorem connFamily_fixedLen_card_le_peierls_of_geometryResidue {n ℓ : ℕ}
    (h : ContourGeometryResidue n ℓ) :
    ((connClusterFamily (d := 2) n).filter
        (fun K : Finset (Site 2) => contourLen (↑K) (bondFinsetTouch 2 n) = ℓ)).card
      ≤ ℓ * (2 * 2) ^ ℓ :=
  connFamily_fixedLen_card_le_peierls_of_circuitData
    (peierlsContourCircuitData_of_geometryResidue h)











theorem peierlsContourCircuitData_of_empty {n ℓ : ℕ}
    (hempty : realisedContours 2 n ℓ = ∅) : PeierlsContourCircuitData n ℓ := by
  intro F hF
  rw [hempty] at hF
  simp at hF






theorem contourGeometryResidue_of_no_cluster {n ℓ : ℕ}
    (hempty : ∀ K : Finset (Site 2), K ∈ connClusterFamily (d := 2) n →
      contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) ≠ ℓ) :
    ContourGeometryResidue n ℓ := by
  intro K hK hlen
  exact absurd hlen (hempty K hK)




theorem contourSubsetCountBound_of_empty_circuitData {n ℓ : ℕ}
    (hempty : realisedContours 2 n ℓ = ∅) : ContourSubsetCountBound 2 n ℓ :=
  contourSubsetCountBound_of_circuitData (peierlsContourCircuitData_of_empty hempty)

















theorem peierls_long_range_order_of_geometryResidue
    (h : ∀ (n ℓ : ℕ), ContourGeometryResidue n ℓ) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      StatMech.Ising.plusMeasure 2 n β 0 ≠ StatMech.Ising.minusMeasure 2 n β 0 :=
  peierls_long_range_order_of_walkEncoding (by norm_num)
    (fun n ℓ => realisedContourWalkEncoding_of_circuitData
      (peierlsContourCircuitData_of_geometryResidue (h n ℓ)))

end Lattice

end StatMech
