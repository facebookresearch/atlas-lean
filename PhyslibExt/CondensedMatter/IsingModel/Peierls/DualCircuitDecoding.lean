/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Peierls.PeierlsAnchorEncode
public import PhyslibExt.CondensedMatter.IsingModel.Peierls.PeierlsEulerParity
public import PhyslibExt.CondensedMatter.IsingModel.Peierls.PeierlsSingleCircuit

/-!
# Dual circuits decode to contours in two dimensions

In `ℤ²`, the primal edges crossed by a dual circuit through every contour edge of a cluster are
exactly its contour, so such circuits encode contours for the Peierls count.

## i. Overview

Each primal edge of `ℤ²` is crossed by exactly one dual edge, between the two faces flanking it
(`flankFaces`), and conversely each dual edge between adjacent faces crosses one primal edge
(`symPrimal`). These maps are mutually inverse on adjacent pairs and carry the edge boundary `∂K`
onto the edge set of the face-boundary graph of `K`. Consequently a closed dual trail through
every edge of the face-boundary graph of a cluster `K ⊆ Λ_n` decodes, edge by edge, to the
contour of `K`, and its length is the contour length. If every realised contour of length `ℓ`
admits such a circuit passing through an axis face `(j, 0)` with `j < ℓ`
(`PeierlsContourCircuitData`), the axis encoding of `PeierlsAnchorEncode` and the Peierls count
follow.

## ii. Key results

- `symPrimal` : the primal edge crossed by the dual edge between two faces.
- `flankFaces` : the two faces flanking a primal edge.
- `symPrimalSym_injOn_edges` : distinct dual contour edges cross distinct primal edges.
- `circuit_decode_eq_contour` : a covering dual circuit decodes to the contour.
- `circuit_length_eq_contourLen` : a covering dual trail has length equal to the contour length.
- `PeierlsContourCircuitData` : covering dual circuits through axis faces for all realised
  contours of length `ℓ`.
- `contourSubsetCountBound_of_circuitData` : such circuits give the bound `ℓ 4^ℓ`.

## iii. Table of contents

- A. Primal and dual edges
- B. Decoding dual circuits
- C. Circuit data and the Peierls count

## iv. References

- R. Peierls, *On Ising's model of ferromagnetism*, Proc. Cambridge Philos. Soc. 32 (1936)
  477–481.
- R. B. Griffiths, *Peierls proof of spontaneous magnetization in a two-dimensional Ising
  ferromagnet*, Phys. Rev. 136 (1964) A437–A439.
- S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems*, Cambridge University
  Press (2017), Section 3.7.2.
-/

@[expose] public section

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch)

attribute [local instance] Classical.propDecidable

/-! ## A. Primal and dual edges -/

/-- The primal edge of `ℤ²` crossed by the dual edge between the faces `f` and `g`, defined
symmetrically in `f` and `g`. See also `sharedPrimalEdge`, with which it agrees on adjacent
faces (`symPrimal_eq_shared`). -/
noncomputable def symPrimal (f g : Site 2) : Sym2 (Site 2) := by
  classical
  exact if f 0 = g 0 then
    s(![f 0, max (f 1) (g 1)], ![f 0 + 1, max (f 1) (g 1)])
  else
    s(![max (f 0) (g 0), min (f 1) (g 1)], ![max (f 0) (g 0), min (f 1) (g 1) + 1])

lemma symPrimal_comm (f g : Site 2) : symPrimal f g = symPrimal g f := by
  classical
  unfold symPrimal
  by_cases h0 : f 0 = g 0
  · rw [ite_eq_left h0, ite_eq_left h0.symm, h0, max_comm]
  · rw [ite_eq_right h0, ite_eq_right (fun hc => h0 hc.symm), max_comm (f 0), min_comm (f 1)]

lemma symPrimal_eq_shared {f g : Site 2} (h : (hypercubicLattice 2).Adj f g) :
    symPrimal f g = sharedPrimalEdge f g := by
  classical
  unfold symPrimal sharedPrimalEdge
  by_cases h0 : f 0 = g 0
  · rw [ite_eq_left h0, ite_eq_left h0]
  · rw [ite_eq_right h0, ite_eq_right h0]
    have hadj := h
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    have h1 : f 1 = g 1 := by
      by_contra hne
      have hb1 : (f 1 - g 1).natAbs ≥ 1 := by omega
      have hb0 : (f 0 - g 0).natAbs ≥ 1 := by
        rcases Int.natAbs_eq (f 0 - g 0) with he | he <;> omega
      omega
    rw [h1, min_self]

/-- `symPrimal` on unordered pairs of faces. -/
noncomputable def symPrimalSym : Sym2 (Site 2) → Sym2 (Site 2) :=
  Sym2.lift ⟨symPrimal, symPrimal_comm⟩

@[simp] lemma symPrimalSym_mk (f g : Site 2) : symPrimalSym s(f, g) = symPrimal f g := rfl

/-- The two faces of `ℤ²` flanking the primal edge `{p, q}`. -/
noncomputable def flankFaces (p q : Site 2) : Sym2 (Site 2) := by
  classical
  exact if p 0 = q 0 then
    s(![p 0 - 1, min (p 1) (q 1)], ![p 0, min (p 1) (q 1)])
  else
    s(![min (p 0) (q 0), min (p 1) (q 1) - 1], ![min (p 0) (q 0), min (p 1) (q 1)])

lemma flankFaces_comm (p q : Site 2) : flankFaces p q = flankFaces q p := by
  classical
  unfold flankFaces
  by_cases h0 : p 0 = q 0
  · rw [ite_eq_left h0, ite_eq_left h0.symm, h0, min_comm]
  · rw [ite_eq_right h0, ite_eq_right (fun hc => h0 hc.symm), min_comm (p 0), min_comm (p 1)]

/-- `flankFaces` on unordered pairs of sites. -/
noncomputable def flankFacesSym : Sym2 (Site 2) → Sym2 (Site 2) :=
  Sym2.lift ⟨flankFaces, flankFaces_comm⟩

@[simp] lemma flankFacesSym_mk (p q : Site 2) : flankFacesSym s(p, q) = flankFaces p q := rfl

lemma adj_cases {f g : Site 2} (h : (hypercubicLattice 2).Adj f g) :
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

lemma cons_eq_site {f : Site 2} {a b : ℤ} (ha : a = f 0) (hb : b = f 1) : ![a, b] = f := by
  subst ha hb; funext i; fin_cases i <;> simp

lemma flankFacesSym_symPrimal {f g : Site 2} (h : (hypercubicLattice 2).Adj f g) :
    flankFacesSym (symPrimal f g) = s(f, g) := by
  classical
  rcases adj_cases h with ⟨h0, hy⟩ | ⟨h1, hx⟩
  · have hsp : symPrimal f g = s(![f 0, max (f 1) (g 1)], ![f 0 + 1, max (f 1) (g 1)]) := by
      unfold symPrimal; rw [ite_eq_left h0]
    rw [hsp, flankFacesSym_mk]
    unfold flankFaces
    rw [ite_eq_right (by simp only [Matrix.cons_val_zero]; omega)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show min (f 0) (f 0 + 1) = f 0 by omega, min_self]
    rcases hy with hfg | hgf
    · rw [show max (f 1) (g 1) = f 1 by omega, show f 1 - 1 = g 1 by omega, Sym2.eq_swap]
      rw [cons_eq_site rfl rfl, cons_eq_site h0 (by omega)]
    · rw [show max (f 1) (g 1) = g 1 by omega, show g 1 - 1 = f 1 by omega]
      rw [cons_eq_site rfl rfl, cons_eq_site h0 rfl]
  · have hsp : symPrimal f g
        = s(![max (f 0) (g 0), min (f 1) (g 1)], ![max (f 0) (g 0), min (f 1) (g 1) + 1]) := by
      unfold symPrimal; rw [ite_eq_right (by rw [h1] at *; intro hc; omega)]
    rw [hsp, flankFacesSym_mk]
    unfold flankFaces
    rw [ite_eq_left (by simp only [Matrix.cons_val_zero])]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show min (min (f 1) (g 1)) (min (f 1) (g 1) + 1) = min (f 1) (g 1) by omega, h1, min_self]
    rcases hx with hfg | hgf
    · rw [show max (f 0) (g 0) = f 0 by omega, show f 0 - 1 = g 0 by omega, Sym2.eq_swap]
      rw [cons_eq_site rfl h1.symm, cons_eq_site rfl rfl]
    · rw [show max (f 0) (g 0) = g 0 by omega, show g 0 - 1 = f 0 by omega]
      rw [cons_eq_site rfl h1.symm, cons_eq_site rfl rfl]

lemma symPrimalSym_flankFaces {p q : Site 2} (h : (hypercubicLattice 2).Adj p q) :
    symPrimalSym (flankFaces p q) = s(p, q) := by
  classical
  rcases adj_cases h with ⟨h0, hy⟩ | ⟨h1, hx⟩
  · have hfl : flankFaces p q = s(![p 0 - 1, min (p 1) (q 1)], ![p 0, min (p 1) (q 1)]) := by
      unfold flankFaces; rw [ite_eq_left h0]
    rw [hfl, symPrimalSym_mk]; unfold symPrimal
    rw [ite_eq_right (by simp only [Matrix.cons_val_zero]; omega)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show max (p 0 - 1) (p 0) = p 0 by omega, min_self]
    rcases hy with hpq | hqp
    · rw [show min (p 1) (q 1) = q 1 by omega, show q 1 + 1 = p 1 by omega, Sym2.eq_swap]
      rw [cons_eq_site rfl rfl, cons_eq_site h0 rfl]
    · rw [show min (p 1) (q 1) = p 1 by omega, show p 1 + 1 = q 1 by omega]
      rw [cons_eq_site rfl rfl, cons_eq_site h0 rfl]
  · have hfl : flankFaces p q
        = s(![min (p 0) (q 0), min (p 1) (q 1) - 1], ![min (p 0) (q 0), min (p 1) (q 1)]) := by
      unfold flankFaces; rw [ite_eq_right (by rw [h1] at *; intro hc; omega)]
    rw [hfl, symPrimalSym_mk]; unfold symPrimal
    rw [ite_eq_left (by simp only [Matrix.cons_val_zero])]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show max (min (p 1) (q 1) - 1) (min (p 1) (q 1)) = min (p 1) (q 1) by omega, h1, min_self]
    rcases hx with hpq | hqp
    · rw [show min (p 0) (q 0) = q 0 by omega, show q 0 + 1 = p 0 by omega, Sym2.eq_swap]
      rw [cons_eq_site rfl h1.symm, cons_eq_site rfl rfl]
    · rw [show min (p 0) (q 0) = p 0 by omega, show p 0 + 1 = q 0 by omega]
      rw [cons_eq_site rfl h1.symm, cons_eq_site rfl rfl]

lemma flankFaces_latAdj {p q : Site 2} (h : (hypercubicLattice 2).Adj p q) :
    ∃ f g : Site 2, flankFaces p q = s(f, g) ∧ (hypercubicLattice 2).Adj f g := by
  classical
  rcases adj_cases h with ⟨h0, _⟩ | ⟨h1, _⟩
  · refine ⟨![p 0 - 1, min (p 1) (q 1)], ![p 0, min (p 1) (q 1)], ?_, ?_⟩
    · unfold flankFaces; rw [ite_eq_left h0]
    · have h2 := (latAdj_left (p 0) (min (p 1) (q 1))).symm
      convert h2 using 2
  · refine ⟨![min (p 0) (q 0), min (p 1) (q 1) - 1], ![min (p 0) (q 0), min (p 1) (q 1)], ?_, ?_⟩
    · unfold flankFaces; rw [ite_eq_right (by rw [h1] at *; intro hc; omega)]
    · have h2 := (latAdj_bottom (min (p 0) (q 0)) (min (p 1) (q 1))).symm
      convert h2 using 2

lemma flankFacesSym_mem_edgeSet {K : Set (Site 2)} {e : Sym2 (Site 2)}
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

lemma symPrimalSym_mem_boundaryEdgeSet {K : Set (Site 2)} {e : Sym2 (Site 2)}
    (he : e ∈ (faceBoundaryGraph K).edgeSet) : symPrimalSym e ∈ boundaryEdgeSet K := by
  classical
  induction e with
  | h f g =>
    rw [SimpleGraph.mem_edgeSet] at he
    rw [symPrimalSym_mk, symPrimal_eq_shared he.1]
    rw [faceBoundaryGraph_adj_iff_boundaryEdgeSet] at he
    exact he.2

lemma symPrimalSym_injOn_edges (K : Set (Site 2)) :
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

/-! ## B. Decoding dual circuits -/

/-- The set of primal edges crossed by a closed dual walk. -/
noncomputable def dualWalkContour (W : Σ v : Site 2, (hypercubicLattice 2).Walk v v) :
    Finset (Sym2 (Site 2)) :=
  (W.2.edges.map symPrimalSym).toFinset

lemma circuit_image_eq_crossEdges {K : Finset (Site 2)} {n : ℕ}
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

lemma circuit_decode_eq_contour {K : Finset (Site 2)} {n : ℕ}
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

lemma circuit_length_eq_contourLen {K : Finset (Site 2)} {n : ℕ}
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

/-! ## C. Circuit data and the Peierls count -/

/-- Every realised contour of length `ℓ` in `Λ_n ⊆ ℤ²` is the contour of a finite cluster whose
face-boundary graph is connected on `boundarySupport` and meets an axis face `(j, 0)` with `j <
ℓ`. The condition refers to the face set `boundarySupport`, which is chosen by
`Classical.choose`. -/
def PeierlsContourCircuitData (n ℓ : ℕ) : Prop :=
  ∀ F ∈ realisedContours 2 n ℓ,
    ∃ K : Finset (Site 2), (↑K : Set (Site 2)) ⊆ box 2 n ∧
      crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = F ∧
      contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ ∧
      ∃ hfin : (↑K : Set (Site 2)).Finite,
        FaceBoundaryConnected (↑K : Set (Site 2)) (boundarySupport hfin) ∧
        ∃ j : ℕ, j < ℓ ∧ axisVertex 2 j ∈ (boundarySupport hfin : Set (Site 2))

lemma axisContourDualCircuit_of_circuitData {n ℓ : ℕ}
    (h : PeierlsContourCircuitData n ℓ) : AxisContourDualCircuit 2 n ℓ := by
  classical
  refine ⟨dualWalkContour, ?_⟩
  intro F hF
  obtain ⟨K, hKbox, hKcross, hKlen, hfin, hconn, j, hj, haxis⟩ := h F hF
  obtain ⟨c, htrail, hcov⟩ := exists_single_dualCircuit_of_connected hfin hconn haxis
  refine ⟨j, hj, c.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2))), ?_, ?_⟩
  · rw [circuit_length_eq_contourLen hKbox c htrail hcov, hKlen]
  · rw [circuit_decode_eq_contour hKbox c hcov, hKcross]

lemma realisedContourWalkEncoding_of_circuitData {n ℓ : ℕ}
    (h : PeierlsContourCircuitData n ℓ) : RealisedContourWalkEncoding 2 n ℓ :=
  realisedContourWalkEncoding_of_axisCircuit (axisContourDualCircuit_of_circuitData h)

lemma contourSubsetCountBound_of_circuitData {n ℓ : ℕ}
    (h : PeierlsContourCircuitData n ℓ) : ContourSubsetCountBound 2 n ℓ :=
  contourSubsetCountBound_of_walkEncoding (realisedContourWalkEncoding_of_circuitData h)

lemma connFamily_fixedLen_card_le_peierls_of_circuitData {n ℓ : ℕ}
    (h : PeierlsContourCircuitData n ℓ) :
    ((connClusterFamily (d := 2) n).filter
        (fun K : Finset (Site 2) => contourLen (↑K) (bondFinsetTouch 2 n) = ℓ)).card
      ≤ ℓ * (2 * 2) ^ ℓ :=
  connFamily_fixedLen_card_le_peierls n ℓ (contourSubsetCountBound_of_circuitData h)

lemma realisedContour_has_cluster {n ℓ : ℕ} {F : Finset (Sym2 (Site 2))}
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

/-- Every connected cluster in `Λ_n ⊆ ℤ²` with contour length `ℓ` is finite, has face-boundary graph
connected on `boundarySupport`, and meets an axis face `(j, 0)` with `j < ℓ`. The condition
refers to the face set `boundarySupport`, which is chosen by `Classical.choose`;
`TightAxisCircuitData` avoids this choice. -/
def ContourGeometryResidue (n ℓ : ℕ) : Prop :=
  ∀ K : Finset (Site 2), K ∈ connClusterFamily (d := 2) n →
    contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ →
    ∃ hfin : (↑K : Set (Site 2)).Finite,
      FaceBoundaryConnected (↑K : Set (Site 2)) (boundarySupport hfin) ∧
      ∃ j : ℕ, j < ℓ ∧ axisVertex 2 j ∈ (boundarySupport hfin : Set (Site 2))

lemma peierlsContourCircuitData_of_geometryResidue {n ℓ : ℕ}
    (h : ContourGeometryResidue n ℓ) : PeierlsContourCircuitData n ℓ := by
  intro F hF
  obtain ⟨K, hKconn, hKbox, hKcross, hKlen⟩ := realisedContour_has_cluster hF
  obtain ⟨hfin, hconn, j, hj, haxis⟩ := h K hKconn hKlen
  exact ⟨K, hKbox, hKcross, hKlen, hfin, hconn, j, hj, haxis⟩

lemma axisContourDualCircuit_of_geometryResidue {n ℓ : ℕ}
    (h : ContourGeometryResidue n ℓ) : AxisContourDualCircuit 2 n ℓ :=
  axisContourDualCircuit_of_circuitData (peierlsContourCircuitData_of_geometryResidue h)

lemma contourSubsetCountBound_of_geometryResidue {n ℓ : ℕ}
    (h : ContourGeometryResidue n ℓ) : ContourSubsetCountBound 2 n ℓ :=
  contourSubsetCountBound_of_circuitData (peierlsContourCircuitData_of_geometryResidue h)

lemma connFamily_fixedLen_card_le_peierls_of_geometryResidue {n ℓ : ℕ}
    (h : ContourGeometryResidue n ℓ) :
    ((connClusterFamily (d := 2) n).filter
        (fun K : Finset (Site 2) => contourLen (↑K) (bondFinsetTouch 2 n) = ℓ)).card
      ≤ ℓ * (2 * 2) ^ ℓ :=
  connFamily_fixedLen_card_le_peierls_of_circuitData
    (peierlsContourCircuitData_of_geometryResidue h)

lemma peierlsContourCircuitData_of_empty {n ℓ : ℕ}
    (hempty : realisedContours 2 n ℓ = ∅) : PeierlsContourCircuitData n ℓ := by
  intro F hF
  rw [hempty] at hF
  simp at hF

lemma contourGeometryResidue_of_no_cluster {n ℓ : ℕ}
    (hempty : ∀ K : Finset (Site 2), K ∈ connClusterFamily (d := 2) n →
      contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) ≠ ℓ) :
    ContourGeometryResidue n ℓ := by
  intro K hK hlen
  exact absurd hlen (hempty K hK)

lemma contourSubsetCountBound_of_empty_circuitData {n ℓ : ℕ}
    (hempty : realisedContours 2 n ℓ = ∅) : ContourSubsetCountBound 2 n ℓ :=
  contourSubsetCountBound_of_circuitData (peierlsContourCircuitData_of_empty hempty)

lemma peierls_long_range_order_of_geometryResidue
    (h : ∀ (n ℓ : ℕ), ContourGeometryResidue n ℓ) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      StatMech.Ising.plusMeasure 2 n β 0 ≠ StatMech.Ising.minusMeasure 2 n β 0 :=
  peierls_long_range_order_of_walkEncoding (by norm_num)
    (fun n ℓ => realisedContourWalkEncoding_of_circuitData
      (peierlsContourCircuitData_of_geometryResidue (h n ℓ)))

end Lattice

end StatMech
