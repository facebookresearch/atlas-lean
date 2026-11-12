/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Peierls.DualCircuitDecoding
public import PhyslibExt.CondensedMatter.IsingModel.Peierls.PeierlsBoundaryConnected

/-!
# Dual circuits through one component of the contour

The connected component of a face in the face-boundary graph has an Euler circuit; if it carries
every contour edge, the contour is a single dual circuit through that face.

## i. Overview

For a face `f`, the component graph keeps the edges of the face-boundary graph of `K` between
faces reachable from `f`. It is locally finite with even degrees and connected on its finite
support, so it has a closed Eulerian trail at `f`. When the component of `f` contains every
contour edge, that trail is a dual circuit through every contour edge of `K`. Requiring this for
an axis face `(j, 0)` with `j < ℓ` (`TightAxisCircuitData`) avoids any choice of face set and
yields the axis encoding, hence the Peierls count. The singleton cluster `{0}` and every
rectangle `[0, m] × [0, n]` satisfy the requirement.

## ii. Key results

- `componentGraph` : the component of a face in the face-boundary graph.
- `componentEulerCircuit` : the component has a closed Eulerian trail at the face.
- `dualCircuit_of_componentCovers` : a component carrying every contour edge gives a dual circuit
  through all of them.
- `TightAxisCircuitData` : covering components at axis faces for all realised contours of
  length `ℓ`.
- `contourSubsetCountBound_of_tightData` : such data give the bound `ℓ 4^ℓ`.
- `boxCluster_tight_dualCircuit` : rectangles have a covering dual circuit through an axis face.

## iii. Table of contents

- A. The component graph of a face
- B. Euler circuits of a component
- C. Tight circuit data and the Peierls count
- D. Examples: the singleton and rectangular clusters

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

open StatMech.Ising (IsConnectedCluster origin latticeOn crossEdges contourLen connClusterFamily
  bondFinsetTouch)

attribute [local instance] Classical.propDecidable

/-! ## A. The component graph of a face -/

/-- The faces of `T` reachable from `f` in the face-boundary graph of `K`. -/
noncomputable def componentSupport (K : Set (Site 2)) (T : Finset (Site 2)) (f : Site 2) :
    Finset (Site 2) :=
  T.filter (fun g => (faceBoundaryGraph K).Reachable f g)

lemma mem_componentSupport {K : Set (Site 2)} {T : Finset (Site 2)} {f g : Site 2} :
    g ∈ componentSupport K T f ↔ g ∈ T ∧ (faceBoundaryGraph K).Reachable f g := by
  unfold componentSupport; rw [Finset.mem_filter]

lemma self_mem_componentSupport {K : Set (Site 2)} {T : Finset (Site 2)} {f : Site 2}
    (hf : f ∈ T) : f ∈ componentSupport K T f := by
  rw [mem_componentSupport]; exact ⟨hf, SimpleGraph.Reachable.refl _⟩

lemma componentSupport_neighbor {K : Set (Site 2)} {T : Finset (Site 2)} {f g h : Site 2}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)))
    (hg : g ∈ componentSupport K T f) (hadj : (faceBoundaryGraph K).Adj g h) :
    h ∈ componentSupport K T f := by
  rw [mem_componentSupport] at hg ⊢
  refine ⟨hsupp hadj.symm.mem_support_left, hg.2.trans hadj.reachable⟩

lemma componentSupport_walk_subset {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2))) {f g : Site 2}
    (hf : f ∈ T) (p : (faceBoundaryGraph K).Walk f g) :
    ∀ v ∈ p.support, v ∈ componentSupport K T f := by
  intro v hv
  rw [mem_componentSupport]
  have hr : (faceBoundaryGraph K).Reachable f v := ⟨p.takeUntil v hv⟩
  refine ⟨?_, hr⟩
  by_cases hvf : v = f
  · rw [hvf]; exact hf
  · have hr' : (faceBoundaryGraph K).Reachable v f := hr.symm
    obtain ⟨q2⟩ := hr'
    cases q2 with
    | nil => exact absurd rfl hvf
    | @cons _ c _ hadj2 _ => exact hsupp hadj2.mem_support_left

/-- The connected component of the face `f` in the face-boundary graph of `K`, as a graph on all
faces. -/
def componentGraph (K : Set (Site 2)) (f : Site 2) : SimpleGraph (Site 2) where
  Adj a b := (faceBoundaryGraph K).Adj a b ∧ (faceBoundaryGraph K).Reachable f a ∧
    (faceBoundaryGraph K).Reachable f b
  symm := by
    refine ⟨?_⟩
    rintro a b ⟨hadj, hra, hrb⟩
    exact ⟨hadj.symm, hrb, hra⟩
  loopless := by
    refine ⟨fun a => ?_⟩
    rintro ⟨hadj, _, _⟩
    exact (faceBoundaryGraph K).irrefl hadj

@[simp] lemma componentGraph_adj (K : Set (Site 2)) (f a b : Site 2) :
    (componentGraph K f).Adj a b ↔ (faceBoundaryGraph K).Adj a b ∧
      (faceBoundaryGraph K).Reachable f a ∧ (faceBoundaryGraph K).Reachable f b :=
  Iff.rfl

lemma componentGraph_le (K : Set (Site 2)) (f : Site 2) :
    componentGraph K f ≤ faceBoundaryGraph K := fun _ _ h => h.1

lemma componentGraph_neighborSet_eq {K : Set (Site 2)} {f a : Site 2}
    (ha : (faceBoundaryGraph K).Reachable f a) :
    (componentGraph K f).neighborSet a = (faceBoundaryGraph K).neighborSet a := by
  ext b
  simp only [SimpleGraph.mem_neighborSet, componentGraph_adj]
  constructor
  · rintro ⟨hadj, _, _⟩; exact hadj
  · intro hadj; exact ⟨hadj, ha, ha.trans hadj.reachable⟩

lemma componentGraph_neighborSet_empty {K : Set (Site 2)} {f a : Site 2}
    (ha : ¬ (faceBoundaryGraph K).Reachable f a) :
    (componentGraph K f).neighborSet a = ∅ := by
  ext b
  simp only [SimpleGraph.mem_neighborSet, componentGraph_adj, Set.mem_empty_iff_false, iff_false]
  rintro ⟨_, hra, _⟩; exact ha hra

/-- The component graph of a face is locally finite. -/
noncomputable instance componentGraph_locallyFinite (K : Set (Site 2)) (f : Site 2) :
    LocallyFinite (componentGraph K f) := by
  classical
  intro a
  by_cases ha : (faceBoundaryGraph K).Reachable f a
  · rw [componentGraph_neighborSet_eq ha]
    exact (instLocallyFiniteFaceBoundaryGraph K a)
  · rw [componentGraph_neighborSet_empty ha]
    exact Set.fintypeEmpty

/-! ## B. Euler circuits of a component -/

lemma componentGraph_degree_even (K : Set (Site 2)) (f a : Site 2) :
    Even ((componentGraph K f).degree a) := by
  classical
  by_cases ha : (faceBoundaryGraph K).Reachable f a
  · rw [← SimpleGraph.card_neighborSet_eq_degree]
    have hcard : Fintype.card ((componentGraph K f).neighborSet a)
        = (faceBoundaryGraph K).degree a := by
      rw [← SimpleGraph.card_neighborSet_eq_degree]
      exact Fintype.card_congr (Set.equivOfEq (componentGraph_neighborSet_eq ha))
    rw [hcard]; exact degree_faceBoundaryGraph_even K a
  · rw [← SimpleGraph.card_neighborSet_eq_degree]
    have hempty : (componentGraph K f).neighborSet a = ∅ := componentGraph_neighborSet_empty ha
    have hcard : Fintype.card ((componentGraph K f).neighborSet a) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun x => (hempty ▸ x.2 : (x : Site 2) ∈ (∅ : Set (Site 2)))⟩
    rw [hcard]; exact Even.zero

lemma componentGraph_support_subset {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2))) (f : Site 2) :
    (componentGraph K f).support ⊆ (componentSupport K T f : Set (Site 2)) := by
  intro a ha
  rw [SimpleGraph.mem_support] at ha
  obtain ⟨b, hadj, hra, _⟩ := ha
  rw [Finset.mem_coe, mem_componentSupport]
  exact ⟨hsupp hadj.mem_support_left, hra⟩

lemma componentGraph_walk_in_componentSupport {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2))) {f : Site 2} (hf : f ∈ T)
    {g : Site 2} (p : (componentGraph K f).Walk f g) :
    ∀ v ∈ p.support, v ∈ componentSupport K T f := by
  intro v hv
  have hmem : v ∈ (p.mapLe (componentGraph_le K f)).support := by
    rw [SimpleGraph.Walk.support_mapLe_eq_support]; exact hv
  exact componentSupport_walk_subset hsupp hf (p.mapLe (componentGraph_le K f)) v hmem

lemma componentGraph_edge_of_walk_from_base {K : Set (Site 2)} {f g : Site 2}
    (q : (faceBoundaryGraph K).Walk f g) {e : Sym2 (Site 2)} (he : e ∈ q.edges) :
    e ∈ (componentGraph K f).edgeSet := by
  induction e with
  | h x y =>
    have hxadj : (faceBoundaryGraph K).Adj x y := q.adj_of_mem_edges he
    have hx : x ∈ q.support := q.fst_mem_support_of_mem_edges he
    have hy : y ∈ q.support := q.snd_mem_support_of_mem_edges he
    have hrx : (faceBoundaryGraph K).Reachable f x := ⟨q.takeUntil x hx⟩
    have hry : (faceBoundaryGraph K).Reachable f y := ⟨q.takeUntil y hy⟩
    rw [SimpleGraph.mem_edgeSet]
    exact ⟨hxadj, hrx, hry⟩

lemma componentGraph_reachable_of_reachable {K : Set (Site 2)} {f g : Site 2}
    (h : (faceBoundaryGraph K).Reachable f g) : (componentGraph K f).Reachable f g := by
  obtain ⟨p⟩ := h
  exact ⟨p.transfer (componentGraph K f)
    (fun e he => componentGraph_edge_of_walk_from_base p he)⟩

lemma componentGraph_support_walk {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2))) {f : Site 2} (hf : f ∈ T)
    {a b : Site 2} (ha : a ∈ componentSupport K T f) (hb : b ∈ componentSupport K T f) :
    ∃ p : (componentGraph K f).Walk a b, ∀ v ∈ p.support, v ∈ componentSupport K T f := by
  rw [mem_componentSupport] at ha hb
  obtain ⟨pa⟩ := componentGraph_reachable_of_reachable ha.2
  obtain ⟨pb⟩ := componentGraph_reachable_of_reachable hb.2
  refine ⟨pa.reverse.append pb, ?_⟩
  intro v hv
  rw [SimpleGraph.Walk.support_append] at hv
  rcases List.mem_append.mp hv with hva | hvb
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hva
    exact componentGraph_walk_in_componentSupport hsupp hf pa v hva
  · exact componentGraph_walk_in_componentSupport hsupp hf pb v (List.mem_of_mem_tail hvb)

lemma componentGraph_induce_connected {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2))) {f : Site 2} (hf : f ∈ T) :
    ((componentGraph K f).induce (componentSupport K T f : Set (Site 2))).Connected := by
  have hself : f ∈ componentSupport K T f := self_mem_componentSupport hf
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨f, hself⟩⟩⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  have ha' : a ∈ componentSupport K T f := Finset.mem_coe.mp ha
  have hb' : b ∈ componentSupport K T f := Finset.mem_coe.mp hb
  obtain ⟨p, hp⟩ := componentGraph_support_walk hsupp hf ha' hb'
  exact ⟨p.induce (componentSupport K T f : Set (Site 2)) hp⟩

lemma componentEulerCircuit {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2))) {f : Site 2} (hf : f ∈ T) :
    ∃ c : (componentGraph K f).Walk f f,
      c.IsTrail ∧ ∀ e ∈ (componentGraph K f).edgeSet, e ∈ c.edges := by
  refine EulerianExistence.exists_closed_eulerian_of_finite_support (componentGraph K f)
    (componentSupport K T f) (componentGraph_support_subset hsupp f)
    (componentGraph_induce_connected hsupp hf) (componentGraph_degree_even K f) ?_
  exact Finset.mem_coe.mpr (self_mem_componentSupport hf)

lemma dualCircuit_of_componentCovers {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2))) {f : Site 2} (hf : f ∈ T)
    (hcov : ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ (componentGraph K f).edgeSet) :
    ∃ c : (faceBoundaryGraph K).Walk f f,
      c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ c.edges := by
  obtain ⟨c, htrail, hccov⟩ := componentEulerCircuit hsupp hf
  refine ⟨c.mapLe (componentGraph_le K f),
    SimpleGraph.Walk.IsTrail.map (Function.injective_id) ?_, ?_⟩
  · exact htrail
  · intro e he
    have hcomp : e ∈ (componentGraph K f).edgeSet := hcov e he
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
    exact hccov e hcomp

/-! ## C. Tight circuit data and the Peierls count -/

/-- Every realised contour of length `ℓ` in `Λ_n ⊆ ℤ²` is the contour of a cluster whose
face-boundary graph has all its edges in the component of an axis face `(j, 0)` with `j < ℓ`. -/
def TightAxisCircuitData (n ℓ : ℕ) : Prop :=
  ∀ F ∈ realisedContours 2 n ℓ,
    ∃ K : Finset (Site 2), (↑K : Set (Site 2)) ⊆ box 2 n ∧
      crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = F ∧
      contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ ∧
      ∃ (T : Finset (Site 2)) (j : ℕ),
        (faceBoundaryGraph (↑K : Set (Site 2))).support ⊆ (T : Set (Site 2)) ∧
        j < ℓ ∧ axisVertex 2 j ∈ T ∧
        (∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet,
          e ∈ (componentGraph (↑K : Set (Site 2)) (axisVertex 2 j)).edgeSet)

lemma axisContourDualCircuit_of_tightData {n ℓ : ℕ}
    (h : TightAxisCircuitData n ℓ) : AxisContourDualCircuit 2 n ℓ := by
  classical
  refine ⟨dualWalkContour, ?_⟩
  intro F hF
  obtain ⟨K, hKbox, hKcross, hKlen, T, j, hsupp, hj, hax, hcov⟩ := h F hF
  obtain ⟨c, htrail, hccov⟩ := dualCircuit_of_componentCovers hsupp hax hcov
  refine ⟨j, hj, c.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2))), ?_, ?_⟩
  · rw [circuit_length_eq_contourLen hKbox c htrail hccov, hKlen]
  · rw [circuit_decode_eq_contour hKbox c hccov, hKcross]

lemma realisedContourWalkEncoding_of_tightData {n ℓ : ℕ}
    (h : TightAxisCircuitData n ℓ) : RealisedContourWalkEncoding 2 n ℓ :=
  realisedContourWalkEncoding_of_axisCircuit (axisContourDualCircuit_of_tightData h)

lemma contourSubsetCountBound_of_tightData {n ℓ : ℕ}
    (h : TightAxisCircuitData n ℓ) : ContourSubsetCountBound 2 n ℓ :=
  contourSubsetCountBound_of_walkEncoding (realisedContourWalkEncoding_of_tightData h)

lemma peierls_long_range_order_of_tightData
    (h : ∀ (n ℓ : ℕ), TightAxisCircuitData n ℓ) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      StatMech.Ising.plusMeasure 2 n β 0 ≠ StatMech.Ising.minusMeasure 2 n β 0 :=
  peierls_long_range_order_of_walkEncoding (by norm_num)
    (fun n ℓ => realisedContourWalkEncoding_of_tightData (h n ℓ))

lemma componentCovers_of_faceBoundaryConnected {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)))
    (hconn : FaceBoundaryConnected K T) {f : Site 2} (hf : f ∈ T) :
    ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ (componentGraph K f).edgeSet := by
  intro e he
  induction e with
  | h x y =>
    rw [SimpleGraph.mem_edgeSet] at he
    have hxT : x ∈ T := Finset.mem_coe.mp (hsupp he.mem_support_left)
    have hyT : y ∈ T := Finset.mem_coe.mp (hsupp he.symm.mem_support_left)
    have hfT : f ∈ T := hf
    have hrI : ((faceBoundaryGraph K).induce (T : Set (Site 2))).Reachable ⟨f, hfT⟩ ⟨x, hxT⟩ :=
      (hconn.preconnected ⟨f, hfT⟩ ⟨x, hxT⟩)
    have hrfx : (faceBoundaryGraph K).Reachable f x := by
      obtain ⟨p⟩ := hrI
      exact ⟨(p.map (SimpleGraph.Embedding.induce (T : Set (Site 2))).toHom).copy rfl rfl⟩
    rw [SimpleGraph.mem_edgeSet]
    exact ⟨he, hrfx, hrfx.trans he.reachable⟩

lemma tightAxisCircuitData_instance {n ℓ : ℕ} {F : Finset (Sym2 (Site 2))}
    {K : Finset (Site 2)} (hKbox : (↑K : Set (Site 2)) ⊆ box 2 n)
    (hKcross : crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = F)
    (hKlen : contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ)
    {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph (↑K : Set (Site 2))).support ⊆ (T : Set (Site 2)))
    (hconn : FaceBoundaryConnected (↑K : Set (Site 2)) T)
    {j : ℕ} (hj : j < ℓ) (hax : axisVertex 2 j ∈ T) :
    ∃ K' : Finset (Site 2), (↑K' : Set (Site 2)) ⊆ box 2 n ∧
      crossEdges (↑K' : Set (Site 2)) (bondFinsetTouch 2 n) = F ∧
      contourLen (↑K' : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ ∧
      ∃ (T' : Finset (Site 2)) (j' : ℕ),
        (faceBoundaryGraph (↑K' : Set (Site 2))).support ⊆ (T' : Set (Site 2)) ∧
        j' < ℓ ∧ axisVertex 2 j' ∈ T' ∧
        (∀ e ∈ (faceBoundaryGraph (↑K' : Set (Site 2))).edgeSet,
          e ∈ (componentGraph (↑K' : Set (Site 2)) (axisVertex 2 j')).edgeSet) :=
  ⟨K, hKbox, hKcross, hKlen, T, j, hsupp, hj, hax,
    componentCovers_of_faceBoundaryConnected hsupp hconn hax⟩

/-! ## D. Examples: the singleton and rectangular clusters -/

lemma axisVertex_two_zero : axisVertex 2 0 = (![0, 0] : Site 2) := by
  funext i; fin_cases i <;> simp [axisVertex]

lemma axisVertex_zero_mem_singletonBoundarySupport :
    axisVertex 2 0 ∈ singletonBoundarySupport := by
  rw [axisVertex_two_zero]; exact mem_singletonBoundarySupport_00

lemma singletonOrigin_tight_dualCircuit :
    ∃ c : (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Walk
        (axisVertex 2 0) (axisVertex 2 0),
      c.IsTrail ∧
        ∀ e ∈ (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).edgeSet,
          e ∈ c.edges := by
  have hcov := componentCovers_of_faceBoundaryConnected
    (K := (↑({origin 2} : Finset (Site 2)) : Set (Site 2))) (T := singletonBoundarySupport)
    support_singletonOrigin_subset singletonOrigin_faceBoundaryConnected
    axisVertex_zero_mem_singletonBoundarySupport
  exact dualCircuit_of_componentCovers support_singletonOrigin_subset
    axisVertex_zero_mem_singletonBoundarySupport hcov

lemma singletonOrigin_componentCovers :
    ∀ e ∈ (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).edgeSet,
      e ∈ (componentGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))
        (axisVertex 2 0)).edgeSet :=
  componentCovers_of_faceBoundaryConnected support_singletonOrigin_subset
    singletonOrigin_faceBoundaryConnected axisVertex_zero_mem_singletonBoundarySupport

lemma axisVertex_two_natCast (m : ℕ) : axisVertex 2 m = (![(m : ℤ), 0] : Site 2) := by
  funext i; fin_cases i <;> simp [axisVertex]

lemma axisVertex_m_mem_boxFrame (m n : ℕ) : axisVertex 2 m ∈ boxFrame m n := by
  rw [axisVertex_two_natCast]
  exact mem_boxFrame_right m n 0 (by omega) (by positivity)

lemma boxCluster_componentCovers (m n : ℕ) :
    ∀ e ∈ (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).edgeSet,
      e ∈ (componentGraph (↑(boxCluster m n) : Set (Site 2)) (axisVertex 2 m)).edgeSet :=
  componentCovers_of_faceBoundaryConnected (support_boxCluster_subset_frame m n)
    (boxCluster_faceBoundaryConnected m n) (axisVertex_m_mem_boxFrame m n)

lemma boxCluster_tight_dualCircuit (m n : ℕ) :
    ∃ c : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk
        (axisVertex 2 m) (axisVertex 2 m),
      c.IsTrail ∧
        ∀ e ∈ (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).edgeSet, e ∈ c.edges :=
  dualCircuit_of_componentCovers (support_boxCluster_subset_frame m n)
    (axisVertex_m_mem_boxFrame m n) (boxCluster_componentCovers m n)

lemma tightAxisCircuitData_of_empty {n ℓ : ℕ}
    (hempty : realisedContours 2 n ℓ = ∅) : TightAxisCircuitData n ℓ := by
  intro F hF
  rw [hempty] at hF
  simp at hF

lemma contourSubsetCountBound_of_empty_tightData {n ℓ : ℕ}
    (hempty : realisedContours 2 n ℓ = ∅) : ContourSubsetCountBound 2 n ℓ :=
  contourSubsetCountBound_of_tightData (tightAxisCircuitData_of_empty hempty)

end Lattice

end StatMech
