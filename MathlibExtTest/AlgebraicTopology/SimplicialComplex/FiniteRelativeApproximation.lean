/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialComplex.FiniteRelativeApproximation

/-!
# Empty and folding consumers of actual simplicial morphisms

Unused ambient labels do not obstruct maps between geometrically empty
complexes. Collapsing the full two-vertex simplex retains the total mass and
is a continuous map to the literal target vertex.
-/

open PreAbstractSimplicialComplex

noncomputable section

namespace FiniteRelativeApproximationConsumer

/-- A ghost ambient label requires no image in the empty target type. -/
def ghostToEmpty : Morphism (⊥ : PreAbstractSimplicialComplex Unit)
    (⊥ : PreAbstractSimplicialComplex Empty) where
  vertexMap v := False.elim v.property
  face_mem s := False.elim s.property

example : IsEmpty (Vertex (⊥ : PreAbstractSimplicialComplex Unit)) :=
  ⟨fun v => v.property⟩

example : IsEmpty (Realization (⊥ : PreAbstractSimplicialComplex Unit)) :=
  ⟨fun x => x.support_mem⟩

example : Continuous ghostToEmpty.realization := ghostToEmpty.realization.continuous

/-- The full edge folds to one vertex, allowing the two endpoint images to coincide. -/
def foldEdge : Morphism (⊤ : PreAbstractSimplicialComplex Bool)
    (⊤ : PreAbstractSimplicialComplex Unit) where
  vertexMap _ := ⟨(), Finset.singleton_nonempty ()⟩
  face_mem s := by
    classical
    let : DecidableEq Unit := Classical.decEq Unit
    obtain ⟨v, hv⟩ := faceVertices_nonempty _ s
    exact ⟨(), Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩

/-- The outer map selects one endpoint after the inner map folds the edge. -/
def includeFalse : Morphism (⊤ : PreAbstractSimplicialComplex Unit)
    (⊤ : PreAbstractSimplicialComplex Bool) where
  vertexMap _ := ⟨false, Finset.singleton_nonempty false⟩
  face_mem s := by
    classical
    let : DecidableEq Bool := Classical.decEq Bool
    obtain ⟨v, hv⟩ := faceVertices_nonempty _ s
    exact ⟨false, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩

example : (includeFalse.comp foldEdge).vertexMap ⟨true, Finset.singleton_nonempty true⟩ =
    ⟨false, Finset.singleton_nonempty false⟩ := rfl

example : (Morphism.id _).comp foldEdge = foldEdge := by
  ext v

example : (includeFalse.comp foldEdge).comp (Morphism.id _) =
    includeFalse.comp (foldEdge.comp (Morphism.id _)) :=
  Morphism.comp_assoc _ _ _

theorem foldEdge_constant (x : Realization (⊤ : PreAbstractSimplicialComplex Bool)) :
    foldEdge.realization x = Realization.vertex (⊤ : PreAbstractSimplicialComplex Unit)
      () (Finset.singleton_nonempty ()) := by
  apply Realization.ext
  change (foldEdge.realizationMap x).point = _
  rw [Morphism.realizationMap_point]
  exact Convexity.StdSimplex.map_const _ ()

example : foldEdge.vertexMap ⟨false, Finset.singleton_nonempty false⟩ =
    foldEdge.vertexMap ⟨true, Finset.singleton_nonempty true⟩ := rfl

example (x : Realization (⊤ : PreAbstractSimplicialComplex Bool)) :
    (foldEdge.comp (Morphism.id _)).realizationMap x = foldEdge.realizationMap x := by
  rw [Morphism.realizationMap_comp, Morphism.realizationMap_id]

example (f : C(Realization (⊤ : PreAbstractSimplicialComplex Bool),
    Realization (⊤ : PreAbstractSimplicialComplex ℕ))) :
    ∃ t : Finset ℕ,
      ∃ g : C(Realization (⊤ : PreAbstractSimplicialComplex Bool),
        Realization (restrictVertices (⊤ : PreAbstractSimplicialComplex ℕ) t)),
      ∀ x, Realization.inclusion (restrictVertices_le _ t) (g x) = f x :=
  Realization.exists_finite_vertex_factor f

example (P : PreAbstractSimplicialComplex ℕ) (v : Vertex P) :
    IsOpen (Realization.openStar P v) := Realization.isOpen_openStar P v

/-- The constructed carrier homotopy is available as an actual homotopy relative
to a literal source vertex, for use in based constructions. -/
def basedCarrierHomotopy {V W : Type*} (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) [Finite (Face P)]
    (f g : C(Realization P, Realization Q))
    (h : ∀ x, (g x).point.weights.support ⊆ (f x).point.weights.support)
    (v : Vertex P)
    (hv : f (Realization.vertex P v.val v.property) =
      g (Realization.vertex P v.val v.property)) :
    ContinuousMap.HomotopyRel f g {Realization.vertex P v.val v.property} where
  toHomotopy := Realization.carrierHomotopy f g h
  prop' t x hx := by
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact Realization.carrierHomotopy_fixed f g h hv t

def edgeToInfiniteVertex : C(Realization (⊤ : PreAbstractSimplicialComplex Bool),
    Realization (⊤ : PreAbstractSimplicialComplex ℕ)) :=
  ContinuousMap.const _ (Realization.vertex _ 0 (Finset.singleton_nonempty 0))

def infiniteVertexChoice : Vertex (⊤ : PreAbstractSimplicialComplex Bool) →
    Vertex (⊤ : PreAbstractSimplicialComplex ℕ) :=
  fun _ => ⟨0, Finset.singleton_nonempty 0⟩

theorem infiniteVertexChoice_star :
    ∀ v x, x ∈ Realization.openStar _ v →
      edgeToInfiniteVertex x ∈ Realization.openStar _ (infiniteVertexChoice v) :=
  fun _ _ _ => Realization.vertex_mem_openStar _

/-- The star construction is a folding-safe map into a genuinely infinite target. -/
def starFold : Morphism (⊤ : PreAbstractSimplicialComplex Bool)
    (⊤ : PreAbstractSimplicialComplex ℕ) :=
  Morphism.ofStarMap edgeToInfiniteVertex infiniteVertexChoice infiniteVertexChoice_star

example (v : Vertex (⊤ : PreAbstractSimplicialComplex Bool)) (t : unitInterval) :
    Morphism.starCarrierHomotopy edgeToInfiniteVertex infiniteVertexChoice
      infiniteVertexChoice_star (t, Realization.vertex _ v.val v.property) =
        Realization.vertex (⊤ : PreAbstractSimplicialComplex ℕ) 0
          (Finset.singleton_nonempty 0) :=
  Morphism.starCarrierHomotopy_fixed_vertex _ _ _ v ⟨0, Finset.singleton_nonempty 0⟩ rfl t

example (P : PreAbstractSimplicialComplex ℕ) (v : Vertex P) :
    IsClosed (Realization.closedStar P v) := Realization.isClosed_closedStar v

/-- The zero sphere has two isolated actual vertices and no edge. -/
def zeroSphere : PreAbstractSimplicialComplex Bool where
  faces := {s | ∃ b : Bool, s = {b}}
  isRelLowerSet_faces := by
    rintro s ⟨b, rfl⟩
    refine ⟨Finset.singleton_nonempty b, ?_⟩
    intro t ht hne
    rcases Finset.subset_singleton_iff.mp ht with h | rfl
    · exact (hne.ne_empty h).elim
    · exact ⟨b, rfl⟩

theorem zeroSphere_face_range (s : Face zeroSphere) :
    ∃ b : Bool, Set.range (Realization.faceMap zeroSphere s) =
      {Realization.vertex zeroSphere b ⟨b, rfl⟩} := by
  obtain ⟨b, hb⟩ := s.property
  have hconst : ∀ q : Convexity.StdSimplex ℝ s.val,
      Realization.faceMap zeroSphere s q = Realization.vertex zeroSphere b ⟨b, rfl⟩ := by
    intro q
    apply Realization.ext
    have hval : (Subtype.val : s.val → Bool) = (fun _ => b) := by
      funext v
      exact Finset.mem_singleton.mp (hb ▸ v.property)
    change q.map (Subtype.val : s.val → Bool) = Convexity.StdSimplex.single b
    rw [hval]
    exact Convexity.StdSimplex.map_const q b
  refine ⟨b, ?_⟩
  have : Nonempty s.val := (zeroSphere.isRelLowerSet_faces s.property).1.to_subtype
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact Set.mem_singleton_iff.mpr (hconst q)
  · intro hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨Convexity.StdSimplex.single (Classical.choice this), hconst _⟩

/-- The quantitative construction already applies to the unsubdivided zero
sphere, deriving the vertex choices and fixing every given vertex value. -/
theorem zeroSphere_vertexApproximation {W : Type*} (Q : PreAbstractSimplicialComplex W)
    (f : C(Realization zeroSphere, Realization Q)) :
    ∃ g : Morphism zeroSphere Q, ∃ H : ContinuousMap.Homotopy f g.realization,
      ∀ v : Vertex zeroSphere, ∀ w : Vertex Q,
        f (Realization.vertex zeroSphere v.val v.property) =
            Realization.vertex Q w.val w.property →
          g.vertexMap v = w ∧ ∀ t : unitInterval,
            H (t, Realization.vertex zeroSphere v.val v.property) =
              f (Realization.vertex zeroSphere v.val v.property) := by
  let := Realization.finiteCoordinateMetricSpace zeroSphere
  obtain ⟨ε, hε, hbound⟩ := Morphism.exists_starApproximation_mesh_bound f
  have hmesh : ∀ s : Face zeroSphere,
      Metric.diam ((ContinuousMap.id (Realization zeroSphere)) ''
        Set.range (Realization.faceMap zeroSphere s)) ≤ ε := by
    intro s
    obtain ⟨b, hb⟩ := zeroSphere_face_range s
    change Metric.diam (_root_.id '' Set.range (Realization.faceMap zeroSphere s)) ≤ ε
    rw [Set.image_id, hb, Metric.diam_singleton]
    exact hε.le
  obtain ⟨g, H, _, hfixed⟩ := hbound Bool zeroSphere (ContinuousMap.id _) hmesh
  exact ⟨g, H, hfixed⟩

end FiniteRelativeApproximationConsumer

end
