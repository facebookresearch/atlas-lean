/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.Subdivision
public import MathlibExt.AlgebraicTopology.SimplicialComplex.FiniteRelativeApproximation
public import MathlibExt.Topology.Category.TopCat.MappingCone
public import Mathlib.Data.Finset.Sum

/-!
# Actual simplicial mapping cylinders and cones

The copied domain is the actual barycentric subdivision. A cylinder face
is a finite chain of copied source faces together with target vertices,
whose combined target hull is a genuine target face. This definition allows
folding maps, arbitrary ambient ghost labels and infinite weak targets.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Topology CategoryTheory MonoidalCategory

universe u v w

namespace PreAbstractSimplicialComplex
namespace MappingCylinder

variable {V : Type u} {W : Type v}
variable {P : PreAbstractSimplicialComplex V} {Q : PreAbstractSimplicialComplex W}

/-- The target vertices required by one finite cylinder label set. -/
def hull (f : Morphism P Q) (s : Finset (Face P ⊕ W)) : Finset W := by
  classical
  exact s.toRight ∪ s.toLeft.biUnion (fun a => (f.faceImage a).val)

theorem hull_mono (f : Morphism P Q) {s t : Finset (Face P ⊕ W)} (h : s ⊆ t) :
    hull f s ⊆ hull f t := by
  classical
  apply Finset.union_subset_union (Finset.toRight_subset_toRight h)
  intro a ha
  obtain ⟨b, hb, hab⟩ := Finset.mem_biUnion.mp ha
  exact Finset.mem_biUnion.mpr ⟨b, Finset.toLeft_subset_toLeft h hb, hab⟩

open Classical in
theorem hull_disjSum (f : Morphism P Q) (a : Finset (Face P)) (b : Finset W) :
    hull f (a.disjSum b) = b ∪ a.biUnion (fun x => (f.faceImage x).val) := by
  simp only [hull, Finset.toRight_disjSum, Finset.toLeft_disjSum]

/-- The genuine cylinder complex on copied source-face and original target labels. -/
def complex (f : Morphism P Q) : PreAbstractSimplicialComplex (Face P ⊕ W) where
  faces := {s | s.Nonempty ∧ IsChain (· ≤ ·) (s.toLeft : Set (Face P)) ∧ hull f s ∈ Q}
  isRelLowerSet_faces := by
    classical
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    refine ⟨ht, hs.2.1.mono (Finset.toLeft_subset_toLeft hts), ?_⟩
    exact (Q.isRelLowerSet_faces hs.2.2).2 (hull_mono f hts) (by
      obtain ⟨z, hz⟩ := ht
      cases z with
      | inl a =>
        obtain ⟨b, hb⟩ := (Q.isRelLowerSet_faces (f.faceImage a).property).1
        exact ⟨b, Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨a, Finset.mem_toLeft.mpr hz, hb⟩)⟩
      | inr b => exact ⟨b, Finset.mem_union_left _ (Finset.mem_toRight.mpr hz)⟩)

@[simp]
theorem mem_complex (f : Morphism P Q) (s : Finset (Face P ⊕ W)) :
    s ∈ complex f ↔ s.Nonempty ∧ IsChain (· ≤ ·) (s.toLeft : Set (Face P)) ∧
      hull f s ∈ Q := Iff.rfl

/-- The target hull of every nonempty cylinder face is an actual target face. -/
def hullFace (f : Morphism P Q) (s : Face (complex f)) : Face Q :=
  ⟨hull f s.val, s.property.2.2⟩

theorem faceImage_mono (f : Morphism P Q) {a b : Face P} (h : a ≤ b) :
    (f.faceImage a).val ⊆ (f.faceImage b).val := by
  classical
  exact Finset.image_mono _ (faceVertices_mono P h)

/-- The pure copied subdivision face is a face of the actual cylinder. -/
theorem domain_face_mem (f : Morphism P Q) (s : Face (barycentricSubdivision P)) :
    s.val.disjSum (∅ : Finset W) ∈ complex f := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Finset.disjSum_empty, Finset.map_nonempty] using s.property.1
  · simpa only [Finset.toLeft_disjSum] using s.property.2
  · rw [hull_disjSum, Finset.empty_union]
    apply (Q.isRelLowerSet_faces (f.faceImage (subdivisionLastFace P s)).property).2
    · intro b hb
      obtain ⟨a, ha, hba⟩ := Finset.mem_biUnion.mp hb
      exact faceImage_mono f (le_subdivisionLastFace P s ⟨a, ha⟩) hba
    · obtain ⟨a, ha⟩ := s.property.1
      obtain ⟨b, hb⟩ := (Q.isRelLowerSet_faces (f.faceImage a).property).1
      exact ⟨b, Finset.mem_biUnion.mpr ⟨a, ha, hb⟩⟩

/-- Original target faces are retained without subdivision or changed labels. -/
theorem target_face_mem (f : Morphism P Q) (s : Face Q) :
    (∅ : Finset (Face P)).disjSum s.val ∈ complex f := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Finset.empty_disjSum, Finset.map_nonempty] using
      (Q.isRelLowerSet_faces s.property).1
  · simp only [Finset.toLeft_disjSum, Finset.coe_empty]
    exact IsChain.empty
  · simpa only [hull_disjSum, Finset.biUnion_empty, Finset.union_empty] using s.property

/-- The actual nonempty faces after an injective ambient relabeling. -/
def relabelComplex {A : Type u} {B : Type v}
    (T : PreAbstractSimplicialComplex A) (e : A ↪ B) : PreAbstractSimplicialComplex B := by
  classical
  exact T.map e

/-- The literal copied subdivision subcomplex, on the cylinder label type. -/
def domainComplex (P : PreAbstractSimplicialComplex V) (W : Type v) :
    PreAbstractSimplicialComplex (Face P ⊕ W) :=
  relabelComplex (barycentricSubdivision P) Function.Embedding.inl

/-- The unchanged target, viewed on the cylinder label type. -/
def targetComplex (P : PreAbstractSimplicialComplex V) (Q : PreAbstractSimplicialComplex W) :
    PreAbstractSimplicialComplex (Face P ⊕ W) := relabelComplex Q Function.Embedding.inr

theorem domainComplex_le (f : Morphism P Q) : domainComplex P W ≤ complex f := by
  classical
  let : DecidableEq (Face P ⊕ W) := Classical.decEq _
  intro s hs
  obtain ⟨a, ha, rfl⟩ := hs
  have h := domain_face_mem f ⟨a, ha⟩
  rw [Finset.disjSum_empty, Finset.map_eq_image] at h
  change a.image (Function.Embedding.inl : Face P ↪ Face P ⊕ W) ∈ complex f
  change a.image (Function.Embedding.inl : Face P ↪ Face P ⊕ W) ∈ complex f at h
  exact h

theorem targetComplex_le (f : Morphism P Q) : targetComplex P Q ≤ complex f := by
  classical
  let : DecidableEq (Face P ⊕ W) := Classical.decEq _
  intro s hs
  obtain ⟨a, ha, rfl⟩ := hs
  have h := target_face_mem f ⟨a, ha⟩
  rw [Finset.empty_disjSum, Finset.map_eq_image] at h
  change a.image (Function.Embedding.inr : W ↪ Face P ⊕ W) ∈ complex f
  change a.image (Function.Embedding.inr : W ↪ Face P ⊕ W) ∈ complex f at h
  exact h

/-- The literal belonging-vertex map into the injectively relabeled complex. -/
def relabelMorphism {A : Type u} {B : Type v}
    (T : PreAbstractSimplicialComplex A) (e : A ↪ B) : Morphism T (relabelComplex T e) where
  vertexMap v := ⟨e v.val, by
    classical
    exact ⟨{v.val}, v.property, Finset.image_singleton e v.val⟩⟩
  face_mem s := by
    classical
    refine ⟨s.val, s.property, ?_⟩
    have h := congrArg (fun a : Finset A => a.image e) (faceVertices_image_val T s)
    rw [Finset.image_image] at h
    exact h.symm

theorem relabelMorphism_point {A : Type u} {B : Type v}
    (T : PreAbstractSimplicialComplex A) (e : A ↪ B) (x : Realization T) :
    ((relabelMorphism T e).realization x).point = x.point.map e := by
  change (Realization.vertexCoordinates x).map (fun v => e v.val) = x.point.map e
  calc
    (Realization.vertexCoordinates x).map (fun v => e v.val) =
        ((Realization.vertexCoordinates x).map (Subtype.val : Vertex T → A)).map e :=
      (Convexity.StdSimplex.map_map _ _ _).symm
    _ = x.point.map e := by rw [Realization.map_vertexCoordinates]

theorem relabelMorphism_injective {A : Type u} {B : Type v}
    (T : PreAbstractSimplicialComplex A) (e : A ↪ B) :
    Function.Injective (relabelMorphism T e).realization := by
  intro x y h
  apply Realization.ext
  apply Convexity.StdSimplex.map_injective e.injective
  simpa only [relabelMorphism_point] using congrArg Realization.point h

theorem relabelMorphism_surjective {A : Type u} {B : Type v}
    (T : PreAbstractSimplicialComplex A) (e : A ↪ B) :
    Function.Surjective (relabelMorphism T e).realization := by
  classical
  intro y
  obtain ⟨s, hs, hsupport⟩ := y.support_mem
  have hy : y.point ∈ Set.range (Convexity.StdSimplex.map (fun a : s => e a.val)) := by
    rw [Convexity.StdSimplex.mem_range_map_iff]
    intro b hb
    by_contra hweight
    have hmem : b ∈ y.point.weights.support := Finsupp.mem_support_iff.mpr hweight
    rw [← hsupport] at hmem
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hmem
    exact hb ⟨⟨a, ha⟩, he⟩
  obtain ⟨q, hq⟩ := hy
  refine ⟨Realization.faceMap T ⟨s, hs⟩ q, ?_⟩
  apply Realization.ext
  rw [relabelMorphism_point]
  change (q.map (Subtype.val : s → A)).map e = y.point
  rw [Convexity.StdSimplex.map_map]
  exact hq

open Classical in
/-- The intrinsic finite-face coordinate equivalence for an injective relabeling. -/
def finiteRelabelEquiv {A : Type u} {B : Type v} (e : A ↪ B) (s : Finset A) :
    s ≃ s.image e :=
  Equiv.ofBijective (fun a : s =>
    (⟨e a.val, Finset.mem_image.mpr ⟨a.val, a.property, rfl⟩⟩ : s.image e))
    ⟨by
      intro a b h
      exact Subtype.ext (e.injective (congrArg Subtype.val h)), by
      intro b
      obtain ⟨a, ha, he⟩ := Finset.mem_image.mp b.property
      exact ⟨⟨a, ha⟩, Subtype.ext he⟩⟩

/-- Injective ambient relabeling preserves the actual weak face topology. -/
def relabelHomeomorph {A : Type u} {B : Type v}
    (T : PreAbstractSimplicialComplex A) (e : A ↪ B) :
    Realization T ≃ₜ Realization (relabelComplex T e) := by
  classical
  let E := Equiv.ofBijective (relabelMorphism T e).realization
    ⟨relabelMorphism_injective T e, relabelMorphism_surjective T e⟩
  refine
    { toEquiv := E
      continuous_toFun := (relabelMorphism T e).realization.continuous
      continuous_invFun := ?_ }
  rw [Realization.continuous_iff]
  rintro ⟨s, hs⟩
  obtain ⟨t, ht, rfl⟩ := hs
  let H := simplexRelabelHomeomorph (finiteRelabelEquiv e t)
  have heq : E.symm ∘ Realization.faceMap (relabelComplex T e)
        ⟨t.image e, ⟨t, ht, rfl⟩⟩ =
      Realization.faceMap T ⟨t, ht⟩ ∘ H.symm := by
    funext q
    apply relabelMorphism_injective T e
    change E (E.symm _) = _
    rw [Equiv.apply_symm_apply]
    apply Realization.ext
    rw [relabelMorphism_point]
    change q.map (Subtype.val : t.image e → B) =
      ((H.symm q).map (Subtype.val : t → A)).map e
    have h := congrArg (fun r : Convexity.StdSimplex ℝ (t.image e) =>
      r.map (Subtype.val : t.image e → B)) (H.apply_symm_apply q)
    change ((H.symm q).map (finiteRelabelEquiv e t)).map
      (Subtype.val : t.image e → B) = q.map (Subtype.val : t.image e → B) at h
    rw [Convexity.StdSimplex.map_map] at h ⊢
    exact h.symm
  change Continuous (E.symm ∘ Realization.faceMap (relabelComplex T e)
    ⟨t.image e, ⟨t, ht, rfl⟩⟩)
  erw [heq]
  exact (Realization.continuous_faceMap T ⟨t, ht⟩).comp H.symm.continuous

/-- The literal belonging-vertex morphism of an actual subcomplex inclusion. -/
def inclusionMorphism {A : Type u} {T U : PreAbstractSimplicialComplex A}
    (h : T ≤ U) : Morphism T U where
  vertexMap v := ⟨v.val, h v.property⟩
  face_mem s := by
    classical
    change (faceVertices T s).image (Subtype.val : Vertex T → A) ∈ U
    rw [faceVertices_image_val]
    exact h s.property

private theorem inclusionMorphism_point {A : Type u} {T U : PreAbstractSimplicialComplex A}
    (h : T ≤ U) (x : Realization T) :
    ((inclusionMorphism h).realization x).point = x.point :=
  Realization.map_vertexCoordinates x

private theorem inclusionMorphism_realization {A : Type u}
    {T U : PreAbstractSimplicialComplex A} (h : T ≤ U) (x : Realization T) :
    (inclusionMorphism h).realization x = Realization.inclusion h x :=
  Realization.ext (inclusionMorphism_point h x)

/-- The copied actual barycentric domain is included by its literal left labels. -/
def domainMorphism (f : Morphism P Q) : Morphism (barycentricSubdivision P) (complex f) :=
  (inclusionMorphism (domainComplex_le f)).comp
    (relabelMorphism (barycentricSubdivision P) Function.Embedding.inl)

/-- The original target is included by its unchanged literal right labels. -/
def targetMorphism (f : Morphism P Q) : Morphism Q (complex f) :=
  (inclusionMorphism (targetComplex_le f)).comp (relabelMorphism Q Function.Embedding.inr)

theorem domainMorphism_point (f : Morphism P Q) (x : Realization (barycentricSubdivision P)) :
    ((domainMorphism f).realization x).point = x.point.map Sum.inl := by
  have hc := Morphism.realizationMap_comp (inclusionMorphism (domainComplex_le f))
    (relabelMorphism (barycentricSubdivision P) Function.Embedding.inl) x
  calc
    ((domainMorphism f).realization x).point =
        ((inclusionMorphism (domainComplex_le f)).realization
          ((relabelMorphism (barycentricSubdivision P)
            Function.Embedding.inl).realization x)).point :=
      congrArg Realization.point hc
    _ = ((relabelMorphism (barycentricSubdivision P) Function.Embedding.inl).realization x).point :=
      inclusionMorphism_point _ _
    _ = x.point.map Sum.inl := relabelMorphism_point _ _ _

theorem targetMorphism_point (f : Morphism P Q) (x : Realization Q) :
    ((targetMorphism f).realization x).point = x.point.map Sum.inr := by
  have hc := Morphism.realizationMap_comp (inclusionMorphism (targetComplex_le f))
    (relabelMorphism Q Function.Embedding.inr) x
  calc
    ((targetMorphism f).realization x).point =
        ((inclusionMorphism (targetComplex_le f)).realization
          ((relabelMorphism Q Function.Embedding.inr).realization x)).point :=
      congrArg Realization.point hc
    _ = ((relabelMorphism Q Function.Embedding.inr).realization x).point :=
      inclusionMorphism_point _ _
    _ = x.point.map Sum.inr := relabelMorphism_point _ _ _

/-- The copied barycentric domain is genuinely a closed subcomplex embedding. -/
theorem isClosedEmbedding_domainMorphism (f : Morphism P Q) :
    IsClosedEmbedding (domainMorphism f).realization := by
  have heq : (fun x => (domainMorphism f).realization x) =
      Realization.inclusion (domainComplex_le f) ∘
        relabelHomeomorph (barycentricSubdivision P) Function.Embedding.inl := by
    funext x
    change (domainMorphism f).realizationMap x = _
    rw [domainMorphism, Morphism.realizationMap_comp]
    exact inclusionMorphism_realization _ _
  change IsClosedEmbedding (fun x => (domainMorphism f).realization x)
  rw [heq]
  exact (Realization.isClosedEmbedding_inclusion (domainComplex_le f)).comp
    (relabelHomeomorph (barycentricSubdivision P) Function.Embedding.inl).isClosedEmbedding

/-- The unchanged target is genuinely a closed subcomplex embedding. -/
theorem isClosedEmbedding_targetMorphism (f : Morphism P Q) :
    IsClosedEmbedding (targetMorphism f).realization := by
  have heq : (fun x => (targetMorphism f).realization x) =
      Realization.inclusion (targetComplex_le f) ∘
        relabelHomeomorph Q Function.Embedding.inr := by
    funext x
    change (targetMorphism f).realizationMap x = _
    rw [targetMorphism, Morphism.realizationMap_comp]
    exact inclusionMorphism_realization _ _
  change IsClosedEmbedding (fun x => (targetMorphism f).realization x)
  rw [heq]
  exact (Realization.isClosedEmbedding_inclusion (targetComplex_le f)).comp
    (relabelHomeomorph Q Function.Embedding.inr).isClosedEmbedding

@[simp]
theorem hull_singleton_inr (f : Morphism P Q) (b : W) :
    hull f {Sum.inr b} = {b} := by
  classical
  have hl : ({Sum.inr b} : Finset (Face P ⊕ W)).toLeft = ∅ := by ext a; simp
  have hr : ({Sum.inr b} : Finset (Face P ⊕ W)).toRight = {b} := by ext a; simp
  simp only [hull, hl, hr, Finset.biUnion_empty, Finset.union_empty]

theorem right_vertex_mem (f : Morphism P Q) (b : W)
    (hb : ({Sum.inr b} : Finset (Face P ⊕ W)) ∈ complex f) : ({b} : Finset W) ∈ Q := by
  have h := hb.2.2
  simpa only [hull_singleton_inr] using h

/-- A copied source-face vertex retracts to the given map's actual barycenter
image, retaining all multiplicities when that map folds source vertices. -/
def leftPoint (f : Morphism P Q) (a : Face P) : Realization Q :=
  f.realization (Realization.faceBarycenter a)

theorem leftPoint_support (f : Morphism P Q) (a : Face P) :
    (leftPoint f a).point.weights.support ⊆ (f.faceImage a).val := by
  let := (P.isRelLowerSet_faces a.property).1.to_subtype
  change (f.realizationMap (Realization.faceMap P a
    (Convexity.StdSimplex.barycenter (K := ℝ) (M := a.val)))).point.weights.support ⊆ _
  rw [Morphism.realizationMap_faceMap]
  exact Realization.support_map_subtype_subset _ _

/-- The retraction's point value on each actual belonging cylinder vertex. -/
def vertexPoint (f : Morphism P Q) (v : Vertex (complex f)) : Realization Q :=
  match v with
  | ⟨Sum.inl a, _⟩ => leftPoint f a
  | ⟨Sum.inr b, hb⟩ => Realization.vertex Q b (right_vertex_mem f b hb)

theorem vertexPoint_support (f : Morphism P Q) (s : Face (complex f))
    (v : Vertex (complex f)) (hv : v ∈ faceVertices (complex f) s) :
    (vertexPoint f v).point.weights.support ⊆ (hullFace f s).val := by
  classical
  have hlabel : v.val ∈ s.val := Finset.mem_subtype.mp hv
  rcases v with ⟨z, hz⟩
  cases z with
  | inl a =>
      have ha : a ∈ s.val.toLeft := Finset.mem_toLeft.mpr hlabel
      exact (leftPoint_support f a).trans (by
        intro b hb
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a, ha, hb⟩))
  | inr b =>
      have hs : (vertexPoint f ⟨Sum.inr b, hz⟩).point.weights.support = {b} :=
        Convexity.StdSimplex.support_weights_eq_singleton.mpr rfl
      rw [hs]
      exact Finset.singleton_subset_iff.mpr
        (Finset.mem_union_left _ (Finset.mem_toRight.mpr hlabel))

/-- The exact affine pushforward to the original target coordinates. -/
def retractionPoint (f : Morphism P Q) (x : Realization (complex f)) :
    Convexity.StdSimplex ℝ W :=
  (Realization.vertexCoordinates x).iConvexComb (fun v => (vertexPoint f v).point)

theorem retractionPoint_faceMap (f : Morphism P Q) (s : Face (complex f))
    (q : Convexity.StdSimplex ℝ s.val) :
    retractionPoint f (Realization.faceMap (complex f) s q) =
      q.iConvexComb (fun a : s.val =>
        (vertexPoint f (faceVertexEmbedding (complex f) s a)).point) := by
  rw [retractionPoint, Realization.vertexCoordinates_faceMap, Convexity.iConvexComb_map]

theorem retractionPoint_support (f : Morphism P Q) (x : Realization (complex f)) :
    (retractionPoint f x).weights.support ⊆
      hull f x.point.weights.support := by
  classical
  let s : Face (complex f) := ⟨x.point.weights.support, x.support_mem⟩
  have hcoords : (Realization.vertexCoordinates x).weights.support =
      faceVertices (complex f) s := by
    change (x.point.weights.subtypeDomain
      (fun z => ({z} : Finset (Face P ⊕ W)) ∈ complex f)).support =
      x.point.weights.support.subtype (fun z => ({z} : Finset (Face P ⊕ W)) ∈ complex f)
    exact Finsupp.support_subtypeDomain
  intro b hb
  by_contra houtside
  have hzero : (retractionPoint f x).weights b = 0 := by
    rw [retractionPoint, Convexity.StdSimplex.weights_iConvexComb_eq_sum, Finsupp.sum_apply]
    change ∑ v ∈ (Realization.vertexCoordinates x).weights.support,
      (Realization.vertexCoordinates x).weights v * (vertexPoint f v).point.weights b = 0
    apply Finset.sum_eq_zero
    intro v hv
    have hz : (vertexPoint f v).point.weights b = 0 := by
      by_contra hne
      exact houtside (vertexPoint_support f s v (hcoords ▸ hv)
        (Finsupp.mem_support_iff.mpr hne))
    rw [hz, mul_zero]
  exact (Finsupp.mem_support_iff.mp hb) hzero

/-- The unique actual coordinates of a point lying in a specified closed face. -/
def pointInFace {A : Type u} {T : PreAbstractSimplicialComplex A} (s : Face T)
    (x : Realization T) (hx : x.point.weights.support ⊆ s.val) :
    Convexity.StdSimplex ℝ s.val :=
  Classical.choose ((Realization.mem_range_faceMap_iff s x).mpr hx)

theorem pointInFace_map {A : Type u} {T : PreAbstractSimplicialComplex A} (s : Face T)
    (x : Realization T) (hx : x.point.weights.support ⊆ s.val) :
    Realization.faceMap T s (pointInFace s x hx) = x :=
  Classical.choose_spec ((Realization.mem_range_faceMap_iff s x).mpr hx)

/-- Finite affine coordinates of the retraction on one actual cylinder face. -/
def faceRetractionCoordinates (f : Morphism P Q) (s : Face (complex f)) :
    Convexity.ConvexSpace.AffineMap ℝ (Convexity.StdSimplex ℝ s.val)
      (Convexity.StdSimplex ℝ (hullFace f s).val) :=
  Convexity.StdSimplex.affineMapMk (fun a : s.val =>
    pointInFace (hullFace f s) (vertexPoint f (faceVertexEmbedding (complex f) s a))
      (vertexPoint_support f s _ (faceVertex_mem (complex f) s a)))

theorem faceRetractionCoordinates_point (f : Morphism P Q) (s : Face (complex f))
    (q : Convexity.StdSimplex ℝ s.val) :
    (faceRetractionCoordinates f s q).map
      (Subtype.val : (hullFace f s).val → W) = retractionPoint f
        (Realization.faceMap (complex f) s q) := by
  rw [retractionPoint_faceMap]
  change (q.iConvexComb _ : Convexity.StdSimplex ℝ (hullFace f s).val).map
    (Subtype.val : (hullFace f s).val → W) = _
  rw [Convexity.map_iConvexComb]
  apply Convexity.iConvexComb_congr
  intro a _
  exact congrArg Realization.point (pointInFace_map _ _ _)

theorem continuous_faceRetractionCoordinates (f : Morphism P Q) (s : Face (complex f)) :
    Continuous (faceRetractionCoordinates f s) :=
  Realization.continuous_finite_mixture _

/-- The actual affine retraction to the unchanged target. -/
def retractionMap (f : Morphism P Q) (x : Realization (complex f)) : Realization Q where
  point := retractionPoint f x
  support_mem := (Q.isRelLowerSet_faces (hullFace f
    ⟨x.point.weights.support, x.support_mem⟩).property).2
    (retractionPoint_support f x) (retractionPoint f x).support_weights_nonempty

theorem retractionMap_faceMap (f : Morphism P Q) (s : Face (complex f))
    (q : Convexity.StdSimplex ℝ s.val) :
    retractionMap f (Realization.faceMap (complex f) s q) =
      Realization.faceMap Q (hullFace f s) (faceRetractionCoordinates f s q) := by
  apply Realization.ext
  exact (faceRetractionCoordinates_point f s q).symm

theorem continuous_retractionMap (f : Morphism P Q) : Continuous (retractionMap f) := by
  rw [Realization.continuous_iff]
  intro s
  have heq : retractionMap f ∘ Realization.faceMap (complex f) s =
      Realization.faceMap Q (hullFace f s) ∘ faceRetractionCoordinates f s :=
    funext (retractionMap_faceMap f s)
  rw [heq]
  exact (Realization.continuous_faceMap Q (hullFace f s)).comp
    (continuous_faceRetractionCoordinates f s)

/-- The continuous retraction with its computed finite-face affine formula. -/
def retraction (f : Morphism P Q) : C(Realization (complex f), Realization Q) :=
  ⟨retractionMap f, continuous_retractionMap f⟩

theorem faceBarycenter_point (a : Face P) :
    (Realization.faceBarycenter a).point = Convexity.StdSimplex.subBarycenter a.val
      (P.isRelLowerSet_faces a.property).1 := by
  classical
  let := (P.isRelLowerSet_faces a.property).1.to_subtype
  change (Convexity.StdSimplex.subBarycenter (K := ℝ) (Finset.univ : Finset a.val)
    Finset.univ_nonempty).map (Subtype.val : a.val → V) = _
  rw [Realization.map_subBarycenter_injective _ Subtype.val_injective]
  congr 1
  exact Finset.attach_image_val

theorem vertexCoordinates_barycentricHomeomorph (x : Realization (barycentricSubdivision P)) :
    Realization.vertexCoordinates (barycentricHomeomorph P x) =
      x.point.iConvexComb (fun a : Face P =>
        Realization.vertexCoordinates (Realization.faceBarycenter a)) := by
  apply Convexity.StdSimplex.map_injective (R := ℝ) Subtype.val_injective
  calc
    (Realization.vertexCoordinates (barycentricHomeomorph P x)).map
        (Subtype.val : Vertex P → V) = (barycentricHomeomorph P x).point :=
      Realization.map_vertexCoordinates _
    _ = x.point.iConvexComb (fun a : Face P => Convexity.StdSimplex.subBarycenter a.val
        (P.isRelLowerSet_faces a.property).1) := barycentricHomeomorph_point P x
    _ = (x.point.iConvexComb (fun a : Face P =>
        Realization.vertexCoordinates (Realization.faceBarycenter a))).map
          (Subtype.val : Vertex P → V) := by
      rw [Convexity.map_iConvexComb]
      apply Convexity.iConvexComb_congr
      intro a _
      exact ((Realization.map_vertexCoordinates _).trans (faceBarycenter_point a)).symm

theorem retractionPoint_domain (f : Morphism P Q)
    (x : Realization (barycentricSubdivision P)) :
    retractionPoint f ((domainMorphism f).realization x) =
      x.point.iConvexComb (fun a => (leftPoint f a).point) := by
  change (Realization.vertexCoordinates ((domainMorphism f).realizationMap x)).iConvexComb _ = _
  rw [Morphism.vertexCoordinates_realizationMap, Convexity.iConvexComb_map]
  change (Realization.vertexCoordinates x).iConvexComb
    (fun v : Vertex (barycentricSubdivision P) => (leftPoint f v.val).point) = _
  calc
    (Realization.vertexCoordinates x).iConvexComb
        (fun v : Vertex (barycentricSubdivision P) => (leftPoint f v.val).point) =
        ((Realization.vertexCoordinates x).map
          (Subtype.val : Vertex (barycentricSubdivision P) → Face P)).iConvexComb
            (fun a => (leftPoint f a).point) :=
      (Convexity.iConvexComb_map (Realization.vertexCoordinates x)
        (Subtype.val : Vertex (barycentricSubdivision P) → Face P)
        (fun a : Face P => (leftPoint f a).point)).symm
    _ = x.point.iConvexComb (fun a => (leftPoint f a).point) := by
      rw [Realization.map_vertexCoordinates]

/-- The terminal copied-domain map is exactly the original given map under
the constructed barycentric comparison, with all folding multiplicities. -/
theorem retraction_domain (f : Morphism P Q)
    (x : Realization (barycentricSubdivision P)) :
    retraction f ((domainMorphism f).realization x) =
      f.realization (barycentricHomeomorph P x) := by
  apply Realization.ext
  change retractionPoint f ((domainMorphism f).realization x) = _
  rw [retractionPoint_domain]
  change x.point.iConvexComb (fun a => (leftPoint f a).point) =
    (Realization.vertexCoordinates (barycentricHomeomorph P x)).map
      (fun v : Vertex P => (f.vertexMap v).val)
  rw [vertexCoordinates_barycentricHomeomorph, Convexity.map_iConvexComb]
  rfl

/-- The entire unchanged target is fixed by the actual affine retraction. -/
theorem retraction_target (f : Morphism P Q) (x : Realization Q) :
    retraction f ((targetMorphism f).realization x) = x := by
  apply Realization.ext
  change (Realization.vertexCoordinates ((targetMorphism f).realizationMap x)).iConvexComb _ = _
  rw [Morphism.vertexCoordinates_realizationMap, Convexity.iConvexComb_map]
  change (Realization.vertexCoordinates x).iConvexComb
    (fun v : Vertex Q => Convexity.StdSimplex.single v.val) = x.point
  calc
    (Realization.vertexCoordinates x).iConvexComb
        (fun v : Vertex Q => Convexity.StdSimplex.single v.val) =
        ((Realization.vertexCoordinates x).map (Subtype.val : Vertex Q → W)).iConvexComb
          Convexity.StdSimplex.single :=
      (Convexity.iConvexComb_map (Realization.vertexCoordinates x)
        (Subtype.val : Vertex Q → W) (Convexity.StdSimplex.single (R := ℝ))).symm
    _ = x.point := by
      rw [Realization.map_vertexCoordinates, Convexity.StdSimplex.iConvexComb_single]

/-- The ordinary compact-interval product preserves the weak finite-face
continuity test. The whole weak polyhedron need not be compact or locally finite. -/
theorem continuous_interval_product {A : Type u} (T : PreAbstractSimplicialComplex A)
    {Z : Type w} [TopologicalSpace Z] (F : unitInterval × Realization T → Z)
    (hF : ∀ s : Face T, Continuous (fun z : unitInterval × Convexity.StdSimplex ℝ s.val =>
      F (z.1, Realization.faceMap T s z.2))) : Continuous F := by
  have htime (x : Realization T) : Continuous (fun t : unitInterval => F (t, x)) := by
    obtain ⟨q, hq⟩ := Realization.mem_range_support_face x
    have h : Continuous (fun t : unitInterval => F (t,
        Realization.faceMap T ⟨x.point.weights.support, x.support_mem⟩ q)) :=
      (hF ⟨x.point.weights.support, x.support_mem⟩).comp
        (continuous_id.prodMk (continuous_const (y := q)))
    rw [hq] at h
    exact h
  let curve : Realization T → C(unitInterval, Z) := fun x => ⟨fun t => F (t, x), htime x⟩
  have hc : Continuous curve := by
    rw [Realization.continuous_iff]
    intro s
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : Convexity.StdSimplex ℝ s.val × unitInterval =>
      F (z.2, Realization.faceMap T s z.1))
    exact (hF s).comp (continuous_snd.prodMk continuous_fst)
  have hu := ContinuousMap.continuous_uncurry_of_continuous
    (⟨curve, hc⟩ : C(Realization T, C(unitInterval, Z)))
  exact hu.comp (continuous_snd.prodMk continuous_fst)

/-- A constructed finite face containing a source cylinder face and every
point of its retracted target hull. -/
def carrierFace (f : Morphism P Q) (s : Face (complex f)) : Face (complex f) := by
  classical
  let t := s.val.toLeft.disjSum (hull f s.val)
  have hst : s.val ⊆ t := Finset.subset_disjSum.mpr
    ⟨Finset.Subset.refl _, Finset.subset_union_left⟩
  refine ⟨t, ?_⟩
  refine ⟨(complex f |>.isRelLowerSet_faces s.property).1.mono hst, ?_, ?_⟩
  · simpa only [t, Finset.toLeft_disjSum] using s.property.2.1
  · rw [hull_disjSum]
    have hi : s.val.toLeft.biUnion (fun a => (f.faceImage a).val) ⊆ hull f s.val :=
      Finset.subset_union_right
    rw [Finset.union_eq_left.mpr hi]
    exact s.property.2.2

theorem subset_carrierFace (f : Morphism P Q) (s : Face (complex f)) :
    s.val ⊆ (carrierFace f s).val := by
  classical
  exact Finset.subset_disjSum.mpr ⟨Finset.Subset.refl _, Finset.subset_union_left⟩

/-- The literal inclusion of the original face coordinates in its constructed carrier. -/
def carrierSourceEmbedding (f : Morphism P Q) (s : Face (complex f)) :
    s.val ↪ (carrierFace f s).val where
  toFun a := ⟨a.val, subset_carrierFace f s a.property⟩
  inj' a b h := by
    have hh : a.val = b.val :=
      congrArg (fun c : (carrierFace f s).val => c.val) h
    exact Subtype.ext hh

/-- The target hull coordinates in the same finite carrier face. -/
def carrierTargetEmbedding (f : Morphism P Q) (s : Face (complex f)) :
    (hullFace f s).val ↪ (carrierFace f s).val where
  toFun a := ⟨Sum.inr a.val, Finset.inr_mem_disjSum.mpr a.property⟩
  inj' a b h := by
    have hh : (Sum.inr a.val : Face P ⊕ W) = Sum.inr b.val :=
      congrArg (fun c : (carrierFace f s).val => c.val) h
    exact Subtype.ext (Sum.inr.inj hh)

theorem target_support_carrier (f : Morphism P Q) (s : Face (complex f))
    (x : Realization Q) (hx : x.point.weights.support ⊆ (hullFace f s).val) :
    ((targetMorphism f).realization x).point.weights.support ⊆ (carrierFace f s).val := by
  classical
  rw [targetMorphism_point]
  intro z hz
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hz)
  exact Finset.inr_mem_disjSum.mpr (hx hb)

theorem retraction_support_face (f : Morphism P Q) (s : Face (complex f))
    (q : Convexity.StdSimplex ℝ s.val) :
    (retraction f (Realization.faceMap (complex f) s q)).point.weights.support ⊆
      (hullFace f s).val :=
  (retractionPoint_support f _).trans
    (hull_mono f (Realization.support_map_subtype_subset s.val q))

theorem map_segmentPoint {A : Type u} {B : Type v} (g : A → B) (t : unitInterval)
    (x y : Convexity.StdSimplex ℝ A) :
    (Realization.segmentPoint t x y).map g =
      Realization.segmentPoint t (x.map g) (y.map g) :=
  (Convexity.StdSimplex.isAffineMap_map ℝ g).map_convexCombPair _ _ _ _ _

/-- The straight deformation's actual finite-face coordinates. -/
def deformationCoordinates (f : Morphism P Q) (s : Face (complex f))
    (z : unitInterval × Convexity.StdSimplex ℝ s.val) :
    Convexity.StdSimplex ℝ (carrierFace f s).val :=
  Realization.segmentPoint z.1 (z.2.map (carrierSourceEmbedding f s))
    ((faceRetractionCoordinates f s z.2).map (carrierTargetEmbedding f s))

theorem continuous_deformationCoordinates (f : Morphism P Q) (s : Face (complex f)) :
    Continuous (deformationCoordinates f s) := by
  have hleft : Continuous (fun z : unitInterval × Convexity.StdSimplex ℝ s.val =>
      z.2.map (carrierSourceEmbedding f s)) :=
    (Convexity.StdSimplex.continuous_map ℝ _).comp continuous_snd
  have hright : Continuous (fun z : unitInterval × Convexity.StdSimplex ℝ s.val =>
      (faceRetractionCoordinates f s z.2).map (carrierTargetEmbedding f s)) :=
    (Convexity.StdSimplex.continuous_map ℝ _).comp
      ((continuous_faceRetractionCoordinates f s).comp continuous_snd)
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
    (carrierFace f s).val).continuous_iff.mpr
  apply continuous_pi
  intro a
  change Continuous (fun z : unitInterval × Convexity.StdSimplex ℝ s.val =>
    (Realization.segmentPoint z.1 (z.2.map (carrierSourceEmbedding f s))
      ((faceRetractionCoordinates f s z.2).map (carrierTargetEmbedding f s))).weights a)
  simp only [Realization.segmentPoint_weights, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul]
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    ((Convexity.StdSimplex.continuous_weights_apply ℝ a).comp hleft)).add
    ((continuous_subtype_val.comp continuous_fst).mul
      ((Convexity.StdSimplex.continuous_weights_apply ℝ a).comp hright))

theorem deformationCoordinates_point (f : Morphism P Q) (s : Face (complex f))
    (z : unitInterval × Convexity.StdSimplex ℝ s.val) :
    (deformationCoordinates f s z).map (Subtype.val : (carrierFace f s).val → Face P ⊕ W) =
      Realization.segmentPoint z.1 (Realization.faceMap (complex f) s z.2).point
        ((targetMorphism f).realization
          (retraction f (Realization.faceMap (complex f) s z.2))).point := by
  rw [deformationCoordinates, map_segmentPoint]
  have hleft : (z.2.map (carrierSourceEmbedding f s)).map
      (Subtype.val : (carrierFace f s).val → Face P ⊕ W) =
      (Realization.faceMap (complex f) s z.2).point := by
    rw [Convexity.StdSimplex.map_map]
    rfl
  have hright : ((faceRetractionCoordinates f s z.2).map (carrierTargetEmbedding f s)).map
      (Subtype.val : (carrierFace f s).val → Face P ⊕ W) =
      ((targetMorphism f).realization
        (retraction f (Realization.faceMap (complex f) s z.2))).point := by
    rw [targetMorphism_point, Convexity.StdSimplex.map_map]
    have h := congrArg (Convexity.StdSimplex.map (Sum.inr : W → Face P ⊕ W))
      (faceRetractionCoordinates_point f s z.2)
    rw [Convexity.StdSimplex.map_map] at h
    exact h
  rw [hleft, hright]

/-- The actual straight coordinate deformation, inside the finite carrier
derived from each point's original cylinder face. -/
def deformationPoint (f : Morphism P Q) (z : unitInterval × Realization (complex f)) :
    Realization (complex f) where
  point := Realization.segmentPoint z.1 z.2.point
    ((targetMorphism f).realization (retraction f z.2)).point
  support_mem := by
    classical
    let : DecidableEq (Face P ⊕ W) := Classical.decEq _
    let s : Face (complex f) := ⟨z.2.point.weights.support, z.2.support_mem⟩
    apply ((complex f).isRelLowerSet_faces (carrierFace f s).property).2
    · exact (Realization.segmentPoint_support_subset _ _ _).trans
        (Finset.union_subset (subset_carrierFace f s)
          (target_support_carrier f s (retraction f z.2) (retractionPoint_support f z.2)))
    · exact (Realization.segmentPoint _ _ _).support_weights_nonempty

theorem deformationPoint_faceMap (f : Morphism P Q) (s : Face (complex f))
    (z : unitInterval × Convexity.StdSimplex ℝ s.val) :
    deformationPoint f (z.1, Realization.faceMap (complex f) s z.2) =
      Realization.faceMap (complex f) (carrierFace f s) (deformationCoordinates f s z) := by
  apply Realization.ext
  exact (deformationCoordinates_point f s z).symm

theorem continuous_deformationPoint_faceMap (f : Morphism P Q) (s : Face (complex f)) :
    Continuous (fun z : unitInterval × Convexity.StdSimplex ℝ s.val =>
      deformationPoint f (z.1, Realization.faceMap (complex f) s z.2)) := by
  have heq : (fun z : unitInterval × Convexity.StdSimplex ℝ s.val =>
        deformationPoint f (z.1, Realization.faceMap (complex f) s z.2)) =
      Realization.faceMap (complex f) (carrierFace f s) ∘ deformationCoordinates f s :=
    funext (deformationPoint_faceMap f s)
  rw [heq]
  exact (Realization.continuous_faceMap (complex f) (carrierFace f s)).comp
    (continuous_deformationCoordinates f s)

/-- Joint continuity holds on the ordinary interval product of the entire
possibly infinite cylinder, by its actual weak finite-face topology. -/
theorem continuous_deformationPoint (f : Morphism P Q) : Continuous (deformationPoint f) :=
  continuous_interval_product (complex f) (deformationPoint f)
    (continuous_deformationPoint_faceMap f)

/-- The actual deformation from the identity to the included affine retraction. -/
def deformation (f : Morphism P Q) :
    ContinuousMap.Homotopy (ContinuousMap.id (Realization (complex f)))
      ((targetMorphism f).realization.comp (retraction f)) where
  toFun := deformationPoint f
  continuous_toFun := continuous_deformationPoint f
  map_zero_left x := Realization.ext (Realization.segmentPoint_zero x.point
    ((targetMorphism f).realization (retraction f x)).point)
  map_one_left x := Realization.ext (Realization.segmentPoint_one x.point
    ((targetMorphism f).realization (retraction f x)).point)

/-- Every point of the unchanged target is stationary throughout the deformation. -/
theorem deformation_target_fixed (f : Morphism P Q) (t : unitInterval) (x : Realization Q) :
    deformation f (t, (targetMorphism f).realization x) = (targetMorphism f).realization x := by
  apply Realization.ext
  change Realization.segmentPoint t ((targetMorphism f).realization x).point
    ((targetMorphism f).realization (retraction f ((targetMorphism f).realization x))).point = _
  rw [retraction_target]
  exact Realization.segmentPoint_self _ _

/-- The ordinary deformation is relative to the entire unchanged codomain subcomplex. -/
def deformationRelativeTarget (f : Morphism P Q) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (Realization (complex f)))
      ((targetMorphism f).realization.comp (retraction f))
        (Set.range (targetMorphism f).realization) where
  toHomotopy := deformation f
  prop' t x hx := by
    obtain ⟨y, rfl⟩ := hx
    exact deformation_target_fixed f t y

/-- The terminal domain equation is corrected to the given map literally. -/
theorem deformation_terminal_domain (f : Morphism P Q)
    (x : Realization (barycentricSubdivision P)) :
    deformation f (1, (domainMorphism f).realization x) =
      (targetMorphism f).realization (f.realization (barycentricHomeomorph P x)) := by
  rw [ContinuousMap.Homotopy.apply_one]
  change (targetMorphism f).realization (retraction f ((domainMorphism f).realization x)) = _
  rw [retraction_domain]

theorem finiteFaces_relabelComplex {A : Type u} {B : Type v}
    (T : PreAbstractSimplicialComplex A) [Finite (Face T)] (e : A ↪ B) :
    Finite (Face (relabelComplex T e)) := by
  classical
  let F : Face T → Face (relabelComplex T e) :=
    fun a => ⟨a.val.image e, ⟨a.val, a.property, rfl⟩⟩
  apply Finite.of_surjective F
  rintro ⟨s, hs⟩
  obtain ⟨a, ha, rfl⟩ := hs
  exact ⟨⟨a, ha⟩, rfl⟩

/-- The copied domain retains the actual finite face set, despite ambient ghost labels. -/
theorem finiteFaces_domainComplex (P : PreAbstractSimplicialComplex V) [Finite (Face P)]
    (W : Type v) : Finite (Face (domainComplex P W)) := by
  let := finiteFaces_barycentricSubdivision P
  exact finiteFaces_relabelComplex (barycentricSubdivision P) Function.Embedding.inl

/-- The actual simplicial cone, with a fresh apex retained even for an empty base. -/
def coneComplex {A : Type u} (T : PreAbstractSimplicialComplex A) :
    PreAbstractSimplicialComplex (A ⊕ PUnit.{u + 1}) where
  faces := {s | s.Nonempty ∧ (s.toLeft ∈ T ∨ s.toLeft = ∅)}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    refine ⟨ht, ?_⟩
    by_cases hempty : t.toLeft = ∅
    · exact Or.inr hempty
    · have hnonempty : t.toLeft.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      rcases hs.2 with hs | hs
      · exact Or.inl ((T.isRelLowerSet_faces hs).2
          (Finset.toLeft_subset_toLeft hts) hnonempty)
      · have he := Finset.subset_empty.mp (hs ▸ Finset.toLeft_subset_toLeft hts)
        exact (hempty he).elim

@[simp]
theorem mem_coneComplex {A : Type u} (T : PreAbstractSimplicialComplex A)
    (s : Finset (A ⊕ PUnit)) :
    s ∈ coneComplex T ↔ s.Nonempty ∧ (s.toLeft ∈ T ∨ s.toLeft = ∅) := Iff.rfl

theorem cone_base_face_mem {A : Type u} (T : PreAbstractSimplicialComplex A) (s : Face T) :
    s.val.disjSum (∅ : Finset PUnit) ∈ coneComplex T := by
  refine ⟨?_, Or.inl ?_⟩
  · simpa only [Finset.disjSum_empty, Finset.map_nonempty] using
      (T.isRelLowerSet_faces s.property).1
  · simpa only [Finset.toLeft_disjSum] using s.property

theorem cone_base_le {A : Type u} (T : PreAbstractSimplicialComplex A) :
    relabelComplex T (Function.Embedding.inl : A ↪ A ⊕ PUnit) ≤ coneComplex T := by
  classical
  let : DecidableEq (A ⊕ PUnit) := Classical.decEq _
  intro s hs
  obtain ⟨a, ha, rfl⟩ := hs
  have h := cone_base_face_mem T ⟨a, ha⟩
  rw [Finset.disjSum_empty, Finset.map_eq_image] at h
  exact h

/-- The literal fresh cone apex, with no point of the base chosen. -/
def coneApex {A : Type u} (T : PreAbstractSimplicialComplex A) : Vertex (coneComplex T) :=
  ⟨Sum.inr PUnit.unit, by
    refine ⟨Finset.singleton_nonempty _, Or.inr ?_⟩
    ext a
    simp⟩

/-- Cone faces close under adjoining the fresh apex. -/
theorem cone_insert_apex {A : Type u} [DecidableEq (A ⊕ PUnit)]
    (T : PreAbstractSimplicialComplex A)
    (s : Face (coneComplex T)) : insert (coneApex T).val s.val ∈ coneComplex T := by
  classical
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  have he : (insert (coneApex T).val s.val).toLeft = s.val.toLeft := by
    ext a
    simp [Finset.mem_toLeft, coneApex]
  rw [he]
  exact s.property.2

/-- The actual source-base embedding into its cone. -/
def coneBaseMorphism {A : Type u} (T : PreAbstractSimplicialComplex A) :
    Morphism T (coneComplex T) :=
  (inclusionMorphism (cone_base_le T)).comp (relabelMorphism T Function.Embedding.inl)

theorem isClosedEmbedding_coneBaseMorphism {A : Type u} (T : PreAbstractSimplicialComplex A) :
    IsClosedEmbedding (coneBaseMorphism T).realization := by
  have heq : (fun x => (coneBaseMorphism T).realization x) =
      Realization.inclusion (cone_base_le T) ∘ relabelHomeomorph T Function.Embedding.inl := by
    funext x
    change (coneBaseMorphism T).realizationMap x = _
    rw [coneBaseMorphism, Morphism.realizationMap_comp]
    exact inclusionMorphism_realization _ _
  change IsClosedEmbedding (fun x => (coneBaseMorphism T).realization x)
  rw [heq]
  exact (Realization.isClosedEmbedding_inclusion (cone_base_le T)).comp
    (relabelHomeomorph T Function.Embedding.inl).isClosedEmbedding

/-- The simplicial mapping cone is the actual cylinder with the cone on its
copied barycentric domain attached, using one fresh apex label. -/
def associatedCone (f : Morphism P Q) :
    PreAbstractSimplicialComplex ((Face P ⊕ W) ⊕ PUnit.{max u v + 1}) :=
  relabelComplex (complex f) Function.Embedding.inl ⊔ coneComplex (domainComplex P W)

theorem cone_cylinder_le (f : Morphism P Q) :
    relabelComplex (complex f) (Function.Embedding.inl : Face P ⊕ W ↪ (Face P ⊕ W) ⊕ PUnit) ≤
      associatedCone f := le_sup_left

theorem attachedCone_le (f : Morphism P Q) :
    coneComplex (domainComplex P W) ≤ associatedCone f := le_sup_right

/-- The attached cone meets the cylinder in precisely the copied domain. -/
theorem attachedCone_intersection (f : Morphism P Q) :
    relabelComplex (complex f) Function.Embedding.inl ⊓ coneComplex (domainComplex P W) =
      relabelComplex (domainComplex P W) Function.Embedding.inl := by
  classical
  let : DecidableEq ((Face P ⊕ W) ⊕ PUnit) := Classical.decEq _
  apply le_antisymm
  · intro s hs
    obtain ⟨a, ha, rfl⟩ := hs.1
    have he : (a.image (Function.Embedding.inl : Face P ⊕ W ↪
        (Face P ⊕ W) ⊕ PUnit)).toLeft = a := by
      rw [← Finset.map_eq_image, ← Finset.disjSum_empty, Finset.toLeft_disjSum]
    have hc := hs.2.2
    rw [he] at hc
    rcases hc with hc | hc
    · exact ⟨a, hc, rfl⟩
    · exact ((complex f).isRelLowerSet_faces ha).1.ne_empty hc |>.elim
  · intro s hs
    obtain ⟨a, ha, rfl⟩ := hs
    refine ⟨⟨a, domainComplex_le f ha, rfl⟩, ?_⟩
    have h := cone_base_face_mem (domainComplex P W) ⟨a, ha⟩
    rw [Finset.disjSum_empty, Finset.map_eq_image] at h
    exact h

/-- Weak realization glues the union of two actual subcomplexes along their
intersection, without a local finiteness assumption. -/
def unionDesc {A : Type u} (S T : PreAbstractSimplicialComplex A)
    {Z : Type w} [TopologicalSpace Z] (g : C(Realization S, Z))
    (h : C(Realization T, Z))
    (hag : ∀ x : Realization (S ⊓ T),
      g (Realization.inclusion inf_le_left x) = h (Realization.inclusion inf_le_right x)) :
    C(Realization (S ⊔ T), Z) := by
  classical
  let d : Realization (S ⊔ T) → Z := fun x =>
    if hx : x.point.weights.support ∈ S then g ⟨x.point, hx⟩
    else h ⟨x.point, x.support_mem.resolve_left hx⟩
  have dleft (x : Realization S) : d (Realization.inclusion le_sup_left x) = g x := by
    dsimp [d, Realization.inclusion]
    rw [dite_eq_left x.support_mem]
  have dright (x : Realization T) : d (Realization.inclusion le_sup_right x) = h x := by
    dsimp [d, Realization.inclusion]
    by_cases hx : x.point.weights.support ∈ S
    · rw [dite_eq_left hx]
      exact hag ⟨x.point, hx, x.support_mem⟩
    · rw [dite_eq_right hx]
  refine ⟨d, ?_⟩
  rw [Realization.continuous_iff]
  intro s
  rcases s.property with hs | ht
  · have heq : d ∘ Realization.faceMap (S ⊔ T) s =
        g ∘ Realization.faceMap S ⟨s.val, hs⟩ := by
      funext q
      exact dleft (Realization.faceMap S ⟨s.val, hs⟩ q)
    rw [heq]
    exact g.continuous.comp (Realization.continuous_faceMap S ⟨s.val, hs⟩)
  · have heq : d ∘ Realization.faceMap (S ⊔ T) s =
        h ∘ Realization.faceMap T ⟨s.val, ht⟩ := by
      funext q
      exact dright (Realization.faceMap T ⟨s.val, ht⟩ q)
    rw [heq]
    exact h.continuous.comp (Realization.continuous_faceMap T ⟨s.val, ht⟩)

@[simp]
theorem unionDesc_left {A : Type u} (S T : PreAbstractSimplicialComplex A)
    {Z : Type w} [TopologicalSpace Z] (g : C(Realization S, Z))
    (h : C(Realization T, Z)) (hag) (x : Realization S) :
    unionDesc S T g h hag (Realization.inclusion le_sup_left x) = g x := by
  classical
  change (if hx : x.point.weights.support ∈ S then g ⟨x.point, hx⟩ else _) = _
  rw [dite_eq_left x.support_mem]

@[simp]
theorem unionDesc_right {A : Type u} (S T : PreAbstractSimplicialComplex A)
    {Z : Type w} [TopologicalSpace Z] (g : C(Realization S, Z))
    (h : C(Realization T, Z)) (hag) (x : Realization T) :
    unionDesc S T g h hag (Realization.inclusion le_sup_right x) = h x := by
  classical
  change (if hx : x.point.weights.support ∈ S then g ⟨x.point, hx⟩ else _) = _
  by_cases hx : x.point.weights.support ∈ S
  · rw [dite_eq_left hx]
    exact hag ⟨x.point, hx, x.support_mem⟩
  · rw [dite_eq_right hx]
    rfl

/-- Maps out of the actual weak union are uniquely determined on its two
subcomplexes. Together with `unionDesc`, this is its pushout property. -/
theorem unionDesc_unique {A : Type u} (S T : PreAbstractSimplicialComplex A)
    {Z : Type w} [TopologicalSpace Z] (g : C(Realization S, Z))
    (h : C(Realization T, Z)) (hag) (m : C(Realization (S ⊔ T), Z))
    (hl : ∀ x : Realization S, m (Realization.inclusion le_sup_left x) = g x)
    (hr : ∀ x : Realization T, m (Realization.inclusion le_sup_right x) = h x) :
    m = unionDesc S T g h hag := by
  ext x
  rcases x.support_mem with hs | ht
  · exact (hl ⟨x.point, hs⟩).trans (unionDesc_left S T g h hag ⟨x.point, hs⟩).symm
  · exact (hr ⟨x.point, ht⟩).trans (unionDesc_right S T g h hag ⟨x.point, ht⟩).symm

/-- An actual finite base has an actual finite cone, independently of unused
ambient labels; the isolated apex also exists when the base is empty. -/
theorem finiteFaces_coneComplex {A : Type u} (T : PreAbstractSimplicialComplex A)
    [Finite (Face T)] : Finite (Face (coneComplex T)) := by
  classical
  let : Fintype (Face T) := Fintype.ofFinite _
  let b : Finset A := Finset.univ.biUnion (fun s : Face T => s.val)
  let c : Finset (A ⊕ PUnit) := b.disjSum Finset.univ
  have bound (s : Face (coneComplex T)) : s.val ⊆ c := by
    rw [Finset.subset_disjSum]
    refine ⟨?_, Finset.subset_univ _⟩
    rcases s.property.2 with hs | hs
    · exact Finset.subset_biUnion_of_mem (fun t : Face T => t.val)
        (Finset.mem_univ (⟨s.val.toLeft, hs⟩ : Face T))
    · rw [hs]
      exact Finset.empty_subset _
  let e : Face (coneComplex T) → {s // s ∈ c.powerset} :=
    fun s => ⟨s.val, Finset.mem_powerset.mpr (bound s)⟩
  exact Finite.of_injective e (fun s t h =>
    Subtype.ext (congrArg (fun z : {s // s ∈ c.powerset} => z.val) h))

/-- The actual cone attached to a finite copied domain is finite. -/
theorem finiteFaces_attachedCone (P : PreAbstractSimplicialComplex V) [Finite (Face P)]
    (W : Type v) : Finite (Face (coneComplex (domainComplex P W))) := by
  let := finiteFaces_domainComplex P W
  exact finiteFaces_coneComplex (domainComplex P W)

/-- The cylinder is a closed, literally relabeled subcomplex of its associated cone. -/
def cylinderToCone (f : Morphism P Q) : Morphism (complex f) (associatedCone f) :=
  (inclusionMorphism (cone_cylinder_le f)).comp
    (relabelMorphism (complex f) Function.Embedding.inl)

/-- The cone on the copied domain is included in the actual associated cone. -/
def attachedConeMorphism (f : Morphism P Q) :
    Morphism (coneComplex (domainComplex P W)) (associatedCone f) :=
  inclusionMorphism (attachedCone_le f)

theorem cylinderToCone_point (f : Morphism P Q) (x : Realization (complex f)) :
    ((cylinderToCone f).realization x).point = x.point.map Sum.inl := by
  change ((cylinderToCone f).realizationMap x).point = _
  rw [cylinderToCone, Morphism.realizationMap_comp]
  change ((inclusionMorphism (cone_cylinder_le f)).realization
    ((relabelMorphism (complex f) Function.Embedding.inl).realization x)).point = _
  rw [inclusionMorphism_point]
  exact relabelMorphism_point _ _ _

theorem attachedConeMorphism_point (f : Morphism P Q)
    (x : Realization (coneComplex (domainComplex P W))) :
    ((attachedConeMorphism f).realization x).point = x.point :=
  inclusionMorphism_point _ _

theorem isClosedEmbedding_cylinderToCone (f : Morphism P Q) :
    IsClosedEmbedding (cylinderToCone f).realization := by
  have heq : (fun x => (cylinderToCone f).realization x) =
      Realization.inclusion (cone_cylinder_le f) ∘
        relabelHomeomorph (complex f) Function.Embedding.inl := by
    funext x
    change (cylinderToCone f).realizationMap x = _
    rw [cylinderToCone, Morphism.realizationMap_comp]
    exact inclusionMorphism_realization _ _
  change IsClosedEmbedding (fun x => (cylinderToCone f).realization x)
  rw [heq]
  exact (Realization.isClosedEmbedding_inclusion (cone_cylinder_le f)).comp
    (relabelHomeomorph (complex f) Function.Embedding.inl).isClosedEmbedding

theorem isClosedEmbedding_attachedConeMorphism (f : Morphism P Q) :
    IsClosedEmbedding (attachedConeMorphism f).realization := by
  have heq : (fun x => (attachedConeMorphism f).realization x) =
      Realization.inclusion (attachedCone_le f) := by
    funext x
    exact inclusionMorphism_realization _ _
  change IsClosedEmbedding (fun x => (attachedConeMorphism f).realization x)
  rw [heq]
  exact Realization.isClosedEmbedding_inclusion _

/-- The source-base map on the actual cone and the copied-domain map on the
cylinder agree literally in the associated cone. -/
theorem associatedCone_base_agreement (f : Morphism P Q)
    (x : Realization (domainComplex P W)) :
    (cylinderToCone f).realization (Realization.inclusion (domainComplex_le f) x) =
      (attachedConeMorphism f).realization
        ((coneBaseMorphism (domainComplex P W)).realization x) := by
  apply Realization.ext
  rw [cylinderToCone_point, Realization.inclusion_point, attachedConeMorphism_point]
  change _ = ((coneBaseMorphism (domainComplex P W)).realizationMap x).point
  rw [coneBaseMorphism, Morphism.realizationMap_comp]
  change _ = ((inclusionMorphism (cone_base_le (domainComplex P W))).realization
    ((relabelMorphism (domainComplex P W) Function.Embedding.inl).realization x)).point
  rw [inclusionMorphism_point]
  exact (relabelMorphism_point (domainComplex P W) Function.Embedding.inl x).symm

/-- The given domain is identified with the actual copied barycentric domain. -/
def copiedDomainHomeomorph (f : Morphism P Q) :
    Realization P ≃ₜ Set.range (domainMorphism f).realization :=
  (barycentricHomeomorph P).symm.trans
    (isClosedEmbedding_domainMorphism f).isEmbedding.toHomeomorph

@[simp]
theorem copiedDomainHomeomorph_coe (f : Morphism P Q) (x : Realization P) :
    (copiedDomainHomeomorph f x).val =
      (domainMorphism f).realization ((barycentricHomeomorph P).symm x) := rfl

/-- A supplied triangulation identification is retained literally on the
constructed copied domain; it plays no role in constructing the cylinder. -/
def copiedTriangulation {X : Type w} [TopologicalSpace X]
    (f : Morphism P Q) (σ : X ≃ₜ Realization P) :
    X ≃ₜ Set.range (domainMorphism f).realization := σ.trans (copiedDomainHomeomorph f)

@[simp]
theorem copiedTriangulation_retraction {X : Type w} [TopologicalSpace X]
    (f : Morphism P Q) (σ : X ≃ₜ Realization P) (x : X) :
    retraction f (copiedTriangulation f σ x).val = f.realization (σ x) := by
  change retraction f ((domainMorphism f).realization ((barycentricHomeomorph P).symm (σ x))) = _
  rw [retraction_domain, Homeomorph.apply_symm_apply]

/-- The ordinary topological pushout of two weak subcomplex realizations is
their actual union realization. -/
theorem isPushout_union {A : Type u} (S T : PreAbstractSimplicialComplex A) :
    CategoryTheory.IsPushout
      (TopCat.ofHom (inclusionMorphism (inf_le_left : S ⊓ T ≤ S)).realization)
      (TopCat.ofHom (inclusionMorphism (inf_le_right : S ⊓ T ≤ T)).realization)
      (TopCat.ofHom (inclusionMorphism (le_sup_left : S ≤ S ⊔ T)).realization)
      (TopCat.ofHom (inclusionMorphism (le_sup_right : T ≤ S ⊔ T)).realization) := by
  let comm : CategoryTheory.CommSq
      (TopCat.ofHom (inclusionMorphism (inf_le_left : S ⊓ T ≤ S)).realization)
      (TopCat.ofHom (inclusionMorphism (inf_le_right : S ⊓ T ≤ T)).realization)
      (TopCat.ofHom (inclusionMorphism (le_sup_left : S ≤ S ⊔ T)).realization)
      (TopCat.ofHom (inclusionMorphism (le_sup_right : T ≤ S ⊔ T)).realization) := by
    refine ⟨?_⟩
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    apply Realization.ext
    change (((inclusionMorphism le_sup_left).realization
      ((inclusionMorphism inf_le_left).realization x))).point =
        (((inclusionMorphism le_sup_right).realization
          ((inclusionMorphism inf_le_right).realization x))).point
    simp only [inclusionMorphism_point]
  apply CategoryTheory.IsPushout.of_isColimit' comm
  apply CategoryTheory.Limits.PushoutCocone.isColimitAux'
  intro s
  have hag (x : Realization (S ⊓ T)) :
      s.inl (Realization.inclusion inf_le_left x) =
        s.inr (Realization.inclusion inf_le_right x) := by
    have h := CategoryTheory.ConcreteCategory.congr_hom s.condition x
    change s.inl ((inclusionMorphism inf_le_left).realization x) =
      s.inr ((inclusionMorphism inf_le_right).realization x) at h
    simpa only [TopCat.ofHom_apply, inclusionMorphism_realization] using h
  let d := TopCat.ofHom (unionDesc S T s.inl.hom s.inr.hom hag)
  refine ⟨d, ?_, ?_, ?_⟩
  · ext x
    change unionDesc S T s.inl.hom s.inr.hom hag
      ((inclusionMorphism le_sup_left).realization x) = s.inl x
    rw [inclusionMorphism_realization]
    exact unionDesc_left S T _ _ _ x
  · ext x
    change unionDesc S T s.inl.hom s.inr.hom hag
      ((inclusionMorphism le_sup_right).realization x) = s.inr x
    rw [inclusionMorphism_realization]
    exact unionDesc_right S T _ _ _ x
  · intro m hl hr
    apply TopCat.hom_ext
    exact unionDesc_unique S T s.inl.hom s.inr.hom hag m.hom
      (fun x => by
        have h := CategoryTheory.ConcreteCategory.congr_hom hl x
        change m ((inclusionMorphism le_sup_left).realization x) = s.inl x at h
        rw [inclusionMorphism_realization] at h
        exact h)
      (fun x => by
        have h := CategoryTheory.ConcreteCategory.congr_hom hr x
        change m ((inclusionMorphism le_sup_right).realization x) = s.inr x at h
        rw [inclusionMorphism_realization] at h
        exact h)

theorem copiedDomainCone_cylinder_le (f : Morphism P Q) :
    relabelComplex (domainComplex P W) Function.Embedding.inl ≤
      relabelComplex (complex f) (Function.Embedding.inl :
        Face P ⊕ W ↪ (Face P ⊕ W) ⊕ PUnit.{max u v + 1}) := by
  rw [← attachedCone_intersection f]
  exact inf_le_left

theorem isPushout_union_of_intersection {A : Type u}
    (S T B : PreAbstractSimplicialComplex A) (hB : S ⊓ T = B)
    (hl : B ≤ S) (hr : B ≤ T) :
    CategoryTheory.IsPushout
      (TopCat.ofHom (inclusionMorphism hl).realization)
      (TopCat.ofHom (inclusionMorphism hr).realization)
      (TopCat.ofHom (inclusionMorphism (le_sup_left : S ≤ S ⊔ T)).realization)
      (TopCat.ofHom (inclusionMorphism (le_sup_right : T ≤ S ⊔ T)).realization) := by
  subst B
  exact isPushout_union S T

/-- The associated cone is the ordinary realization pushout obtained by
attaching the actual simplicial cone along the literal copied domain. -/
theorem isPushout_associatedCone (f : Morphism P Q) :
    CategoryTheory.IsPushout
      (TopCat.ofHom (inclusionMorphism (copiedDomainCone_cylinder_le f)).realization)
      (TopCat.ofHom (inclusionMorphism (cone_base_le (domainComplex P W))).realization)
      (TopCat.ofHom (inclusionMorphism (cone_cylinder_le f)).realization)
      (TopCat.ofHom (inclusionMorphism (attachedCone_le f)).realization) := by
  exact isPushout_union_of_intersection _ _ _ (attachedCone_intersection f) _ _

/-- Straight interpolation is jointly continuous inside each actual finite simplex. -/
theorem continuous_segmentPoint_finite {A : Type u} [Finite A]
    {Z : Type w} [TopologicalSpace Z] (τ : Z → unitInterval)
    (a b : Z → Convexity.StdSimplex ℝ A) (hτ : Continuous τ)
    (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun z => Realization.segmentPoint (τ z) (a z) (b z)) := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ A).continuous_iff.mpr
  apply continuous_pi
  intro i
  change Continuous (fun z => (Realization.segmentPoint (τ z) (a z) (b z)).weights i)
  simp only [Realization.segmentPoint_weights, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  exact ((continuous_const.sub (continuous_subtype_val.comp hτ)).mul
    ((Convexity.StdSimplex.continuous_weights_apply ℝ i).comp ha)).add
    ((continuous_subtype_val.comp hτ).mul
      ((Convexity.StdSimplex.continuous_weights_apply ℝ i).comp hb))

/-- The ordinary cone parameter has literal base and fresh-apex coordinates. -/
def coneParameterPoint {A : Type u} (T : PreAbstractSimplicialComplex A)
    (z : unitInterval × Realization T) : Realization (coneComplex T) where
  point := Realization.segmentPoint z.1 ((coneBaseMorphism T).realization z.2).point
    (Convexity.StdSimplex.single (coneApex T).val)
  support_mem := by
    classical
    let : DecidableEq (A ⊕ PUnit) := Classical.decEq _
    let x := (coneBaseMorphism T).realization z.2
    let s : Face (coneComplex T) := ⟨x.point.weights.support, x.support_mem⟩
    apply ((coneComplex T).isRelLowerSet_faces (cone_insert_apex T s)).2
    · apply (Realization.segmentPoint_support_subset _ _ _).trans
      apply Finset.union_subset (Finset.subset_insert _ _)
      rw [Convexity.StdSimplex.support_weights_eq_singleton.mpr rfl]
      exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
    · exact (Realization.segmentPoint _ _ _).support_weights_nonempty

theorem continuous_coneParameterPoint {A : Type u} (T : PreAbstractSimplicialComplex A) :
    Continuous (coneParameterPoint T) := by
  classical
  apply continuous_interval_product T
  intro s
  let x := (coneBaseMorphism T).faceImage s
  let c : Face (coneComplex T) := ⟨insert (coneApex T).val x.val, cone_insert_apex T x⟩
  let b : s.val → c.val := fun a =>
    ⟨((coneBaseMorphism T).faceVertexMap s a).val,
      Finset.mem_insert_of_mem ((coneBaseMorphism T).faceVertexMap s a).property⟩
  let apex : c.val := ⟨(coneApex T).val, Finset.mem_insert_self _ _⟩
  let F : unitInterval × Convexity.StdSimplex ℝ s.val → Convexity.StdSimplex ℝ c.val :=
    fun z => Realization.segmentPoint z.1 (z.2.map b) (Convexity.StdSimplex.single apex)
  have hF : Continuous F := continuous_segmentPoint_finite _ _ _ continuous_fst
    ((Convexity.StdSimplex.continuous_map ℝ b).comp continuous_snd) continuous_const
  have heq : (fun z : unitInterval × Convexity.StdSimplex ℝ s.val =>
      coneParameterPoint T (z.1, Realization.faceMap T s z.2)) =
      Realization.faceMap (coneComplex T) c ∘ F := by
    funext z
    apply Realization.ext
    change Realization.segmentPoint z.1
      ((coneBaseMorphism T).realization (Realization.faceMap T s z.2)).point
        (Convexity.StdSimplex.single (coneApex T).val) =
      (F z).map (Subtype.val : c.val → A ⊕ PUnit)
    dsimp only [F]
    rw [map_segmentPoint, Convexity.StdSimplex.map_map, Convexity.StdSimplex.map_single]
    congr 1
    change ((coneBaseMorphism T).realizationMap (Realization.faceMap T s z.2)).point = _
    rw [coneBaseMorphism, Morphism.realizationMap_comp]
    change ((inclusionMorphism (cone_base_le T)).realization
      ((relabelMorphism T Function.Embedding.inl).realization
        (Realization.faceMap T s z.2))).point = _
    rw [inclusionMorphism_point, relabelMorphism_point]
    change (z.2.map (Subtype.val : s.val → A)).map Sum.inl = _
    rw [Convexity.StdSimplex.map_map]
    rfl
  rw [heq]
  exact (Realization.continuous_faceMap (coneComplex T) c).comp hF

/-- The actual ordinary cone parameter, constructed without a nonempty base. -/
def coneParameter {A : Type u} (T : PreAbstractSimplicialComplex A) :
    C(unitInterval × Realization T, Realization (coneComplex T)) :=
  ⟨coneParameterPoint T, continuous_coneParameterPoint T⟩

@[simp]
theorem coneParameter_zero {A : Type u} (T : PreAbstractSimplicialComplex A)
    (x : Realization T) : coneParameter T (0, x) = (coneBaseMorphism T).realization x :=
  Realization.ext (Realization.segmentPoint_zero _ _)

@[simp]
theorem coneParameter_one {A : Type u} (T : PreAbstractSimplicialComplex A)
    (x : Realization T) : coneParameter T (1, x) =
      Realization.vertex (coneComplex T) (coneApex T).val (coneApex T).property :=
  Realization.ext (Realization.segmentPoint_one _ _)

theorem coneBaseMorphism_point {A : Type u} (T : PreAbstractSimplicialComplex A)
    (x : Realization T) : ((coneBaseMorphism T).realization x).point = x.point.map Sum.inl := by
  change ((coneBaseMorphism T).realizationMap x).point = _
  rw [coneBaseMorphism, Morphism.realizationMap_comp]
  change ((inclusionMorphism (cone_base_le T)).realization
    ((relabelMorphism T Function.Embedding.inl).realization x)).point = _
  rw [inclusionMorphism_point]
  exact relabelMorphism_point T Function.Embedding.inl x

/-- The base part of a cone point is normalized only when it has nonzero base
weight. Its membership is derived from the actual cone face. -/
def normalizedConeBaseRelabel {A : Type u} (T : PreAbstractSimplicialComplex A)
    (x : Realization (coneComplex T))
    (hx : ∃ a : A, x.point.weights (Sum.inl a) ≠ 0) :
    Realization (relabelComplex T (Function.Embedding.inl : A ↪ A ⊕ PUnit)) := by
  classical
  let : DecidableEq (A ⊕ PUnit) := Classical.decEq _
  let L : Set (A ⊕ PUnit) := {a | a ≠ (coneApex T).val}
  have hL : ∃ a ∈ L, x.point.weights a ≠ 0 := by
    obtain ⟨a, ha⟩ := hx
    exact ⟨Sum.inl a, Sum.inl_ne_inr, ha⟩
  let q := x.point.restrict L hL
  have hface : x.point.weights.support.toLeft ∈ T := by
    rcases x.support_mem.2 with h | h
    · exact h
    · obtain ⟨a, ha⟩ := hx
      have hm : a ∈ x.point.weights.support.toLeft :=
        Finset.mem_toLeft.mpr (Finsupp.mem_support_iff.mpr ha)
      rw [h] at hm
      exact (Finset.notMem_empty _ hm).elim
  have hsupport : q.weights.support =
      x.point.weights.support.toLeft.image (Function.Embedding.inl : A ↪ A ⊕ PUnit) := by
    rw [Convexity.StdSimplex.support_weights_restrict]
    ext a
    cases a with
    | inl a => simp [L, coneApex, Finset.mem_toLeft]
    | inr a => cases a; simp [L, coneApex]
  exact ⟨q, hsupport ▸ ⟨x.point.weights.support.toLeft, hface, rfl⟩⟩

/-- The base point obtained from the derived nonzero normalized base coordinates. -/
def normalizedConeBase {A : Type u} (T : PreAbstractSimplicialComplex A)
    (x : Realization (coneComplex T))
    (hx : ∃ a : A, x.point.weights (Sum.inl a) ≠ 0) : Realization T :=
  (relabelHomeomorph T Function.Embedding.inl).symm (normalizedConeBaseRelabel T x hx)

theorem normalizedConeBase_point {A : Type u} (T : PreAbstractSimplicialComplex A)
    (x : Realization (coneComplex T)) (hx)
    (hL : ∃ a ∈ {a | a ≠ (coneApex T).val}, x.point.weights a ≠ 0) :
    ((coneBaseMorphism T).realization (normalizedConeBase T x hx)).point =
      x.point.restrict {a | a ≠ (coneApex T).val} hL := by
  classical
  rw [coneBaseMorphism_point]
  have h := congrArg Realization.point
    ((relabelHomeomorph T Function.Embedding.inl).apply_symm_apply
      (normalizedConeBaseRelabel T x hx))
  change ((relabelMorphism T Function.Embedding.inl).realization
    (normalizedConeBase T x hx)).point = _ at h
  rw [relabelMorphism_point] at h
  exact h

/-- Normalizing the nonzero base part gives the actual radial presentation
of every nonapex cone point. -/
theorem coneParameter_normalizedConeBase {A : Type u} (T : PreAbstractSimplicialComplex A)
    (x : Realization (coneComplex T)) (hx : ∃ a : A, x.point.weights (Sum.inl a) ≠ 0) :
    coneParameter T (⟨x.point.weights (coneApex T).val,
      x.point.weights_nonneg _, x.point.weights_apply_le_one _⟩,
        normalizedConeBase T x hx) = x := by
  classical
  let L : Set (A ⊕ PUnit) := {a | a ≠ (coneApex T).val}
  have hL : ∃ a ∈ L, x.point.weights a ≠ 0 := by
    obtain ⟨a, ha⟩ := hx
    exact ⟨Sum.inl a, Sum.inl_ne_inr, ha⟩
  have hfilter : x.point.weights.filter (fun a => a ∉ L) =
      Finsupp.single (coneApex T).val (x.point.weights (coneApex T).val) := by
    ext a
    simp only [Finsupp.filter_apply, Finsupp.single_apply, L, Set.mem_ofPred_eq, not_not]
    split_ifs <;> simp_all [eq_comm]
  have hmass : (x.point.weights.filter (· ∈ L)).sum (fun _ r => r) =
      1 - x.point.weights (coneApex T).val := by
    have h := Finsupp.sum_filter_add_sum_filter_not (· ∈ L) x.point.weights (fun _ r => r)
    rw [hfilter] at h
    simpa only [Finsupp.sum_single_index, zero_add, x.point.total] using eq_sub_of_add_eq h
  apply Realization.ext
  change Realization.segmentPoint _
    ((coneBaseMorphism T).realization (normalizedConeBase T x hx)).point
      (Convexity.StdSimplex.single (coneApex T).val) = x.point
  rw [normalizedConeBase_point T x hx hL]
  by_cases ha : x.point.weights (coneApex T).val = 0
  · have he : x.point.restrict L hL = x.point := by
      apply Convexity.StdSimplex.ext
      rw [Convexity.StdSimplex.weights_restrict, hmass, ha]
      simp only [sub_zero, inv_one, one_smul]
      apply (Finsupp.filter_eq_self_iff _ _).mpr
      intro a h
      exact fun he => h (he ▸ ha)
    rw [he]
    have ht : (⟨x.point.weights (coneApex T).val,
        x.point.weights_nonneg _, x.point.weights_apply_le_one _⟩ : unitInterval) = 0 :=
      Subtype.ext ha
    rw [ht, Realization.segmentPoint_zero]
  · have hLc : ∃ a ∈ Lᶜ, x.point.weights a ≠ 0 :=
      ⟨(coneApex T).val, by simp [L], ha⟩
    have he : x.point.restrict Lᶜ hLc = Convexity.StdSimplex.single (coneApex T).val := by
      have hset : Lᶜ = {(coneApex T).val} := by ext a; simp [L]
      simp only [hset, Convexity.StdSimplex.restrict_singleton]
    have h := congrArg Convexity.StdSimplex.weights
      (Convexity.StdSimplex.convexCombPair_restrict_restrict_compl x.point L hL hLc)
    rw [he] at h
    apply Convexity.StdSimplex.ext
    simpa only [Convexity.StdSimplex.weights_convexCombPair, Realization.segmentPoint_weights,
      hmass, hfilter, Finsupp.sum_single_index] using h

/-- A cone point is either the fresh apex or has its derived base-and-height
presentation. No base point is chosen when the base is empty. -/
theorem coneParameter_or_apex {A : Type u} (T : PreAbstractSimplicialComplex A)
    (x : Realization (coneComplex T)) :
    (∃ z, coneParameter T z = x) ∨
      x = Realization.vertex (coneComplex T) (coneApex T).val (coneApex T).property := by
  classical
  by_cases hx : ∃ a : A, x.point.weights (Sum.inl a) ≠ 0
  · exact Or.inl ⟨_, coneParameter_normalizedConeBase T x hx⟩
  · right
    apply Realization.ext
    apply Convexity.StdSimplex.support_weights_eq_singleton.mp
    apply Finset.Subset.antisymm
    · intro a ha
      cases a with
      | inl a => exact (hx ⟨a, Finsupp.mem_support_iff.mp ha⟩).elim
      | inr a => cases a; exact Finset.mem_singleton_self _
    · obtain ⟨a, ha⟩ := x.point.support_weights_nonempty
      cases a with
      | inl a => exact (hx ⟨a, Finsupp.mem_support_iff.mp ha⟩).elim
      | inr a => cases a; exact Finset.singleton_subset_iff.mpr ha

/-- The characteristic interval map into the actual simplicial cone. -/
def coneCylinderToRealization {A : Type u} (T : PreAbstractSimplicialComplex A) :
    TopCat.of (Realization T) ⊗ TopCat.I.{u} ⟶ TopCat.of (Realization (coneComplex T)) :=
  TopCat.ofHom ⟨fun z => coneParameter T (TopCat.I.homeomorph z.2, z.1),
      (coneParameter T).continuous.comp
        ((TopCat.I.homeomorph.continuous.comp continuous_snd).prodMk continuous_fst)⟩

/-- The characteristic point summand at the actual fresh cone apex. -/
def coneApexToRealization {A : Type u} (T : PreAbstractSimplicialComplex A) :
    TopCat.of PUnit.{u + 1} ⟶ TopCat.of (Realization (coneComplex T)) :=
  TopCat.ofHom (ContinuousMap.const _
    (Realization.vertex (coneComplex T) (coneApex T).val (coneApex T).property))

/-- The actual simplicial cone comparison is induced by the ordinary
topological cone's characteristic quotient. -/
def ordinaryConeToRealization {A : Type u} (T : PreAbstractSimplicialComplex A) :
    TopCat.cone (TopCat.of (Realization T)) ⟶ TopCat.of (Realization (coneComplex T)) := by
  refine CategoryTheory.Limits.pushout.desc (coneCylinderToRealization T)
    (coneApexToRealization T) ?_
  apply CategoryTheory.ConcreteCategory.hom_ext
  intro x
  change coneParameter T (TopCat.I.homeomorph (1 : TopCat.I.{u}), x) = _
  rw [TopCat.I.homeomorph_one, coneParameter_one]
  rfl

@[simp]
theorem ordinaryConeToRealization_cylinder {A : Type u} (T : PreAbstractSimplicialComplex A)
    (x : Realization T) (t : TopCat.I.{u}) :
    ordinaryConeToRealization T (TopCat.coneCylinder (TopCat.of (Realization T)) (x, t)) =
      coneParameter T (TopCat.I.homeomorph t, x) := by
  change (TopCat.coneCylinder (TopCat.of (Realization T)) ≫ ordinaryConeToRealization T) (x, t) = _
  dsimp only [TopCat.coneCylinder, ordinaryConeToRealization]
  rw [CategoryTheory.Limits.pushout.inl_desc]
  rfl

@[simp]
theorem ordinaryConeToRealization_apex {A : Type u} (T : PreAbstractSimplicialComplex A) :
    ordinaryConeToRealization T
      (TopCat.conePoint (TopCat.of (Realization T)) PUnit.unit) =
        Realization.vertex (coneComplex T) (coneApex T).val (coneApex T).property := by
  change (TopCat.conePoint (TopCat.of (Realization T)) ≫ ordinaryConeToRealization T) PUnit.unit = _
  dsimp only [TopCat.conePoint, ordinaryConeToRealization]
  rw [CategoryTheory.Limits.pushout.inr_desc]
  rfl

theorem ordinaryConeToRealization_surjective {A : Type u} (T : PreAbstractSimplicialComplex A) :
    Function.Surjective (ordinaryConeToRealization T) := by
  intro x
  rcases coneParameter_or_apex T x with ⟨z, hz⟩ | hx
  · refine ⟨TopCat.coneCylinder (TopCat.of (Realization T))
      (z.2, TopCat.I.homeomorph.symm z.1), ?_⟩
    rw [ordinaryConeToRealization_cylinder, Homeomorph.apply_symm_apply, hz]
  · refine ⟨TopCat.conePoint (TopCat.of (Realization T)) PUnit.unit, ?_⟩
    rw [ordinaryConeToRealization_apex, hx]

/-- Ordinary cone points have the actual cylinder-or-apex presentation,
including when there is no point of the base. -/
theorem ordinaryCone_cylinder_or_apex (X : TopCat.{u}) (p : TopCat.cone X) :
    (∃ z, TopCat.coneCylinder X z = p) ∨ p = TopCat.conePoint X PUnit.unit := by
  let hc := CategoryTheory.Limits.isColimitOfPreserves (CategoryTheory.forget TopCat)
    (CategoryTheory.Limits.pushout.isColimit (TopCat.ι₁ : X ⟶ X ⊗ TopCat.I)
      (TopCat.isTerminalPUnit.from X))
  obtain ⟨j, x, hx⟩ := CategoryTheory.Limits.Types.jointly_surjective_of_isColimit hc p
  cases j with
  | none =>
    change X at x
    left
    let c := CategoryTheory.Limits.pushout.cocone (TopCat.ι₁ : X ⟶ X ⊗ TopCat.I)
      (TopCat.isTerminalPUnit.from X)
    have hzero : c.ι.app CategoryTheory.Limits.WalkingSpan.zero =
        TopCat.ι₁ ≫ TopCat.coneCylinder X :=
      (c.ι.naturality CategoryTheory.Limits.WalkingSpan.Hom.fst).symm
    change c.ι.app CategoryTheory.Limits.WalkingSpan.zero x = p at hx
    rw [hzero] at hx
    exact ⟨(x, 1), hx⟩
  | some j =>
    cases j with
    | left => exact Or.inl ⟨x, hx⟩
    | right =>
      change PUnit at x
      cases x
      exact Or.inr hx.symm

theorem coneParameter_weight_apex {A : Type u} (T : PreAbstractSimplicialComplex A)
    (z : unitInterval × Realization T) :
    (coneParameter T z).point.weights (coneApex T).val = (z.1 : ℝ) := by
  change (Realization.segmentPoint z.1 ((coneBaseMorphism T).realization z.2).point
    (Convexity.StdSimplex.single (coneApex T).val)).weights (coneApex T).val = _
  rw [Realization.segmentPoint_weights, coneBaseMorphism_point]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Convexity.StdSimplex.weights_single, Finsupp.single_eq_same, mul_one]
  have he : (z.2.point.map (Sum.inl : A → A ⊕ PUnit)).weights (coneApex T).val = 0 :=
    Finsupp.mapDomain_of_notMem_range _ _ (by simp [coneApex])
  rw [he, mul_zero, zero_add]

theorem coneParameter_weight_base {A : Type u} (T : PreAbstractSimplicialComplex A)
    (z : unitInterval × Realization T) (a : A) :
    (coneParameter T z).point.weights (Sum.inl a) = (1 - (z.1 : ℝ)) * z.2.point.weights a := by
  change (Realization.segmentPoint z.1 ((coneBaseMorphism T).realization z.2).point
    (Convexity.StdSimplex.single (coneApex T).val)).weights (Sum.inl a) = _
  rw [Realization.segmentPoint_weights, coneBaseMorphism_point]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Convexity.StdSimplex.weights_single]
  rw [Finsupp.single_eq_of_ne (by simp [coneApex]), mul_zero, add_zero]
  congr 1
  exact Finsupp.mapDomain_apply_of_injective Sum.inl_injective _ _

theorem coneParameter_eq_apex_iff {A : Type u} (T : PreAbstractSimplicialComplex A)
    (t : unitInterval) (x : Realization T) :
    coneParameter T (t, x) =
      Realization.vertex (coneComplex T) (coneApex T).val (coneApex T).property ↔ t = 1 := by
  constructor
  · intro h
    apply Subtype.ext
    change (t : ℝ) = 1
    have ht := congrArg (fun z : Realization (coneComplex T) => z.point.weights (coneApex T).val) h
    rw [coneParameter_weight_apex] at ht
    simpa only [Realization.vertex, Convexity.StdSimplex.weights_single,
      Finsupp.single_eq_same] using ht
  · rintro rfl
    exact coneParameter_one T x

theorem coneParameter_injective_below_apex {A : Type u} (T : PreAbstractSimplicialComplex A)
    (t : unitInterval) (ht : t ≠ 1) : Function.Injective (fun x => coneParameter T (t, x)) := by
  intro x y h
  apply Realization.ext
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro a
  have hw := congrArg (fun z : Realization (coneComplex T) => z.point.weights (Sum.inl a)) h
  rw [coneParameter_weight_base, coneParameter_weight_base] at hw
  have hc : 1 - (t : ℝ) ≠ 0 := by
    intro he
    apply ht
    exact Subtype.ext (sub_eq_zero.mp he).symm
  exact mul_left_cancel₀ hc hw

/-- The ordinary cone quotient comparison is injective, with no nonempty-base
hypothesis: height distinguishes the apex and the remaining base weights. -/
theorem ordinaryConeToRealization_injective {A : Type u} (T : PreAbstractSimplicialComplex A) :
    Function.Injective (ordinaryConeToRealization T) := by
  intro x y h
  rcases ordinaryCone_cylinder_or_apex (TopCat.of (Realization T)) x with ⟨⟨a, t⟩, rfl⟩ | hx
  · rcases ordinaryCone_cylinder_or_apex (TopCat.of (Realization T)) y with ⟨⟨b, s⟩, rfl⟩ | hy
    · rw [ordinaryConeToRealization_cylinder, ordinaryConeToRealization_cylinder] at h
      have hts : t = s := by
        apply TopCat.I.homeomorph.injective
        apply Subtype.ext
        have hh := congrArg
          (fun z : Realization (coneComplex T) => z.point.weights (coneApex T).val) h
        simpa only [coneParameter_weight_apex] using hh
      subst s
      by_cases ht : t = 1
      · subst t
        rw [TopCat.coneCylinder_eq_conePoint_of_snd_eq_one _ _ rfl,
          TopCat.coneCylinder_eq_conePoint_of_snd_eq_one _ _ rfl]
      · have ht' : TopCat.I.homeomorph t ≠ 1 := by
          intro he
          apply ht
          apply TopCat.I.homeomorph.injective
          simpa only [TopCat.I.homeomorph_one] using he
        have hab := coneParameter_injective_below_apex T _ ht' h
        rw [hab]
    · rw [hy, ordinaryConeToRealization_cylinder, ordinaryConeToRealization_apex] at h
      have ht : t = 1 := by
        apply TopCat.I.homeomorph.injective
        simpa only [TopCat.I.homeomorph_one] using (coneParameter_eq_apex_iff T _ _).mp h
      exact (TopCat.coneCylinder_eq_conePoint_of_snd_eq_one _ _ ht).trans hy.symm
  · rcases ordinaryCone_cylinder_or_apex (TopCat.of (Realization T)) y with ⟨⟨b, s⟩, rfl⟩ | hy
    · rw [hx, ordinaryConeToRealization_apex, ordinaryConeToRealization_cylinder] at h
      have hs : s = 1 := by
        apply TopCat.I.homeomorph.injective
        simpa only [TopCat.I.homeomorph_one] using (coneParameter_eq_apex_iff T _ _).mp h.symm
      exact hx.trans (TopCat.coneCylinder_eq_conePoint_of_snd_eq_one _ _ hs).symm
    · exact hx.trans hy.symm

/-- A finite weak base has a compact ordinary cone, also for the empty base. -/
theorem compactSpace_ordinaryCone {A : Type u} (T : PreAbstractSimplicialComplex A)
    [Finite (Face T)] : CompactSpace (TopCat.cone (TopCat.of (Realization T))) := by
  let X := TopCat.of (Realization T)
  let : CompactSpace TopCat.I.{u} :=
    Function.Surjective.compactSpace TopCat.I.homeomorph.symm.continuous
      TopCat.I.homeomorph.symm.surjective
  let : CompactSpace X := inferInstanceAs (CompactSpace (Realization T))
  let : CompactSpace (↑(X ⊗ TopCat.I.{u})) :=
    inferInstanceAs (CompactSpace (X × TopCat.I.{u}))
  let H := TopCat.coprodHomeomorphSum (X ⊗ TopCat.I) (TopCat.of PUnit)
  let : CompactSpace (↑((X ⊗ TopCat.I) ⨿ TopCat.of PUnit)) :=
    Function.Surjective.compactSpace H.symm.continuous H.symm.surjective
  exact Function.Surjective.compactSpace
    (CategoryTheory.Limits.coprod.desc
      (TopCat.coneCylinder X) (TopCat.conePoint X)).hom.continuous
    (TopCat.pushoutCoproductMap_isQuotientMap
      (TopCat.ι₁ : X ⟶ X ⊗ TopCat.I) (TopCat.isTerminalPUnit.from X)).surjective

/-- The actual finite simplicial cone realizes the ordinary cone, with its
canonical quotient comparison as the homeomorphism. -/
def ordinaryConeHomeomorph {A : Type u} (T : PreAbstractSimplicialComplex A)
    [Finite (Face T)] : TopCat.cone (TopCat.of (Realization T)) ≃ₜ Realization (coneComplex T) := by
  let := compactSpace_ordinaryCone T
  let e := Equiv.ofBijective (ordinaryConeToRealization T)
    ⟨ordinaryConeToRealization_injective T, ordinaryConeToRealization_surjective T⟩
  exact e.toHomeomorphOfContinuousClosed (ordinaryConeToRealization T).hom.continuous
    (ordinaryConeToRealization T).hom.continuous.isClosedMap

@[simp]
theorem ordinaryConeHomeomorph_base {A : Type u} (T : PreAbstractSimplicialComplex A)
    [Finite (Face T)] (x : Realization T) :
    ordinaryConeHomeomorph T (TopCat.coneBase (TopCat.of (Realization T)) x) =
      (coneBaseMorphism T).realization x := by
  change ordinaryConeToRealization T (TopCat.coneCylinder (TopCat.of (Realization T)) (x, 0)) = _
  rw [ordinaryConeToRealization_cylinder, TopCat.I.homeomorph_zero, coneParameter_zero]

@[simp]
theorem ordinaryConeHomeomorph_apex {A : Type u} (T : PreAbstractSimplicialComplex A)
    [Finite (Face T)] :
    ordinaryConeHomeomorph T (TopCat.conePoint (TopCat.of (Realization T)) PUnit.unit) =
      Realization.vertex (coneComplex T) (coneApex T).val (coneApex T).property :=
  ordinaryConeToRealization_apex T

/-- The ordinary cone on the actual copied domain is included by the
constructed cone homeomorphism and actual cone subcomplex embedding. -/
def ordinaryConeAttachment (f : Morphism P Q) [Finite (Face P)] :
    C(TopCat.cone (TopCat.of (Realization (domainComplex P W))),
      Realization (associatedCone f)) := by
  let := finiteFaces_domainComplex P W
  exact (attachedConeMorphism f).realization.comp
    ⟨ordinaryConeHomeomorph (domainComplex P W),
      (ordinaryConeHomeomorph (domainComplex P W)).continuous⟩

@[simp]
theorem ordinaryConeAttachment_base (f : Morphism P Q) [Finite (Face P)]
    (x : Realization (domainComplex P W)) :
    ordinaryConeAttachment f (TopCat.coneBase (TopCat.of (Realization (domainComplex P W))) x) =
      (cylinderToCone f).realization (Realization.inclusion (domainComplex_le f) x) := by
  let := finiteFaces_domainComplex P W
  change (attachedConeMorphism f).realization
    (ordinaryConeHomeomorph (domainComplex P W)
      (TopCat.coneBase (TopCat.of (Realization (domainComplex P W))) x)) = _
  rw [ordinaryConeHomeomorph_base]
  exact (associatedCone_base_agreement f x).symm

/-- The exact ordinary attachment square uses the actual copied domain and
the actual ordinary cone, with no replacement span supplied. -/
theorem isPushout_ordinaryConeAttachment (f : Morphism P Q) [Finite (Face P)] :
    CategoryTheory.IsPushout
      (TopCat.ofHom (inclusionMorphism (domainComplex_le f)).realization)
      (TopCat.coneBase (TopCat.of (Realization (domainComplex P W))))
      (TopCat.ofHom (cylinderToCone f).realization)
      (TopCat.ofHom (ordinaryConeAttachment f)) := by
  let := finiteFaces_domainComplex P W
  let e1 : TopCat.of (Realization (domainComplex P W)) ≅
      TopCat.of (Realization (relabelComplex (domainComplex P W)
        (Function.Embedding.inl : Face P ⊕ W ↪ (Face P ⊕ W) ⊕ PUnit))) :=
    TopCat.isoOfHomeo (relabelHomeomorph (domainComplex P W) Function.Embedding.inl)
  let e2 : TopCat.of (Realization (complex f)) ≅
      TopCat.of (Realization (relabelComplex (complex f)
        (Function.Embedding.inl : Face P ⊕ W ↪ (Face P ⊕ W) ⊕ PUnit))) :=
    TopCat.isoOfHomeo (relabelHomeomorph (complex f) Function.Embedding.inl)
  let e3 : TopCat.cone (TopCat.of (Realization (domainComplex P W))) ≅
      TopCat.of (Realization (coneComplex (domainComplex P W))) :=
    TopCat.isoOfHomeo (ordinaryConeHomeomorph (domainComplex P W))
  refine (isPushout_associatedCone f).of_iso' e1 e2 e3 (CategoryTheory.Iso.refl _) ?_ ?_ ?_ ?_
  · apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    apply Realization.ext
    change ((inclusionMorphism (copiedDomainCone_cylinder_le f)).realization
      (relabelHomeomorph (domainComplex P W) Function.Embedding.inl x)).point =
        (relabelHomeomorph (complex f) Function.Embedding.inl
          ((inclusionMorphism (domainComplex_le f)).realization x)).point
    rw [inclusionMorphism_point]
    change ((relabelMorphism _ _).realization x).point =
      ((relabelMorphism _ _).realization ((inclusionMorphism _).realization x)).point
    rw [relabelMorphism_point, relabelMorphism_point, inclusionMorphism_point]
  · apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    apply Realization.ext
    change ((inclusionMorphism (cone_base_le (domainComplex P W))).realization
      (relabelHomeomorph (domainComplex P W) Function.Embedding.inl x)).point =
        (ordinaryConeHomeomorph (domainComplex P W)
          (TopCat.coneBase (TopCat.of (Realization (domainComplex P W))) x)).point
    rw [inclusionMorphism_point, ordinaryConeHomeomorph_base, coneBaseMorphism_point]
    exact relabelMorphism_point _ _ _
  · apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    apply Realization.ext
    change ((inclusionMorphism (cone_cylinder_le f)).realization
      (relabelHomeomorph (complex f) Function.Embedding.inl x)).point =
        ((cylinderToCone f).realization x).point
    rw [inclusionMorphism_point, cylinderToCone_point]
    exact relabelMorphism_point _ _ _
  · apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    change (inclusionMorphism (attachedCone_le f)).realization
      (ordinaryConeHomeomorph (domainComplex P W) x) = ordinaryConeAttachment f x
    rfl

/-- The actual sphere boundary of a classical cell keeps its supplied finite
triangulation identification on the copied domain. The max-norm sphere and
the empty zero-dimensional boundary are literal. -/
def copiedSphereBoundary (f : Morphism P Q) (n : ℕ)
    (σ : Metric.sphere (0 : Fin n → ℝ) 1 ≃ₜ Realization P) :
    Metric.sphere (0 : Fin n → ℝ) 1 ≃ₜ Set.range (domainMorphism f).realization :=
  copiedTriangulation f σ

@[simp]
theorem copiedSphereBoundary_coe (f : Morphism P Q) (n : ℕ)
    (σ : Metric.sphere (0 : Fin n → ℝ) 1 ≃ₜ Realization P)
    (x : Metric.sphere (0 : Fin n → ℝ) 1) :
    (copiedSphereBoundary f n σ x).val =
      (domainMorphism f).realization ((barycentricHomeomorph P).symm (σ x)) := rfl

theorem copiedSphereBoundary_retraction (f : Morphism P Q) (n : ℕ)
    (σ : Metric.sphere (0 : Fin n → ℝ) 1 ≃ₜ Realization P)
    (x : Metric.sphere (0 : Fin n → ℝ) 1) :
    retraction f (copiedSphereBoundary f n σ x).val = f.realization (σ x) :=
  copiedTriangulation_retraction f σ x

/-- The actual two ends of the cylinder are disjoint, even for a folding map. -/
theorem domain_target_disjoint (f : Morphism P Q) :
    Disjoint (Set.range (domainMorphism f).realization)
      (Set.range (targetMorphism f).realization) := by
  rw [Set.disjoint_left]
  rintro x ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨v, hv⟩ := a.point.support_weights_nonempty
  have h := congrArg (fun z : Realization (complex f) => z.point.weights (Sum.inl v))
    (ha.trans hb.symm)
  rw [domainMorphism_point, targetMorphism_point] at h
  have he : (b.point.map (Sum.inr : W → Face P ⊕ W)).weights (Sum.inl v) = 0 :=
    Finsupp.mapDomain_of_notMem_range _ _ (by simp)
  rw [he] at h
  have hl : (a.point.map (Sum.inl : Face P → Face P ⊕ W)).weights (Sum.inl v) = a.point.weights v :=
    Finsupp.mapDomain_apply_of_injective Sum.inl_injective _ _
  rw [hl] at h
  exact (Finsupp.mem_support_iff.mp hv) h

/-- The unchanged target also embeds as a closed subcomplex of the associated cone. -/
def targetToConeMorphism (f : Morphism P Q) : Morphism Q (associatedCone f) :=
  (cylinderToCone f).comp (targetMorphism f)

theorem isClosedEmbedding_targetToConeMorphism (f : Morphism P Q) :
    IsClosedEmbedding (targetToConeMorphism f).realization := by
  have heq : (fun x => (targetToConeMorphism f).realization x) =
      (cylinderToCone f).realization ∘ (targetMorphism f).realization := by
    funext x
    exact Morphism.realizationMap_comp _ _ x
  change IsClosedEmbedding (fun x => (targetToConeMorphism f).realization x)
  rw [heq]
  exact (isClosedEmbedding_cylinderToCone f).comp (isClosedEmbedding_targetMorphism f)

/-- Finite-domain geometry is derived for the actual construction: the copied
domain and attached cone are finite and both cylinder ends are genuine disjoint
closed embeddings. Ambient vertex types may still be infinite or empty. -/
theorem finiteDomain_geometry (f : Morphism P Q) [Finite (Face P)] :
    Finite (Face (domainComplex P W)) ∧
      Finite (Face (coneComplex (domainComplex P W))) ∧
      IsClosedEmbedding (domainMorphism f).realization ∧
      IsClosedEmbedding (targetMorphism f).realization ∧
      Disjoint (Set.range (domainMorphism f).realization)
        (Set.range (targetMorphism f).realization) :=
  ⟨finiteFaces_domainComplex P W, finiteFaces_attachedCone P W,
    isClosedEmbedding_domainMorphism f, isClosedEmbedding_targetMorphism f,
      domain_target_disjoint f⟩

end MappingCylinder
end PreAbstractSimplicialComplex

end
