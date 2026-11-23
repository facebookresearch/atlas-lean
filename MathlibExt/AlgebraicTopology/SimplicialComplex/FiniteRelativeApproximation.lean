/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.Morphism
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationCompactSupport
public import MathlibExt.Topology.MetricSpace.CompactCover

/-!
# Finite carriers and vertex stars of weak polyhedra

Finiteness means finitely many actual faces, allowing arbitrary unused
ambient labels. Compact subsets of an arbitrary weak polyhedron have finite
vertex support, obtained from compact support in its face-poset realization.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology
open scoped Simplicial

universe u v w

namespace PreAbstractSimplicialComplex

variable {V : Type u} {W : Type v}

/-- The actual subcomplex supported on a specified finite vertex set. -/
def restrictVertices (P : PreAbstractSimplicialComplex V) (s : Finset V) :
    PreAbstractSimplicialComplex V where
  faces := {t | t ∈ P ∧ t ⊆ s}
  isRelLowerSet_faces := by
    intro t ht
    exact ⟨(P.isRelLowerSet_faces ht.1).1, fun r hrt hr =>
      ⟨(P.isRelLowerSet_faces ht.1).2 hrt hr, hrt.trans ht.2⟩⟩

theorem restrictVertices_le (P : PreAbstractSimplicialComplex V) (s : Finset V) :
    restrictVertices P s ≤ P := fun _ ht => ht.1

/-- A finite vertex restriction has finitely many actual faces. -/
instance (P : PreAbstractSimplicialComplex V) (s : Finset V) :
    Finite (Face (restrictVertices P s)) := by
  classical
  exact Finite.of_injective
    (fun t : Face (restrictVertices P s) =>
      (⟨t.val, Finset.mem_powerset.mpr t.property.2⟩ : s.powerset))
    (by intro a b hab; exact Subtype.ext (congrArg (fun z : s.powerset => z.val) hab))

/-- Finitely many actual faces imply finitely many belonging vertices. -/
instance (P : PreAbstractSimplicialComplex V) [Finite (Face P)] : Finite (Vertex P) :=
  Finite.of_injective (fun v : Vertex P => (⟨{v.val}, v.property⟩ : Face P)) (by
    intro a b h
    have hs : ({a.val} : Finset V) = {b.val} := congrArg (fun s : Face P => s.val) h
    exact Subtype.ext (Finset.singleton_injective hs))

/-- The actual subcomplex consisting of faces contained in a face incident to the vertex. -/
def vertexStar (P : PreAbstractSimplicialComplex V) (v : Vertex P) :
    PreAbstractSimplicialComplex V := by
  classical
  exact
    { faces := {s | s ∈ P ∧ insert v.val s ∈ P}
      isRelLowerSet_faces := fun _ hs =>
        ⟨(P.isRelLowerSet_faces hs.1).1, fun t hts ht =>
          ⟨(P.isRelLowerSet_faces hs.1).2 hts ht,
            (P.isRelLowerSet_faces hs.2).2 (Finset.insert_subset_insert v.val hts)
              (Finset.insert_nonempty _ _)⟩⟩ }

theorem vertexStar_le (P : PreAbstractSimplicialComplex V) (v : Vertex P) :
    vertexStar P v ≤ P := by
  classical
  intro t hs
  change t ∈ P ∧ insert v.val t ∈ P at hs
  exact hs.1

namespace Realization

variable {P : PreAbstractSimplicialComplex V}

/-- A finite weak polyhedron is compact, including the empty complex. -/
instance (P : PreAbstractSimplicialComplex V) [Finite (Face P)] :
    CompactSpace (Realization P) := by
  have hcover : (⋃ s : Face P, Set.range (faceMap P s)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr
      ⟨⟨x.point.weights.support, x.support_mem⟩, mem_range_support_face x⟩
  exact isCompact_univ_iff.mp
    (hcover ▸ isCompact_iUnion (fun s : Face P => isCompact_range (continuous_faceMap P s)))

/-- For a finite complex, the coordinate injection is a genuine closed embedding. -/
theorem isClosedEmbedding_weights (P : PreAbstractSimplicialComplex V) [Finite (Face P)] :
    IsClosedEmbedding (fun x : Realization P => (x.point.weights : V → ℝ)) :=
  (continuous_pi (continuous_weight P)).isClosedEmbedding (by
    intro a b h
    exact Realization.ext (Convexity.StdSimplex.ext (Finsupp.ext (congr_fun h))))

/-- The finite complex's weak topology agrees with its coordinate topology. -/
theorem continuous_iff_weights [Finite (Face P)] {X : Type*} [TopologicalSpace X]
    (f : X → Realization P) :
    Continuous f ↔ ∀ v : V, Continuous (fun x => (f x).point.weights v) := by
  rw [(isClosedEmbedding_weights P).isEmbedding.continuous_iff, continuous_pi_iff]
  rfl

/-- Finite polyhedra embed by their coordinates on actual belonging vertices. -/
theorem isClosedEmbedding_vertexWeights (P : PreAbstractSimplicialComplex V)
    [Finite (Face P)] :
    IsClosedEmbedding (fun x : Realization P =>
      (fun v : Vertex P => x.point.weights v.val)) :=
  (continuous_pi (fun v : Vertex P => continuous_weight P v.val)).isClosedEmbedding (by
    intro a b h
    have hs : vertexCoordinates a = vertexCoordinates b :=
      Convexity.StdSimplex.ext (Finsupp.ext (congr_fun h))
    have hm := congrArg (Convexity.StdSimplex.map (Subtype.val : Vertex P → V)) hs
    rw [map_vertexCoordinates, map_vertexCoordinates] at hm
    exact Realization.ext hm)

/-- The finite coordinate metric preserves the actual weak topology via the
proved actual-vertex embedding. It imposes no topology on an infinite complex. -/
@[instance_reducible]
def finiteCoordinateMetricSpace (P : PreAbstractSimplicialComplex V) [Finite (Face P)] :
    MetricSpace (Realization P) := by
  letI := Fintype.ofFinite (Vertex P)
  exact (isClosedEmbedding_vertexWeights P).isEmbedding.comapMetricSpace
    (fun x : Realization P => (fun v : Vertex P => x.point.weights v.val))

/-- Distance is exactly the finite supremum coordinate distance on belonging vertices. -/
theorem finiteCoordinateMetricSpace_dist [Finite (Face P)] (x y : Realization P) :
    letI := Fintype.ofFinite (Vertex P)
    letI := finiteCoordinateMetricSpace P
    dist x y = dist (fun v : Vertex P => x.point.weights v.val)
      (fun v : Vertex P => y.point.weights v.val) := rfl

/-- The literal open star of a belonging vertex. -/
def openStar (P : PreAbstractSimplicialComplex V) (v : Vertex P) : Set (Realization P) :=
  {x | 0 < x.point.weights v.val}

theorem isOpen_openStar (P : PreAbstractSimplicialComplex V) (v : Vertex P) :
    IsOpen (openStar P v) :=
  isOpen_lt continuous_const (continuous_weight P v.val)

/-- Actual vertex stars cover the entire weak polyhedron. -/
theorem iUnion_openStar (P : PreAbstractSimplicialComplex V) :
    (⋃ v : Vertex P, openStar P v) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨v, hv⟩ := x.point.support_weights_nonempty
  exact Set.mem_iUnion.mpr ⟨⟨v, support_vertex x hv⟩,
    lt_of_le_of_ne (x.point.weights_nonneg v) (Finsupp.mem_support_iff.mp hv).symm⟩

/-- The actual closed star is the image of its incident-face subcomplex. -/
def closedStar (P : PreAbstractSimplicialComplex V) (v : Vertex P) : Set (Realization P) :=
  Set.range (inclusion (vertexStar_le P v))

open Classical in
theorem mem_closedStar_iff (v : Vertex P) (x : Realization P) :
    x ∈ closedStar P v ↔ insert v.val x.point.weights.support ∈ P := by
  rw [closedStar, mem_range_inclusion_iff]
  change (x.point.weights.support ∈ P ∧ insert v.val x.point.weights.support ∈ P) ↔ _
  exact and_iff_right x.support_mem

theorem isClosed_closedStar (v : Vertex P) : IsClosed (closedStar P v) :=
  (isClosedEmbedding_inclusion (vertexStar_le P v)).isClosed_range

theorem openStar_subset_closedStar (v : Vertex P) : openStar P v ⊆ closedStar P v := by
  classical
  intro x hx
  rw [mem_closedStar_iff, Finset.insert_eq_of_mem (Finsupp.mem_support_iff.mpr (ne_of_gt hx))]
  exact x.support_mem

/-- Every face incident to the vertex is contained in its actual closed star. -/
theorem faceMap_mem_closedStar (v : Vertex P) (s : Face P) (hv : v.val ∈ s.val)
    (q : Convexity.StdSimplex ℝ s.val) : faceMap P s q ∈ closedStar P v := by
  classical
  rw [mem_closedStar_iff]
  exact (P.isRelLowerSet_faces s.property).2
    (Finset.insert_subset hv (support_map_subtype_subset s.val q))
    (Finset.insert_nonempty _ _)

/-- The closed star is precisely the union of the closed faces incident to its vertex. -/
theorem closedStar_eq_iUnion_faces (v : Vertex P) :
    closedStar P v = ⋃ s : {s : Face P // v.val ∈ s.val}, Set.range (faceMap P s.val) := by
  classical
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · intro hx
    let s : Face P := ⟨insert v.val x.point.weights.support, (mem_closedStar_iff v x).mp hx⟩
    exact ⟨⟨s, Finset.mem_insert_self _ _⟩,
      (mem_range_faceMap_iff s x).mpr (Finset.subset_insert _ _)⟩
  · rintro ⟨s, q, rfl⟩
    exact faceMap_mem_closedStar v s.val s.property q

/-- An image of a closed vertex star has diameter at most twice the face mesh.
The metric is on the target; the source retains its original weak topology. -/
theorem diam_image_closedStar_le {X : Type w} [MetricSpace X]
    (f : C(Realization P, X)) {r : ℝ} (hr : 0 ≤ r)
    (hmesh : ∀ s : Face P, Metric.diam (f '' Set.range (faceMap P s)) ≤ r)
    (v : Vertex P) : Metric.diam (f '' closedStar P v) ≤ 2 * r := by
  let c := f (vertex P v.val v.property)
  have hrad : ∀ x ∈ f '' closedStar P v, dist x c ≤ r := by
    rintro x ⟨y, hy, rfl⟩
    rw [closedStar_eq_iUnion_faces] at hy
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hy
    have hv : vertex P v.val v.property ∈ Set.range (faceMap P s.val) := by
      refine ⟨Convexity.StdSimplex.single ⟨v.val, s.property⟩, ?_⟩
      apply Realization.ext
      exact Convexity.StdSimplex.map_single _ _
    exact (Metric.dist_le_diam_of_mem
      ((isCompact_range (continuous_faceMap P s.val)).image f.continuous).isBounded
      ⟨y, hs, rfl⟩ ⟨vertex P v.val v.property, hv, rfl⟩).trans (hmesh s.val)
  apply Metric.diam_le_of_forall_dist_le (mul_nonneg (by norm_num) hr)
  intro x hx y hy
  calc
    dist x y ≤ dist x c + dist c y := dist_triangle x c y
    _ ≤ r + r := add_le_add (hrad x hx) (by simpa only [dist_comm] using hrad y hy)
    _ = 2 * r := by ring

open Classical in
/-- Intersecting finitely many vertex stars produces a face, allowing repeated labels. -/
theorem face_of_mem_openStars (s : Finset (Vertex P)) (hs : s.Nonempty)
    (x : Realization P) (hx : ∀ v ∈ s, x ∈ openStar P v) :
    s.image (Subtype.val : Vertex P → V) ∈ P := by
  classical
  apply (P.isRelLowerSet_faces x.support_mem).2
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Finsupp.mem_support_iff.mpr (ne_of_gt (hx w hw))
  · exact Finset.image_nonempty.mpr hs

/-- The global affine comparison evaluates every nondegenerate chain by its actual mixture. -/
theorem affineHomeomorph_sigmaToTop (s : (faceNerve P).N)
    (q : Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :
    (affineHomeomorph P (SSet.sigmaToTop (faceNerve P) ⟨s, q⟩)).point =
      chainPoint s.simplex q :=
  congrArg Realization.point (affineToTop_cell P s.simplex q)

/-- Compact subsets of an arbitrary weak polyhedron have finite actual vertex support.
The finite support is derived from compact support in the face-poset nerve. -/
theorem exists_finite_vertex_support_of_isCompact (K : Set (Realization P))
    (hK : IsCompact K) :
    ∃ t : Finset V, ∀ x ∈ K, x.point.weights.support ⊆ t := by
  classical
  let e := affineHomeomorph P
  obtain ⟨A, hAfinite, hA⟩ := SSet.exists_finite_subcomplex_of_isCompact (faceNerve P)
    (e.symm '' K) (hK.image e.symm.continuous)
  let := hAfinite
  let := Fintype.ofFinite (SSet.Subcomplex.AmbientCells A)
  let t : Finset V := Finset.univ.biUnion
    (fun a : SSet.Subcomplex.AmbientCells A =>
      (a.val.simplex.obj (Fin.last a.val.dim)).val)
  refine ⟨t, ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := hA ⟨x, hx, rfl⟩
  obtain ⟨z, hz⟩ := SSet.surjective_sigmaToTop (A : SSet.{u}) y
  let s := SSet.Subcomplex.mapCarrier A z.1
  have hs : s.subcomplex ≤ A := by
    rw [SSet.Subcomplex.mem_ambientCells_iff]
    exact z.1.simplex.property
  have heq : e (SSet.sigmaToTop (faceNerve P) ⟨s, z.2⟩) = x := by
    rw [SSet.Subcomplex.sigmaToTop_mapCarrier, hz, hy]
    exact e.apply_symm_apply x
  have hsupport : x.point.weights.support ⊆ (s.simplex.obj (Fin.last s.dim)).val := by
    rw [← heq]
    change (affineHomeomorph P (SSet.sigmaToTop (faceNerve P) ⟨s, z.2⟩)).point.weights.support ⊆ _
    rw [affineHomeomorph_sigmaToTop s z.2]
    exact chainPoint_support_subset s.simplex z.2
  exact hsupport.trans (Finset.subset_biUnion_of_mem
    (fun a : SSet.Subcomplex.AmbientCells A =>
      (a.val.simplex.obj (Fin.last a.val.dim)).val) (Finset.mem_univ ⟨s, hs⟩))

/-- The compact subset lies in the actual closed inclusion of a finite abstract subcomplex. -/
theorem exists_finite_vertex_subcomplex_of_isCompact (K : Set (Realization P))
    (hK : IsCompact K) :
    ∃ t : Finset V, K ⊆ Set.range (inclusion (restrictVertices_le P t)) := by
  obtain ⟨t, ht⟩ := exists_finite_vertex_support_of_isCompact K hK
  exact ⟨t, fun x hx => (mem_range_inclusion_iff (restrictVertices_le P t) x).mpr
    ⟨x.support_mem, ht x hx⟩⟩

/-- A compact continuous family factors through a derived finite vertex restriction,
with literal equality after inclusion. The source universe is arbitrary. -/
theorem exists_finite_vertex_factor {X : Type v} [TopologicalSpace X] [CompactSpace X]
    (f : C(X, Realization P)) :
    ∃ t : Finset V, ∃ g : C(X, Realization (restrictVertices P t)),
      ∀ x, inclusion (restrictVertices_le P t) (g x) = f x := by
  obtain ⟨t, ht⟩ := exists_finite_vertex_support_of_isCompact
    (Set.range f) (isCompact_range f.continuous)
  let g : X → Realization (restrictVertices P t) :=
    fun x => ⟨(f x).point, (f x).support_mem, ht (f x) ⟨x, rfl⟩⟩
  have hg : Continuous g :=
    (isClosedEmbedding_inclusion (restrictVertices_le P t)).isEmbedding.continuous_iff.mpr
      f.continuous
  exact ⟨t, ⟨g, hg⟩, fun _ => rfl⟩

/-- The literal straight barycentric segment between two finite distributions. -/
def segmentPoint (t : unitInterval) (a b : Convexity.StdSimplex ℝ V) :
    Convexity.StdSimplex ℝ V :=
  Convexity.convexCombPair (1 - (t : ℝ)) (t : ℝ)
    (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ)) a b

theorem segmentPoint_weights (t : unitInterval) (a b : Convexity.StdSimplex ℝ V) :
    (segmentPoint t a b).weights = (1 - (t : ℝ)) • a.weights + (t : ℝ) • b.weights :=
  Convexity.StdSimplex.weights_convexCombPair _ _ _ _ _ _ _

open Classical in
/-- The segment is supported in the union of its endpoint supports. -/
theorem segmentPoint_support_subset (t : unitInterval) (a b : Convexity.StdSimplex ℝ V) :
    (segmentPoint t a b).weights.support ⊆ a.weights.support ∪ b.weights.support := by
  classical
  rw [segmentPoint_weights]
  exact Finsupp.support_add.trans
    (Finset.union_subset_union Finsupp.support_smul Finsupp.support_smul)

theorem segmentPoint_zero (a b : Convexity.StdSimplex ℝ V) : segmentPoint 0 a b = a := by
  apply Convexity.StdSimplex.ext
  rw [segmentPoint_weights]
  change (1 - (0 : ℝ)) • a.weights + (0 : ℝ) • b.weights = a.weights
  simp only [sub_zero, one_smul, zero_smul, add_zero]

theorem segmentPoint_one (a b : Convexity.StdSimplex ℝ V) : segmentPoint 1 a b = b := by
  apply Convexity.StdSimplex.ext
  rw [segmentPoint_weights]
  change (1 - (1 : ℝ)) • a.weights + (1 : ℝ) • b.weights = b.weights
  simp only [sub_self, zero_smul, one_smul, zero_add]

theorem segmentPoint_self (t : unitInterval) (a : Convexity.StdSimplex ℝ V) :
    segmentPoint t a a = a :=
  Convexity.convexCombPair_same _ _ _

/-- A straight carrier homotopy on a compact domain, for an arbitrary weak target.
Joint continuity is proved through a finite target restriction derived from the first map.
The carrier condition says the second support lies in the first point's actual face. -/
def carrierHomotopy {X : Type v} [TopologicalSpace X] [CompactSpace X]
    (f g : C(X, Realization P))
    (h : ∀ x, (g x).point.weights.support ⊆ (f x).point.weights.support) :
    ContinuousMap.Homotopy f g := by
  classical
  let bound := exists_finite_vertex_support_of_isCompact
    (Set.range f) (isCompact_range f.continuous)
  let t := Classical.choose bound
  have ht : ∀ x, (f x).point.weights.support ⊆ t :=
    fun x => Classical.choose_spec bound (f x) ⟨x, rfl⟩
  have hsupport (z : unitInterval × X) :
      (segmentPoint z.1 (f z.2).point (g z.2).point).weights.support ⊆
        (f z.2).point.weights.support :=
    (segmentPoint_support_subset z.1 (f z.2).point (g z.2).point).trans
      (Finset.union_subset (Finset.Subset.refl _) (h z.2))
  let H : unitInterval × X → Realization (restrictVertices P t) := fun z =>
    ⟨segmentPoint z.1 (f z.2).point (g z.2).point,
      (P.isRelLowerSet_faces (f z.2).support_mem).2 (hsupport z)
        (segmentPoint z.1 (f z.2).point (g z.2).point).support_weights_nonempty,
      (hsupport z).trans (ht z.2)⟩
  have hH : Continuous H := by
    rw [continuous_iff_weights]
    intro v
    change Continuous (fun z : unitInterval × X =>
      (segmentPoint z.1 (f z.2).point (g z.2).point).weights v)
    simp only [segmentPoint_weights, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_weight P v).comp (f.continuous.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((continuous_weight P v).comp (g.continuous.comp continuous_snd)))
  refine
    { toFun := inclusion (restrictVertices_le P t) ∘ H
      continuous_toFun := (continuous_inclusion (restrictVertices_le P t)).comp hH
      map_zero_left := ?_
      map_one_left := ?_ }
  · intro x
    apply Realization.ext
    exact segmentPoint_zero (f x).point (g x).point
  · intro x
    apply Realization.ext
    exact segmentPoint_one (f x).point (g x).point

/-- The constructed continuous homotopy has the literal affine coordinate formula. -/
theorem carrierHomotopy_point {X : Type v} [TopologicalSpace X] [CompactSpace X]
    (f g : C(X, Realization P))
    (h : ∀ x, (g x).point.weights.support ⊆ (f x).point.weights.support)
    (z : unitInterval × X) :
    (carrierHomotopy f g h z).point = segmentPoint z.1 (f z.2).point (g z.2).point := rfl

/-- Any point where the endpoint maps agree stays literally fixed at all times. -/
theorem carrierHomotopy_fixed {X : Type v} [TopologicalSpace X] [CompactSpace X]
    (f g : C(X, Realization P))
    (h : ∀ x, (g x).point.weights.support ⊆ (f x).point.weights.support)
    {x : X} (hx : f x = g x) (t : unitInterval) :
    carrierHomotopy f g h (t, x) = f x := by
  apply Realization.ext
  rw [carrierHomotopy_point, ← hx]
  exact segmentPoint_self t (f x).point

/-- The actual barycenter of a finite face, in its literal finite-face chart. -/
def faceBarycenter (s : Face P) : Realization P := by
  let := (P.isRelLowerSet_faces s.property).1.to_subtype
  exact faceMap P s (Convexity.StdSimplex.barycenter (K := ℝ) (M := s.val))

/-- The face barycenter lies in the open star of every one of its actual vertices. -/
theorem faceBarycenter_mem_openStar (s : Face P) (v : Vertex P)
    (hv : v ∈ faceVertices P s) : faceBarycenter s ∈ openStar P v := by
  classical
  let := (P.isRelLowerSet_faces s.property).1.to_subtype
  have hvs : v.val ∈ s.val := Finset.mem_subtype.mp hv
  change 0 < ((Convexity.StdSimplex.barycenter (K := ℝ) (M := s.val)).map
    (Subtype.val : s.val → V)).weights v.val
  rw [Convexity.StdSimplex.weights_map, Finsupp.mapDomain_apply_of_injective
    Subtype.val_injective _ ⟨v.val, hvs⟩, Convexity.StdSimplex.weights_barycenter_apply]
  exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

/-- A finite chart carries each singleton to the literal corresponding vertex. -/
theorem faceMap_single (s : Face P) (v : s.val) :
    faceMap P s (Convexity.StdSimplex.single v) =
      vertex P v.val (singleton_mem_of_face P s v.property) := by
  apply Realization.ext
  exact Convexity.StdSimplex.map_single _ _

/-- An affine finite-face map sends its barycenter to the centroid of the
actual belonging vertex images, with every source multiplicity retained. -/
theorem faceBarycenter_coordinates_eq_centroid {R : PreAbstractSimplicialComplex W}
    (e : C(Realization R, Realization P)) (s : Face R)
    (haff : Convexity.IsAffineMap ℝ
      (fun q : Convexity.StdSimplex ℝ s.val => (e (faceMap R s q)).point)) :
    (fun w : Vertex P => (e (faceBarycenter s)).point.weights w.val) =
      (faceVertices R s).centroid ℝ (fun v : Vertex R =>
        (fun w : Vertex P => (e (vertex R v.val v.property)).point.weights w.val)) := by
  classical
  let := (R.isRelLowerSet_faces s.property).1.to_subtype
  let q := Convexity.StdSimplex.barycenter (K := ℝ) (M := s.val)
  have heq : (e (faceBarycenter s)).point =
      q.iConvexComb (fun v : s.val =>
        (e (vertex R v.val (singleton_mem_of_face R s v.property))).point) := by
    calc
      (e (faceBarycenter s)).point =
          (fun z : Convexity.StdSimplex ℝ s.val => (e (faceMap R s z)).point)
            (q.iConvexComb Convexity.StdSimplex.single) := by
        rw [Convexity.StdSimplex.iConvexComb_single]
        rfl
      _ = q.iConvexComb
          ((fun z : Convexity.StdSimplex ℝ s.val => (e (faceMap R s z)).point) ∘
            Convexity.StdSimplex.single) := haff.map_iConvexComb _ _
      _ = q.iConvexComb (fun v : s.val =>
          (e (vertex R v.val (singleton_mem_of_face R s v.property))).point) := by
        congr 1
        funext v
        exact congrArg (fun x : Realization R => (e x).point) (faceMap_single s v)
  rw [heq, faceVertices_eq_map_univ, Finset.centroid_map, Finset.centroid_def,
    Finset.affineCombination_eq_linear_combination]
  · ext w
    rw [Convexity.StdSimplex.weights_iConvexComb_apply]
    simp only [Finset.univ_eq_attach, Finset.centroidWeights_apply, Finset.card_attach,
      Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro v hv
    have hw : q.weights v = (s.val.card : ℝ)⁻¹ := by
      simpa only [Fintype.card_coe] using
        (Convexity.StdSimplex.weights_barycenter_apply (K := ℝ) (M := s.val) v)
    rw [hw]
    rfl
  · exact (Finset.univ : Finset s.val).sum_centroidWeights_eq_one_of_nonempty ℝ
      Finset.univ_nonempty

/-- Affine images of a nested face's barycenters satisfy the intrinsic
`N / (N + 1)` mesh contraction, measured in the original finite polyhedron. -/
theorem diam_faceBarycenters_chain_le [Finite (Face P)]
    {R : PreAbstractSimplicialComplex W} (e : C(Realization R, Realization P))
    {d N : ℕ} (faces : Fin (d + 1) → Face R) (hchain : Monotone faces)
    (hcard : (faces (Fin.last d)).val.card ≤ N + 1)
    (haff : ∀ j, Convexity.IsAffineMap ℝ
      (fun q : Convexity.StdSimplex ℝ (faces j).val =>
        (e (faceMap R (faces j) q)).point)) :
    letI := finiteCoordinateMetricSpace P
    Metric.diam (Set.range (fun j => e (faceBarycenter (faces j)))) ≤
      (N : ℝ) / ((N : ℝ) + 1) *
        Metric.diam (e '' Set.range (faceMap R (faces (Fin.last d)))) := by
  classical
  let := Fintype.ofFinite (Vertex P)
  let := finiteCoordinateMetricSpace P
  let weightsMap : Realization P → (Vertex P → ℝ) :=
    fun x v => x.point.weights v.val
  have hi : Isometry weightsMap :=
    Isometry.of_dist_eq (fun x y => finiteCoordinateMetricSpace_dist x y)
  let vertices : Vertex R → (Vertex P → ℝ) :=
    fun v => weightsMap (e (vertex R v.val v.property))
  let vertexFaces : Fin (d + 1) → Finset (Vertex R) :=
    fun j => faceVertices R (faces j)
  have hc : (vertexFaces (Fin.last d)).card ≤ N + 1 := by
    rw [faceVertices_card]
    exact hcard
  have hm : Monotone vertexFaces :=
    fun i j hij => faceVertices_mono R (hchain hij)
  have hG := AlgebraicTopology.diam_faceBarycenters_chain_le_of_card_le
    vertexFaces (fun j => faceVertices_nonempty R (faces j)) hm hc vertices
  have hcentroids : (fun j => (vertexFaces j).centroid ℝ vertices) =
      (fun j => weightsMap (e (faceBarycenter (faces j)))) :=
    funext (fun j => (faceBarycenter_coordinates_eq_centroid e (faces j) (haff j)).symm)
  have hrange : Set.range (fun j => weightsMap (e (faceBarycenter (faces j)))) =
      weightsMap '' Set.range (fun j => e (faceBarycenter (faces j))) :=
    Set.range_comp weightsMap (fun j => e (faceBarycenter (faces j)))
  rw [hcentroids, hrange, hi.diam_image] at hG
  have hsubset : vertices '' (vertexFaces (Fin.last d) : Set (Vertex R)) ⊆
      weightsMap '' (e '' Set.range (faceMap R (faces (Fin.last d)))) := by
    rintro _ ⟨v, hv, rfl⟩
    have hvlabel : v.val ∈ (faces (Fin.last d)).val := Finset.mem_subtype.mp hv
    have hvertex : vertex R v.val v.property ∈ Set.range (faceMap R (faces (Fin.last d))) :=
      ⟨Convexity.StdSimplex.single ⟨v.val, hvlabel⟩, faceMap_single _ _⟩
    exact ⟨e (vertex R v.val v.property), ⟨vertex R v.val v.property, hvertex, rfl⟩, rfl⟩
  have hcompact : IsCompact (weightsMap '' (e '' Set.range
      (faceMap R (faces (Fin.last d))))) :=
    ((isCompact_range (continuous_faceMap R (faces (Fin.last d)))).image e.continuous).image
      hi.continuous
  have hmax := Metric.diam_mono hsubset hcompact.isBounded
  rw [hi.diam_image] at hmax
  exact hG.trans (mul_le_mul_of_nonneg_left hmax (by positivity))

/-- An actual affine simplex image has diameter bounded by its vertex images.
The point formula suffices; no convex structure is imposed on the whole polyhedron. -/
theorem diam_range_affine_le [Finite (Face P)] {I : Type w} [Finite I]
    (F : Convexity.StdSimplex ℝ I → Realization P) (points : I → Realization P)
    (hF : ∀ q, (F q).point = q.iConvexComb (fun i => (points i).point)) :
    letI := finiteCoordinateMetricSpace P
    Metric.diam (Set.range F) ≤ Metric.diam (Set.range points) := by
  let := Fintype.ofFinite I
  let := Fintype.ofFinite (Vertex P)
  let := finiteCoordinateMetricSpace P
  let weightsMap : Realization P → (Vertex P → ℝ) :=
    fun x v => x.point.weights v.val
  have hi : Isometry weightsMap :=
    Isometry.of_dist_eq (fun x y => finiteCoordinateMetricSpace_dist x y)
  let v : I → (Vertex P → ℝ) := weightsMap ∘ points
  have hw (q : Convexity.StdSimplex ℝ I) : weightsMap (F q) = q.iConvexComb v := by
    ext w
    change (F q).point.weights w.val = _
    rw [hF, Convexity.StdSimplex.weights_iConvexComb_apply, Convexity.iConvexComb_eq_sum,
      Finsupp.sum_fintype _ _ (fun _ => by simp)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  have hbounded : Bornology.IsBounded (Set.range v) := (Set.finite_range v).isBounded
  have hmem (q : Convexity.StdSimplex ℝ I) :
      weightsMap (F q) ∈ convexHull ℝ (Set.range v) := by
    rw [hw, Convexity.iConvexComb_eq_sum,
      Finsupp.sum_fintype _ _ (fun _ => by simp)]
    convert affineCombination_mem_convexHull (s := Finset.univ) (v := v)
      (w := fun i => q.weights i) (fun i _ => q.weights_nonneg i) q.total_of_fintype using 1
    rw [Finset.affineCombination_eq_linear_combination]
    exact q.total_of_fintype
  have hdiam : Metric.diam (Set.range v) = Metric.diam (Set.range points) := by
    have hrange : Set.range v = weightsMap '' Set.range points :=
      Set.range_comp weightsMap points
    rw [hrange, hi.diam_image]
  apply Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  calc
    dist (F x) (F y) = dist (weightsMap (F x)) (weightsMap (F y)) :=
      finiteCoordinateMetricSpace_dist _ _
    _ ≤ Metric.diam (convexHull ℝ (Set.range v)) :=
      Metric.dist_le_diam_of_mem (isBounded_convexHull.mpr hbounded) (hmem x) (hmem y)
    _ = Metric.diam (Set.range v) := convexHull_diam _
    _ = Metric.diam (Set.range points) := hdiam

/-- A whole affine barycentric cell shrinks by the intrinsic face-cardinality factor.
This is the metric estimate used with the constructed subdivision chart formulas. -/
theorem diam_range_faceBarycentric_cell_le [Finite (Face P)]
    {R : PreAbstractSimplicialComplex W} (e : C(Realization R, Realization P))
    {d N : ℕ} (faces : Fin (d + 1) → Face R) (hchain : Monotone faces)
    (hcard : (faces (Fin.last d)).val.card ≤ N + 1)
    (haff : ∀ j, Convexity.IsAffineMap ℝ
      (fun q : Convexity.StdSimplex ℝ (faces j).val =>
        (e (faceMap R (faces j) q)).point))
    (F : Convexity.StdSimplex ℝ (Fin (d + 1)) → Realization P)
    (hF : ∀ q, (F q).point =
      q.iConvexComb (fun j => (e (faceBarycenter (faces j))).point)) :
    letI := finiteCoordinateMetricSpace P
    Metric.diam (Set.range F) ≤ (N : ℝ) / ((N : ℝ) + 1) *
      Metric.diam (e '' Set.range (faceMap R (faces (Fin.last d)))) :=
  (diam_range_affine_le F (fun j => e (faceBarycenter (faces j))) hF).trans
    (diam_faceBarycenters_chain_le e faces hchain hcard haff)

/-- A belonging vertex lies in its own literal open star. -/
theorem vertex_mem_openStar (v : Vertex P) :
    vertex P v.val v.property ∈ openStar P v := by
  change 0 < (Convexity.StdSimplex.single (R := ℝ) v.val).weights v.val
  simp

/-- A literal vertex belongs to exactly its own vertex star. -/
theorem vertex_openStar_eq (v w : Vertex P)
    (h : vertex P w.val w.property ∈ openStar P v) : v = w := by
  apply Subtype.ext
  by_contra hne
  change 0 < (Convexity.StdSimplex.single (R := ℝ) w.val).weights v.val at h
  rw [Convexity.StdSimplex.weights_single, Finsupp.single_eq_of_ne hne] at h
  exact (lt_irrefl 0 h)

end Realization

namespace Morphism

variable {P : PreAbstractSimplicialComplex V} {Q : PreAbstractSimplicialComplex W}

/-- An actual vertex function satisfying the open-star condition determines a
genuine simplicial map. The function may identify vertices. -/
def ofStarMap (f : Realization P → Realization Q) (m : Vertex P → Vertex Q)
    (h : ∀ v x, x ∈ Realization.openStar P v → f x ∈ Realization.openStar Q (m v)) :
    Morphism P Q where
  vertexMap := m
  face_mem s := by
    classical
    let x := Realization.faceBarycenter s
    apply (Q.isRelLowerSet_faces (f x).support_mem).2
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact Finsupp.mem_support_iff.mpr
        (ne_of_gt (h v x (Realization.faceBarycenter_mem_openStar s v hv)))
    · exact Finset.image_nonempty.mpr (faceVertices_nonempty P s)

/-- The star condition places every coordinate of the simplicial map in the
actual face carrying the given image point. -/
theorem ofStarMap_support_subset (f : Realization P → Realization Q)
    (m : Vertex P → Vertex Q)
    (h : ∀ v x, x ∈ Realization.openStar P v → f x ∈ Realization.openStar Q (m v))
    (x : Realization P) :
    ((ofStarMap f m h).realization x).point.weights.support ⊆ (f x).point.weights.support := by
  classical
  change (Finsupp.mapDomain (fun v => (m v).val)
    (Realization.vertexCoordinates x).weights).support ⊆ _
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hw)
  have hvpos : x ∈ Realization.openStar P v :=
    lt_of_le_of_ne (x.point.weights_nonneg v.val)
      (Finsupp.mem_support_iff.mp hv).symm
  exact Finsupp.mem_support_iff.mpr (ne_of_gt (h v x hvpos))

/-- A star-conditioned vertex choice gives an actual continuous straight carrier homotopy. -/
def starCarrierHomotopy [Finite (Face P)] (f : C(Realization P, Realization Q))
    (m : Vertex P → Vertex Q)
    (h : ∀ v x, x ∈ Realization.openStar P v → f x ∈ Realization.openStar Q (m v)) :
    ContinuousMap.Homotopy f (ofStarMap f m h).realization :=
  Realization.carrierHomotopy f (ofStarMap f m h).realization (ofStarMap_support_subset f m h)

/-- The star condition forces the given value at every already vertex-valued point. -/
theorem ofStarMap_vertexMap_eq (f : Realization P → Realization Q)
    (m : Vertex P → Vertex Q)
    (h : ∀ v x, x ∈ Realization.openStar P v → f x ∈ Realization.openStar Q (m v))
    (v : Vertex P) (w : Vertex Q)
    (hw : f (Realization.vertex P v.val v.property) =
      Realization.vertex Q w.val w.property) : (ofStarMap f m h).vertexMap v = w := by
  apply Realization.vertex_openStar_eq
  rw [← hw]
  exact h v _ (Realization.vertex_mem_openStar v)

/-- The actual affine simplicial map preserves every given literal vertex value. -/
theorem ofStarMap_realization_vertex (f : Realization P → Realization Q)
    (m : Vertex P → Vertex Q)
    (h : ∀ v x, x ∈ Realization.openStar P v → f x ∈ Realization.openStar Q (m v))
    (v : Vertex P) (w : Vertex Q)
    (hw : f (Realization.vertex P v.val v.property) =
      Realization.vertex Q w.val w.property) :
    (ofStarMap f m h).realization (Realization.vertex P v.val v.property) =
      f (Realization.vertex P v.val v.property) := by
  rw [realization_vertex, ofStarMap_vertexMap_eq f m h v w hw, hw]

/-- The constructed carrier homotopy fixes every prescribed original vertex
whose given image is a literal target vertex. -/
theorem starCarrierHomotopy_fixed_vertex [Finite (Face P)]
    (f : C(Realization P, Realization Q)) (m : Vertex P → Vertex Q)
    (h : ∀ v x, x ∈ Realization.openStar P v → f x ∈ Realization.openStar Q (m v))
    (v : Vertex P) (w : Vertex Q)
    (hw : f (Realization.vertex P v.val v.property) =
      Realization.vertex Q w.val w.property) (t : unitInterval) :
    starCarrierHomotopy f m h (t, Realization.vertex P v.val v.property) =
      f (Realization.vertex P v.val v.property) :=
  Realization.carrierHomotopy_fixed f (ofStarMap f m h).realization
    (ofStarMap_support_subset f m h) (ofStarMap_realization_vertex f m h v w hw).symm t

/-- One mesh bound, computed on the fixed original finite polyhedron, controls
every later domain whose actual face images satisfy that bound. Vertex choices
are derived from the target open-star cover, including empty vertex types. -/
theorem exists_starMap_mesh_bound [Finite (Face P)]
    (f : C(Realization P, Realization Q)) :
    letI := Realization.finiteCoordinateMetricSpace P
    ∃ ε > 0, ∀ (U : Type w) (R : PreAbstractSimplicialComplex U)
      (e : C(Realization R, Realization P)),
      (∀ s : Face R, Metric.diam (e '' Set.range (Realization.faceMap R s)) ≤ ε) →
      ∃ m : Vertex R → Vertex Q, ∀ v x, x ∈ Realization.openStar R v →
        f (e x) ∈ Realization.openStar Q (m v) := by
  let := Realization.finiteCoordinateMetricSpace P
  obtain ⟨δ, hδ, hsmall⟩ := Metric.exists_diam_lt_subordinate_of_compact f
    (Realization.openStar Q) (Realization.isOpen_openStar Q)
    (by rw [Realization.iUnion_openStar])
  refine ⟨δ / 3, by positivity, ?_⟩
  intro U R e hmesh
  have hstars : ∀ v : Vertex R, ∃ w : Vertex Q,
      f '' (e '' Realization.closedStar R v) ⊆ Realization.openStar Q w := by
    intro v
    apply hsmall
    · exact ⟨e (Realization.vertex R v.val v.property),
        ⟨Realization.vertex R v.val v.property,
          Realization.openStar_subset_closedStar v (Realization.vertex_mem_openStar v), rfl⟩⟩
    · exact lt_of_le_of_lt (Realization.diam_image_closedStar_le e (by positivity) hmesh v)
        (by linarith)
  choose m hm using hstars
  refine ⟨m, ?_⟩
  intro v x hx
  exact hm v ⟨e x, ⟨x, Realization.openStar_subset_closedStar v hx, rfl⟩, rfl⟩

/-- The derived mesh bound constructs the actual simplicial map and continuous
carrier homotopy, retaining all prescribed literal vertex values and the exact
affine coordinate formula. Subdivision geometry must supply the face-mesh bound. -/
theorem exists_starApproximation_mesh_bound [Finite (Face P)]
    (f : C(Realization P, Realization Q)) :
    letI := Realization.finiteCoordinateMetricSpace P
    ∃ ε > 0, ∀ (U : Type w) (R : PreAbstractSimplicialComplex U) [Finite (Face R)]
      (e : C(Realization R, Realization P)),
      (∀ s : Face R, Metric.diam (e '' Set.range (Realization.faceMap R s)) ≤ ε) →
      ∃ g : Morphism R Q, ∃ H : ContinuousMap.Homotopy (f.comp e) g.realization,
        (∀ z : unitInterval × Realization R,
          (H z).point = Realization.segmentPoint z.1 (f (e z.2)).point
            (g.realization z.2).point) ∧
        (∀ v : Vertex R, ∀ w : Vertex Q,
          f (e (Realization.vertex R v.val v.property)) =
              Realization.vertex Q w.val w.property →
            g.vertexMap v = w ∧ ∀ t : unitInterval,
              H (t, Realization.vertex R v.val v.property) =
                f (e (Realization.vertex R v.val v.property))) := by
  let := Realization.finiteCoordinateMetricSpace P
  obtain ⟨ε, hε, hbound⟩ := exists_starMap_mesh_bound f
  refine ⟨ε, hε, ?_⟩
  intro U R hR e hmesh
  obtain ⟨m, hm⟩ := hbound U R e hmesh
  let g := ofStarMap (f.comp e) m hm
  let H := starCarrierHomotopy (f.comp e) m hm
  refine ⟨g, H, ?_, ?_⟩
  · intro z
    exact Realization.carrierHomotopy_point (f.comp e) g.realization
      (ofStarMap_support_subset (f.comp e) m hm) z
  · intro v w hw
    exact ⟨ofStarMap_vertexMap_eq (f.comp e) m hm v w hw,
      fun t => starCarrierHomotopy_fixed_vertex (f.comp e) m hm v w hw t⟩

end Morphism

end PreAbstractSimplicialComplex

end
