/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.Realization

/-!
# Morphisms on actual vertices of abstract complexes

The vertex type consists of the labels whose singletons actually belong to
the complex. This retains empty geometric complexes with unused ambient
labels and allows maps to an empty target when the actual source is empty.
Face-preserving vertex maps may identify vertices.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology

universe u v w z

namespace PreAbstractSimplicialComplex

variable {V : Type u} {W : Type v}

/-- The vertices actually belonging to the complex, including the empty case. -/
abbrev Vertex (P : PreAbstractSimplicialComplex V) := {v : V // ({v} : Finset V) ∈ P}

/-- A vertex of an actual face belongs to the complex. -/
theorem singleton_mem_of_face (P : PreAbstractSimplicialComplex V) (s : Face P)
    {v : V} (hv : v ∈ s.val) : ({v} : Finset V) ∈ P := by
  classical
  exact (P.isRelLowerSet_faces s.property).2 (Finset.singleton_subset_iff.mpr hv)
    (Finset.singleton_nonempty v)

/-- The actual vertices of a closed face. -/
def faceVertices (P : PreAbstractSimplicialComplex V) (s : Face P) : Finset (Vertex P) := by
  classical
  exact s.val.subtype (fun v => ({v} : Finset V) ∈ P)

/-- The literal inclusion of a face's vertices in the actual vertex type. -/
def faceVertexEmbedding (P : PreAbstractSimplicialComplex V) (s : Face P) : s.val ↪ Vertex P where
  toFun v := ⟨v.val, singleton_mem_of_face P s v.property⟩
  inj' a b h := by
    have hv : a.val = b.val := congrArg (fun v : Vertex P => v.val) h
    exact Subtype.ext hv

theorem faceVertex_mem (P : PreAbstractSimplicialComplex V) (s : Face P) (v : s.val) :
    faceVertexEmbedding P s v ∈ faceVertices P s := by
  classical
  exact Finset.mem_subtype.mpr v.property

theorem faceVertices_nonempty (P : PreAbstractSimplicialComplex V) (s : Face P) :
    (faceVertices P s).Nonempty := by
  obtain ⟨v, hv⟩ := (P.isRelLowerSet_faces s.property).1
  exact ⟨faceVertexEmbedding P s ⟨v, hv⟩, faceVertex_mem P s ⟨v, hv⟩⟩

open Classical in
/-- Forgetting the belonging-vertex certificates gives the original face. -/
theorem faceVertices_image_val (P : PreAbstractSimplicialComplex V) (s : Face P) :
    (faceVertices P s).image (Subtype.val : Vertex P → V) = s.val := by
  classical
  ext v
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact Finset.mem_subtype.mp hw
  · intro hv
    exact ⟨⟨v, singleton_mem_of_face P s hv⟩, Finset.mem_subtype.mpr hv, rfl⟩

/-- Passing to actual belonging vertices preserves a face's cardinality. -/
theorem faceVertices_card (P : PreAbstractSimplicialComplex V) (s : Face P) :
    (faceVertices P s).card = s.val.card := by
  classical
  have h := congrArg Finset.card (faceVertices_image_val P s)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
  exact h

/-- The actual vertex finsets respect genuine face inclusions. -/
theorem faceVertices_mono (P : PreAbstractSimplicialComplex V) {s t : Face P}
    (h : s.val ⊆ t.val) : faceVertices P s ⊆ faceVertices P t := by
  classical
  intro v hv
  exact Finset.mem_subtype.mpr (h (Finset.mem_subtype.mp hv))

/-- The face's actual vertex finset is its finite vertex type mapped by the literal embedding. -/
theorem faceVertices_eq_map_univ (P : PreAbstractSimplicialComplex V) (s : Face P) :
    faceVertices P s = Finset.univ.map (faceVertexEmbedding P s) := by
  classical
  ext v
  constructor
  · intro hv
    exact Finset.mem_map.mpr
      ⟨⟨v.val, Finset.mem_subtype.mp hv⟩, Finset.mem_univ _, Subtype.ext rfl⟩
  · intro hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp hv
    exact faceVertex_mem P s w

namespace Realization

variable {P : PreAbstractSimplicialComplex V}

/-- Every nonzero coordinate of an actual realization point is an actual vertex. -/
theorem support_vertex (x : Realization P) {v : V} (hv : v ∈ x.point.weights.support) :
    ({v} : Finset V) ∈ P :=
  singleton_mem_of_face P ⟨x.point.weights.support, x.support_mem⟩ hv

/-- The same barycentric point on the actual belonging vertex subtype. -/
def vertexCoordinates (x : Realization P) : Convexity.StdSimplex ℝ (Vertex P) where
  weights := x.point.weights.subtypeDomain (fun v => ({v} : Finset V) ∈ P)
  nonneg v := x.point.weights_nonneg v.val
  total := by
    exact (Finsupp.sum_subtypeDomain_index (v := x.point.weights)
      (h := fun (_ : V) (r : ℝ) => r) (fun v hv => support_vertex x hv)).trans x.point.total

@[simp]
theorem vertexCoordinates_weight (x : Realization P) (v : Vertex P) :
    (vertexCoordinates x).weights v = x.point.weights v.val := rfl

/-- Forgetting the subtype returns the exact original barycentric coordinates. -/
theorem map_vertexCoordinates (x : Realization P) :
    (vertexCoordinates x).map (Subtype.val : Vertex P → V) = x.point := by
  classical
  apply Convexity.StdSimplex.ext
  ext v
  by_cases hv : ({v} : Finset V) ∈ P
  · rw [Convexity.StdSimplex.weights_map, Finsupp.mapDomain_apply_of_injective
      Subtype.val_injective _ ⟨v, hv⟩]
    rfl
  · rw [Convexity.StdSimplex.weights_map]
    have hr : v ∉ Set.range (Subtype.val : Vertex P → V) := by
      rintro ⟨z, rfl⟩
      exact hv z.property
    rw [Finsupp.mapDomain_of_notMem_range _ _ hr]
    symm
    by_contra hz
    exact hv (support_vertex x (Finsupp.mem_support_iff.mpr hz))

/-- Finite-face coordinates lift naturally to the actual vertex subtype. -/
theorem vertexCoordinates_faceMap (s : Face P) (q : Convexity.StdSimplex ℝ s.val) :
    vertexCoordinates (faceMap P s q) = q.map (faceVertexEmbedding P s) := by
  apply Convexity.StdSimplex.map_injective (R := ℝ) Subtype.val_injective
  rw [map_vertexCoordinates, Convexity.StdSimplex.map_map]
  rfl

end Realization

open Classical in
/-- A simplicial map is a map of actual vertices carrying every actual face
to a target face. Vertex identifications are allowed. -/
structure Morphism (P : PreAbstractSimplicialComplex V) (Q : PreAbstractSimplicialComplex W) where
  /-- The actual vertex map; no unused ambient labels need values. -/
  vertexMap : Vertex P → Vertex Q
  /-- The image of every actual finite face belongs to the target complex. -/
  face_mem (s : Face P) : (faceVertices P s).image (fun v => (vertexMap v).val) ∈ Q

namespace Morphism

variable {P : PreAbstractSimplicialComplex V} {Q : PreAbstractSimplicialComplex W}

/-- A simplicial morphism is determined by its actual vertex map. -/
@[ext]
theorem ext {f g : Morphism P Q} (h : ∀ v, f.vertexMap v = g.vertexMap v) : f = g := by
  cases f with
  | mk fv hf =>
    cases g with
    | mk gv hg =>
      have hfg : fv = gv := funext h
      subst gv
      rfl

/-- The identity on actual vertices is a simplicial morphism. -/
def id (P : PreAbstractSimplicialComplex V) : Morphism P P where
  vertexMap := _root_.id
  face_mem s := by
    classical
    change (faceVertices P s).image (Subtype.val : Vertex P → V) ∈ P
    rw [faceVertices_image_val]
    exact s.property

/-- The literal image of a finite face under the actual vertex map. -/
def faceImage (f : Morphism P Q) (s : Face P) : Face Q := by
  classical
  exact ⟨(faceVertices P s).image (fun v => (f.vertexMap v).val), f.face_mem s⟩

open Classical in
/-- Actual vertices of an image face are exactly the images of its source
vertices, even when the vertex map identifies labels. -/
theorem faceVertices_faceImage (f : Morphism P Q) (s : Face P) :
    faceVertices Q (f.faceImage s) = (faceVertices P s).image f.vertexMap := by
  classical
  ext v
  rw [show v ∈ faceVertices Q (f.faceImage s) ↔ v.val ∈ (f.faceImage s).val from
    Finset.mem_subtype]
  change v.val ∈ (faceVertices P s).image (fun w => (f.vertexMap w).val) ↔
    v ∈ (faceVertices P s).image f.vertexMap
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw, Subtype.ext h⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw, congrArg Subtype.val h⟩

/-- Composition of actual simplicial vertex maps, with the outer map first,
preserves faces and folds. -/
def comp {U : Type w} {R : PreAbstractSimplicialComplex U}
    (g : Morphism Q R) (f : Morphism P Q) : Morphism P R where
  vertexMap := g.vertexMap ∘ f.vertexMap
  face_mem s := by
    classical
    have h := g.face_mem (f.faceImage s)
    rw [faceVertices_faceImage, Finset.image_image] at h
    exact h

/-- Left identity for actual simplicial morphisms. -/
@[simp]
theorem id_comp (f : Morphism P Q) : (id Q).comp f = f := by
  ext v
  rfl

/-- Right identity for actual simplicial morphisms. -/
@[simp]
theorem comp_id (f : Morphism P Q) : f.comp (id P) = f := by
  ext v
  rfl

/-- Associativity of actual simplicial morphism composition. -/
theorem comp_assoc {U : Type w} {Z : Type z}
    {R : PreAbstractSimplicialComplex U} {S : PreAbstractSimplicialComplex Z}
    (h : Morphism R S) (g : Morphism Q R) (f : Morphism P Q) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext v
  rfl

/-- Push forward the actual finite distribution, retaining all multiplicities
when source vertices are identified. -/
def realizationMap (f : Morphism P Q) (x : Realization P) : Realization Q := by
  classical
  let q := (Realization.vertexCoordinates x).map (fun v => (f.vertexMap v).val)
  refine ⟨q, ?_⟩
  apply (Q.isRelLowerSet_faces (f.face_mem ⟨x.point.weights.support, x.support_mem⟩)).2
  · have hs : (Realization.vertexCoordinates x).weights.support =
        faceVertices P ⟨x.point.weights.support, x.support_mem⟩ := by
      change (x.point.weights.subtypeDomain (fun v => ({v} : Finset V) ∈ P)).support =
        x.point.weights.support.subtype (fun v => ({v} : Finset V) ∈ P)
      exact Finsupp.support_subtypeDomain
    change (Finsupp.mapDomain (fun v => (f.vertexMap v).val)
      (Realization.vertexCoordinates x).weights).support ⊆ _
    simpa only [hs] using
      (Finsupp.mapDomain_support (f := fun v : Vertex P => (f.vertexMap v).val)
        (s := (Realization.vertexCoordinates x).weights))
  · exact q.support_weights_nonempty

/-- Coordinate formula for the actual realized vertex map, including folds. -/
theorem realizationMap_point (f : Morphism P Q) (x : Realization P) :
    (f.realizationMap x).point =
      (Realization.vertexCoordinates x).map (fun v => (f.vertexMap v).val) := rfl

/-- The vertex map on one finite face, valued in its actual image face. -/
def faceVertexMap (f : Morphism P Q) (s : Face P) : s.val → (f.faceImage s).val := by
  classical
  intro v
  exact ⟨(f.vertexMap (faceVertexEmbedding P s v)).val,
    Finset.mem_image.mpr ⟨faceVertexEmbedding P s v, faceVertex_mem P s v, rfl⟩⟩

/-- On an actual face the realized map is precisely the finite affine vertex
map into the actual image face. No injectivity of the vertex map is required. -/
theorem realizationMap_faceMap (f : Morphism P Q) (s : Face P)
    (q : Convexity.StdSimplex ℝ s.val) :
    f.realizationMap (Realization.faceMap P s q) =
      Realization.faceMap Q (f.faceImage s) (q.map (f.faceVertexMap s)) := by
  apply Realization.ext
  rw [realizationMap_point, Realization.vertexCoordinates_faceMap]
  change (q.map (faceVertexEmbedding P s)).map (fun v => (f.vertexMap v).val) =
    (q.map (f.faceVertexMap s)).map (Subtype.val : (f.faceImage s).val → W)
  rw [Convexity.StdSimplex.map_map, Convexity.StdSimplex.map_map]
  rfl

/-- Actual affine simplicial maps are continuous for the weak finite-face
topologies of arbitrary complexes. -/
theorem continuous_realizationMap (f : Morphism P Q) : Continuous f.realizationMap := by
  rw [Realization.continuous_iff]
  intro s
  have heq : f.realizationMap ∘ Realization.faceMap P s =
      Realization.faceMap Q (f.faceImage s) ∘ Convexity.StdSimplex.map (f.faceVertexMap s) :=
    funext (f.realizationMap_faceMap s)
  rw [heq]
  exact (Realization.continuous_faceMap Q (f.faceImage s)).comp
    (Convexity.StdSimplex.continuous_map ℝ (f.faceVertexMap s))

/-- The bundled actual affine map of weak polyhedra. -/
def realization (f : Morphism P Q) : C(Realization P, Realization Q) :=
  ⟨f.realizationMap, f.continuous_realizationMap⟩

/-- An actual vertex has its literal Dirac distribution in actual-vertex coordinates. -/
theorem vertexCoordinates_vertex (v : Vertex P) :
    Realization.vertexCoordinates (Realization.vertex P v.val v.property) =
      Convexity.StdSimplex.single v := by
  apply Convexity.StdSimplex.map_injective (R := ℝ) Subtype.val_injective
  rw [Realization.map_vertexCoordinates, Convexity.StdSimplex.map_single]
  rfl

/-- The affine realization sends each belonging vertex to its declared image literally. -/
theorem realization_vertex (f : Morphism P Q) (v : Vertex P) :
    f.realization (Realization.vertex P v.val v.property) =
      Realization.vertex Q (f.vertexMap v).val (f.vertexMap v).property := by
  apply Realization.ext
  change (f.realizationMap (Realization.vertex P v.val v.property)).point = _
  rw [realizationMap_point, vertexCoordinates_vertex, Convexity.StdSimplex.map_single]
  rfl

/-- The actual-vertex distribution itself is pushed forward by the declared map. -/
theorem vertexCoordinates_realizationMap (f : Morphism P Q) (x : Realization P) :
    Realization.vertexCoordinates (f.realizationMap x) =
      (Realization.vertexCoordinates x).map f.vertexMap := by
  apply Convexity.StdSimplex.map_injective (R := ℝ) Subtype.val_injective
  rw [Realization.map_vertexCoordinates, realizationMap_point, Convexity.StdSimplex.map_map]

/-- Realization preserves the actual identity map. -/
theorem realizationMap_id (x : Realization P) : (id P).realizationMap x = x := by
  apply Realization.ext
  rw [realizationMap_point]
  exact Realization.map_vertexCoordinates x

/-- Realization preserves composition of actual affine maps, including folds. -/
theorem realizationMap_comp {U : Type w} {R : PreAbstractSimplicialComplex U}
    (g : Morphism Q R) (f : Morphism P Q) (x : Realization P) :
    (g.comp f).realizationMap x = g.realizationMap (f.realizationMap x) := by
  apply Realization.ext
  rw [realizationMap_point, realizationMap_point, vertexCoordinates_realizationMap,
    Convexity.StdSimplex.map_map]
  rfl

end Morphism

end PreAbstractSimplicialComplex

end
