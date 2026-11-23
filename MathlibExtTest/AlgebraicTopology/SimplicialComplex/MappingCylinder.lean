/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.MappingCylinder

/-!
# Actual finite-domain cylinder and cone consumers

The source is a finite edge with an unused ambient label. Both edge vertices
fold to one vertex of an infinite discrete target, also with an unused label.
The empty source and target test the fresh apex and the literal zero-cell boundary.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Topology CategoryTheory
open PreAbstractSimplicialComplex PreAbstractSimplicialComplex.MappingCylinder

namespace SimplicialCylinderTest

private def edge : PreAbstractSimplicialComplex (Bool ⊕ PUnit.{1}) :=
  relabelComplex (⊤ : PreAbstractSimplicialComplex Bool) Function.Embedding.inl

private instance : Finite (Face edge) :=
  finiteFaces_relabelComplex (⊤ : PreAbstractSimplicialComplex Bool) Function.Embedding.inl

private def infiniteTarget : PreAbstractSimplicialComplex (ℕ ⊕ PUnit.{1}) where
  faces := {s | ∃ n : ℕ, s = {Sum.inl n}}
  isRelLowerSet_faces := by
    intro s hs
    obtain ⟨n, rfl⟩ := hs
    refine ⟨Finset.singleton_nonempty _, ?_⟩
    intro t ht hn
    obtain ⟨a, ha⟩ := hn
    have he : a = Sum.inl n := Finset.mem_singleton.mp (ht ha)
    have hm : Sum.inl n ∈ t := he ▸ ha
    exact ⟨n, Finset.Subset.antisymm ht (Finset.singleton_subset_iff.mpr hm)⟩

private def targetVertex (n : ℕ) : Vertex infiniteTarget := ⟨Sum.inl n, n, rfl⟩

example : Function.Injective targetVertex := by
  intro m n h
  exact Sum.inl.inj (congrArg Subtype.val h)

private def edgeVertex (b : Bool) : Vertex edge := by
  classical
  let : DecidableEq (Bool ⊕ PUnit.{1}) := Classical.decEq _
  exact ⟨Sum.inl b, {b}, Finset.singleton_nonempty _, Finset.image_singleton _ _⟩

example : edgeVertex false ≠ edgeVertex true := by
  intro h
  have he := Sum.inl.inj (congrArg Subtype.val h)
  cases he

example : ({Sum.inr PUnit.unit} : Finset (Bool ⊕ PUnit.{1})) ∉ edge := by
  classical
  let : DecidableEq (Bool ⊕ PUnit.{1}) := Classical.decEq _
  rintro ⟨s, _, hs⟩
  have hm := (congrArg (fun t : Finset (Bool ⊕ PUnit.{1}) => Sum.inr PUnit.unit ∈ t) hs).symm
  have hmem := Eq.mp hm (Finset.mem_singleton_self _)
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hmem
  exact Sum.inl_ne_inr ha

example : ({Sum.inr PUnit.unit} : Finset (ℕ ⊕ PUnit.{1})) ∉ infiniteTarget := by
  rintro ⟨n, hn⟩
  exact Sum.inr_ne_inl (Finset.singleton_injective hn)

private def folding : Morphism edge infiniteTarget where
  vertexMap _ := targetVertex 0
  face_mem s := by
    classical
    let : DecidableEq (ℕ ⊕ PUnit.{1}) := Classical.decEq _
    exact ⟨0, Finset.image_const (faceVertices_nonempty edge s) (Sum.inl 0)⟩

example : folding.vertexMap (edgeVertex false) = folding.vertexMap (edgeVertex true) := rfl

private theorem folding_realization (x : Realization edge) :
    folding.realization x = Realization.vertex infiniteTarget (Sum.inl 0) (targetVertex 0).property := by
  apply Realization.ext
  change (Realization.vertexCoordinates x).map (fun _ => Sum.inl 0) =
    Convexity.StdSimplex.single (Sum.inl 0)
  exact Convexity.StdSimplex.map_const _ _

example : IsClosedEmbedding (domainMorphism folding).realization :=
  isClosedEmbedding_domainMorphism folding

example : IsClosedEmbedding (targetToConeMorphism folding).realization :=
  isClosedEmbedding_targetToConeMorphism folding

example (x : Realization (barycentricSubdivision edge)) :
    retraction folding ((domainMorphism folding).realization x) =
      Realization.vertex infiniteTarget (Sum.inl 0) (targetVertex 0).property := by
  rw [retraction_domain, folding_realization]

example (t : unitInterval) (x : Realization infiniteTarget) :
    deformationRelativeTarget folding (t, (targetMorphism folding).realization x) =
      (targetMorphism folding).realization x :=
  deformation_target_fixed folding t x

example (x : Realization (barycentricSubdivision edge)) :
    deformation folding (1, (domainMorphism folding).realization x) =
      (targetMorphism folding).realization
        (Realization.vertex infiniteTarget (Sum.inl 0) (targetVertex 0).property) := by
  rw [deformation_terminal_domain, folding_realization]

example (x : Realization (barycentricSubdivision edge)) (y : Realization infiniteTarget) :
    (domainMorphism folding).realization x ≠ (targetMorphism folding).realization y := by
  intro h
  exact Set.disjoint_left.mp (domain_target_disjoint folding)
    ⟨x, rfl⟩ ⟨y, h.symm⟩

example : Finite (Face (domainComplex edge (ℕ ⊕ PUnit.{1}))) ∧
    Finite (Face (coneComplex (domainComplex edge (ℕ ⊕ PUnit.{1})))) :=
  ⟨finiteFaces_domainComplex _ _, finiteFaces_attachedCone _ _⟩

example : IsPushout
    (TopCat.ofHom (inclusionMorphism (domainComplex_le folding)).realization)
    (TopCat.coneBase (TopCat.of (Realization (domainComplex edge (ℕ ⊕ PUnit.{1})))))
    (TopCat.ofHom (cylinderToCone folding).realization)
    (TopCat.ofHom (ordinaryConeAttachment folding)) :=
  isPushout_ordinaryConeAttachment folding

example (x : Realization (domainComplex edge (ℕ ⊕ PUnit.{1}))) :
    ordinaryConeAttachment folding
      (TopCat.coneBase (TopCat.of (Realization (domainComplex edge (ℕ ⊕ PUnit.{1})))) x) =
    (cylinderToCone folding).realization (Realization.inclusion (domainComplex_le folding) x) :=
  ordinaryConeAttachment_base folding x

private def emptySource : PreAbstractSimplicialComplex (ℕ ⊕ Bool) := ⊥
private def emptyTarget : PreAbstractSimplicialComplex Empty := ⊥

private instance : IsEmpty (Face emptySource) := ⟨fun s => s.property⟩
private instance : IsEmpty (Realization emptySource) := ⟨fun x => x.support_mem⟩

private def emptyMap : Morphism emptySource emptyTarget where
  vertexMap v := v.property.elim
  face_mem s := s.property.elim

example : IsEmpty (Realization (complex emptyMap)) :=
  ⟨fun x => x.support_mem.2.2⟩

example : Finite (Face (coneComplex (domainComplex emptySource Empty))) :=
  finiteFaces_attachedCone _ _

example : Nonempty (Realization (associatedCone emptyMap)) :=
  ⟨(attachedConeMorphism emptyMap).realization
    (Realization.vertex (coneComplex (domainComplex emptySource Empty))
      (coneApex (domainComplex emptySource Empty)).val
      (coneApex (domainComplex emptySource Empty)).property)⟩

private instance : IsEmpty (Metric.sphere (0 : Fin 0 → ℝ) 1) := by
  refine ⟨fun x => ?_⟩
  have he : x.val = 0 := by ext a; exact Fin.elim0 a
  have h := x.property
  rw [he] at h
  simp only [Metric.mem_sphere, dist_self, zero_ne_one] at h

private def zeroSphereIdentification : Metric.sphere (0 : Fin 0 → ℝ) 1 ≃ₜ Realization emptySource :=
  Homeomorph.empty

example : Metric.sphere (0 : Fin 0 → ℝ) 1 ≃ₜ Set.range (domainMorphism emptyMap).realization :=
  copiedSphereBoundary emptyMap 0 zeroSphereIdentification

example (n : ℕ) (σ : Metric.sphere (0 : Fin n → ℝ) 1 ≃ₜ Realization edge)
    (x : Metric.sphere (0 : Fin n → ℝ) 1) :
    retraction folding (copiedSphereBoundary folding n σ x).val =
      folding.realization (σ x) :=
  copiedSphereBoundary_retraction folding n σ x

end SimplicialCylinderTest

end
