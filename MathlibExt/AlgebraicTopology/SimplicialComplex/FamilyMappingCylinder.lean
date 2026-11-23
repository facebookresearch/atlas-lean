/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.MappingCylinder
public import MathlibExt.AlgebraicTopology.SimplicialComplex.MappingCylinder.SmallCylinder
public import Mathlib.Topology.Homotopy.Basic

/-!
# Mapping cylinders for families of simplicial complexes
-/

/-! Constructed arbitrary-family weak polyhedral cylinder/cone attachments.
All original maps, empty-family targets, whole relative homotopies and
both actual ordinary attachment pushouts are retained. -/

noncomputable section
set_option autoImplicit false
open Topology Set Function PreAbstractSimplicialComplex
open scoped unitInterval
universe u v w s

private theorem actualFamilyInclusionPoint {A : Type u}
    {T U : PreAbstractSimplicialComplex A} (h : T ≤ U) (x : T.Realization) :
    ((MappingCylinder.inclusionMorphism h).realization x).point = x.point := by
  change ((MappingCylinder.inclusionMorphism h).realizationMap x).point = x.point
  rw [Morphism.realizationMap_point]
  exact Realization.map_vertexCoordinates x

private theorem actualFamilyRelabelComplex_eq_map {A : Type u} {B : Type v}
    [decB : DecidableEq B] (T : PreAbstractSimplicialComplex A) (e : A ↪ B) :
    MappingCylinder.relabelComplex T e = T.map e := by
  change @PreAbstractSimplicialComplex.map A B (fun a b => Classical.propDecidable (a = b)) T e =
    @PreAbstractSimplicialComplex.map A B decB T e
  exact congrArg (fun d : DecidableEq B => @PreAbstractSimplicialComplex.map A B d T e)
    (Subsingleton.elim _ _)

namespace WeakFamilyUnionConstruction46

variable {«I» : Type u} {A : Type v}

private abbrev weakUnion (F : «I» → PreAbstractSimplicialComplex A) :
    PreAbstractSimplicialComplex A := ⨆ i, F i

private theorem mem_weakUnion (F : «I» → PreAbstractSimplicialComplex A) (s : Finset A) :
    s ∈ weakUnion F ↔ ∃ i, s ∈ F i := by
  change s ∈ ⋃ K ∈ Set.range F, K.faces ↔ ∃ i, s ∈ F i
  simp only [Set.mem_iUnion, Set.mem_range]
  constructor
  · rintro ⟨K, ⟨i, rfl⟩, hs⟩
    exact ⟨i, hs⟩
  · rintro ⟨i, hs⟩
    exact ⟨F i, ⟨i, rfl⟩, hs⟩

open Classical in
private def inclusion (F : «I» → PreAbstractSimplicialComplex A) (i : «I») :
    C((F i).Realization, (weakUnion F).Realization) :=
  ⟨PreAbstractSimplicialComplex.Realization.inclusion (le_iSup F i),
    PreAbstractSimplicialComplex.Realization.continuous_inclusion (le_iSup F i)⟩

open Classical in
private def sourceIndex (F : «I» → PreAbstractSimplicialComplex A)
    (x : (weakUnion F).Realization) : «I» :=
  Classical.choose ((mem_weakUnion F x.point.weights.support).mp x.support_mem)

private theorem sourceIndex_support (F : «I» → PreAbstractSimplicialComplex A)
    (x : (weakUnion F).Realization) : x.point.weights.support ∈ F (sourceIndex F x) :=
  Classical.choose_spec ((mem_weakUnion F x.point.weights.support).mp x.support_mem)

open Classical in
private def unionDesc (F : «I» → PreAbstractSimplicialComplex A)
    {Z : Type w} [TopologicalSpace Z] (g : ∀ i, C((F i).Realization, Z))
    (hag : ∀ i j, ∀ x : (F i ⊓ F j).Realization,
      g i (PreAbstractSimplicialComplex.Realization.inclusion inf_le_left x) =
        g j (PreAbstractSimplicialComplex.Realization.inclusion inf_le_right x)) :
    C((weakUnion F).Realization, Z) := by
  let d : (weakUnion F).Realization → Z := fun x =>
    g (sourceIndex F x) ⟨x.point, sourceIndex_support F x⟩
  have dcomponent (i : «I») (x : (F i).Realization) : d (inclusion F i x) = g i x := by
    let j := sourceIndex F (inclusion F i x)
    have hj : x.point.weights.support ∈ F j := sourceIndex_support F (inclusion F i x)
    exact hag j i ⟨x.point, hj, x.support_mem⟩
  refine ⟨d, ?_⟩
  rw [PreAbstractSimplicialComplex.Realization.continuous_iff]
  intro s
  obtain ⟨i, hi⟩ := (mem_weakUnion F s.val).mp s.property
  have heq : d ∘ PreAbstractSimplicialComplex.Realization.faceMap (weakUnion F) s =
      g i ∘ PreAbstractSimplicialComplex.Realization.faceMap (F i) ⟨s.val, hi⟩ := by
    funext q
    exact dcomponent i (PreAbstractSimplicialComplex.Realization.faceMap (F i) ⟨s.val, hi⟩ q)
  rw [heq]
  exact (g i).continuous.comp
    (PreAbstractSimplicialComplex.Realization.continuous_faceMap (F i) ⟨s.val, hi⟩)

private theorem unionDesc_component (F : «I» → PreAbstractSimplicialComplex A)
    {Z : Type w} [TopologicalSpace Z] (g : ∀ i, C((F i).Realization, Z)) (hag)
    (i : «I») (x : (F i).Realization) : unionDesc F g hag (inclusion F i x) = g i x := by
  let j := sourceIndex F (inclusion F i x)
  have hj : x.point.weights.support ∈ F j := sourceIndex_support F (inclusion F i x)
  exact hag j i ⟨x.point, hj, x.support_mem⟩

private theorem unionDesc_unique (F : «I» → PreAbstractSimplicialComplex A)
    {Z : Type w} [TopologicalSpace Z] (g : ∀ i, C((F i).Realization, Z)) (hag)
    (m : C((weakUnion F).Realization, Z))
    (hm : ∀ i, ∀ x : (F i).Realization, m (inclusion F i x) = g i x) :
    m = unionDesc F g hag := by
  ext x
  let i := sourceIndex F x
  let y : (F i).Realization := ⟨x.point, sourceIndex_support F x⟩
  exact (hm i y).trans (unionDesc_component F g hag i y).symm

open Classical in
private def sigmaCover (F : «I» → PreAbstractSimplicialComplex A) :
    C((Σ i, (F i).Realization), (weakUnion F).Realization) :=
  ⟨fun p => inclusion F p.1 p.2, continuous_sigma (fun i => (inclusion F i).continuous)⟩

private theorem sigmaCover_surjective (F : «I» → PreAbstractSimplicialComplex A) :
    Function.Surjective (sigmaCover F) := by
  intro x
  exact ⟨⟨sourceIndex F x, ⟨x.point, sourceIndex_support F x⟩⟩, rfl⟩

/-- The ordinary sigma covering has the actual quotient topology of the weak family union. -/
private theorem sigmaCover_isQuotientMap (F : «I» → PreAbstractSimplicialComplex A) :
    IsQuotientMap (sigmaCover F) := by
  rw [isQuotientMap_iff_isClosed]
  refine ⟨sigmaCover_surjective F, ?_⟩
  intro S
  constructor
  · intro hS
    exact hS.preimage (sigmaCover F).continuous
  · intro hS
    rw [PreAbstractSimplicialComplex.Realization.isClosed_iff]
    intro s
    obtain ⟨i, hi⟩ := (mem_weakUnion F s.val).mp s.property
    have hSi : IsClosed ((fun x : (F i).Realization => sigmaCover F ⟨i, x⟩) ⁻¹' S) :=
      (isClosed_sigma_iff.mp hS) i
    exact hSi.preimage
      (PreAbstractSimplicialComplex.Realization.continuous_faceMap (F i) ⟨s.val, hi⟩)

private theorem sigmaCover_injective (F : «I» → PreAbstractSimplicialComplex A)
    (hdis : ∀ i j, i ≠ j → F i ⊓ F j = ⊥) : Function.Injective (sigmaCover F) := by
  classical
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  by_cases hij : i = j
  · subst j
    have hp := congrArg (fun z : (weakUnion F).Realization => z.point) h
    change x.point = y.point at hp
    have hxy : x = y := PreAbstractSimplicialComplex.Realization.ext hp
    subst y
    rfl
  · have hz : x.point.weights.support ∈ F i ⊓ F j := by
      refine ⟨x.support_mem, ?_⟩
      have hp : x.point = y.point := congrArg PreAbstractSimplicialComplex.Realization.point h
      rw [hp]
      exact y.support_mem
    rw [hdis i j hij] at hz
    exact False.elim hz

open Classical in
/-- Disjoint family pieces have their ordinary sigma coproduct topology, without family finiteness.
-/
private def disjointUnionHomeomorph (F : «I» → PreAbstractSimplicialComplex A)
    (hdis : ∀ i j, i ≠ j → F i ⊓ F j = ⊥) :
    (Σ i, (F i).Realization) ≃ₜ (weakUnion F).Realization :=
  (Equiv.ofBijective (sigmaCover F)
    ⟨sigmaCover_injective F hdis, sigmaCover_surjective F⟩).toHomeomorphOfContinuousOpen
      (sigmaCover F).continuous
      ((sigmaCover_isQuotientMap F).isCoinducing.isOpenMap_of_injective
        (sigmaCover_injective F hdis))

end WeakFamilyUnionConstruction46

namespace TaggedFamilyComplexConstruction46

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

private abbrev Labels := (Σ i, Face (P i)) ⊕ W

open Classical in
private def tag (i : «I») : Face (P i) ⊕ W ↪ Labels (W := W) P :=
  Function.Embedding.sumMap
    (Function.Embedding.sigmaMk (β := fun i => Face (P i)) i)
    (Function.Embedding.refl W)

open Classical in
private def oldTarget : PreAbstractSimplicialComplex (Labels (W := W) P) :=
  MappingCylinder.relabelComplex Q Function.Embedding.inr

open Classical in
private def block (f : ∀ i, Morphism (P i) Q) (i : «I») :
    PreAbstractSimplicialComplex (Labels (W := W) P) :=
  MappingCylinder.relabelComplex (MappingCylinder.complex (f i)) (tag P i)

open Classical in
private def optionBlocks (f : ∀ i, Morphism (P i) Q) :
    Option «I» → PreAbstractSimplicialComplex (Labels (W := W) P)
  | none => oldTarget P Q
  | some i => block P Q f i

open Classical in
/-- The actual old target is present even when the family has no index. -/
private def cylinderFamily (f : ∀ i, Morphism (P i) Q) :
    PreAbstractSimplicialComplex (Labels (W := W) P) := ⨆ o, optionBlocks P Q f o

private theorem oldTarget_le_block (f : ∀ i, Morphism (P i) Q) (i : «I») :
    oldTarget P Q ≤ block P Q f i := by
  classical
  let : DecidableEq (Labels (W := W) P) := Classical.decEq _
  let : DecidableEq (Face (P i) ⊕ W) := Classical.decEq _
  intro s hs
  change ∃ a : Finset W, a ∈ Q ∧
    a.image (Function.Embedding.inr : W ↪ Labels (W := W) P) = s at hs
  obtain ⟨a, ha, rfl⟩ := hs
  change ∃ b : Finset (Face (P i) ⊕ W), b ∈ MappingCylinder.complex (f i) ∧
    b.image (tag P i) = a.image (Function.Embedding.inr : W ↪ Labels (W := W) P)
  refine ⟨a.image (Function.Embedding.inr : W ↪ Face (P i) ⊕ W), ?_, ?_⟩
  · apply MappingCylinder.targetComplex_le (f i)
    change ∃ b : Finset W, b ∈ Q ∧
      b.image (Function.Embedding.inr : W ↪ Face (P i) ⊕ W) =
        a.image (Function.Embedding.inr : W ↪ Face (P i) ⊕ W)
    exact ⟨a, ha, rfl⟩
  · rw [Finset.image_image]
    rfl

private theorem oldTarget_le_family (f : ∀ i, Morphism (P i) Q) :
    oldTarget P Q ≤ cylinderFamily P Q f :=
  le_iSup (optionBlocks P Q f) none

private theorem block_le_family (f : ∀ i, Morphism (P i) Q) (i : «I») :
    block P Q f i ≤ cylinderFamily P Q f :=
  le_iSup (optionBlocks P Q f) (some i)

private theorem cylinderFamily_empty_index (f : ∀ i, Morphism (P i) Q) [IsEmpty «I»] :
    cylinderFamily P Q f = oldTarget P Q := by
  apply le_antisymm
  · apply iSup_le
    intro o
    cases o with
    | none => exact le_rfl
    | some i => exact isEmptyElim i
  · exact oldTarget_le_family P Q f

open Classical in
private theorem copy_index_of_mem_image (i : «I») (s : Finset (Face (P i) ⊕ W))
    {k : «I»} (a : Face (P k))
    (h : Sum.inl (⟨k, a⟩ : Σ j, Face (P j)) ∈ s.image (tag P i)) : k = i := by
  obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp h
  cases x with
  | inl b =>
    have he : (⟨i, b⟩ : Σ j, Face (P j)) = ⟨k, a⟩ := Sum.inl.inj heq
    exact (congrArg Sigma.fst he).symm
  | inr b => cases heq

/-- Distinct tags force any common cylinder face to have no copied-domain coordinate. -/
private theorem oldTarget_intersection (f : ∀ i, Morphism (P i) Q) {i j : «I»} (hij : i ≠ j) :
    block P Q f i ⊓ block P Q f j = oldTarget P Q := by
  classical
  let : DecidableEq (Labels (W := W) P) := Classical.decEq _
  let : DecidableEq (Face (P i) ⊕ W) := Classical.decEq _
  let : DecidableEq (Face (P j) ⊕ W) := Classical.decEq _
  apply le_antisymm
  · intro s hs
    obtain ⟨a, ha, rfl⟩ := hs.1
    obtain ⟨b, hb, heq⟩ := hs.2
    change b.image (tag P j) = a.image (tag P i) at heq
    have hleft : a.toLeft = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hmem : Sum.inl (⟨i, x⟩ : Σ k, Face (P k)) ∈ a.image (tag P i) :=
        Finset.mem_image.mpr ⟨Sum.inl x, Finset.mem_toLeft.mp hx, rfl⟩
      have hmem' : Sum.inl (⟨i, x⟩ : Σ k, Face (P k)) ∈ b.image (tag P j) := by
        rw [heq]
        exact hmem
      exact hij (copy_index_of_mem_image P j b x (by
        simpa only [Finset.mem_image] using hmem'))
    have hQ : a.toRight ∈ Q := by
      have h := (MappingCylinder.mem_complex (f i) a).mp ha
      simpa only [MappingCylinder.hull, hleft, Finset.biUnion_empty, Finset.union_empty] using h.2.2
    refine ⟨a.toRight, hQ, ?_⟩
    have hsplit : a.toLeft.disjSum a.toRight = a := Finset.toLeft_disjSum_toRight
    rw [hleft, Finset.empty_disjSum, Finset.map_eq_image] at hsplit
    have hmap : a.image (tag P i) =
        a.toRight.image (Function.Embedding.inr : W ↪ Labels (W := W) P) := by
      calc
        a.image (tag P i) =
            (a.toRight.image (Function.Embedding.inr : W ↪ Face (P i) ⊕ W)).image
              (tag P i) := congrArg (fun t => t.image (tag P i)) hsplit.symm
        _ = a.toRight.image (Function.Embedding.inr : W ↪ Labels (W := W) P) := by
          rw [Finset.image_image]
          rfl
    exact hmap.symm
  · exact le_inf (oldTarget_le_block P Q f i) (oldTarget_le_block P Q f j)

/-- The old target and each tagged block meet in the entire unchanged old target. -/
private theorem oldTarget_block_intersection (f : ∀ i, Morphism (P i) Q) (i : «I») :
    oldTarget P Q ⊓ block P Q f i = oldTarget P Q :=
  inf_eq_left.mpr (oldTarget_le_block P Q f i)

open Classical in
private def oldTargetHomeomorph : Q.Realization ≃ₜ (oldTarget P Q).Realization :=
  MappingCylinder.relabelHomeomorph Q Function.Embedding.inr

open Classical in
private def blockHomeomorph (f : ∀ i, Morphism (P i) Q) (i : «I») :
    (MappingCylinder.complex (f i)).Realization ≃ₜ (block P Q f i).Realization :=
  MappingCylinder.relabelHomeomorph (MappingCylinder.complex (f i)) (tag P i)

open Classical in
private def oldInclusion (f : ∀ i, Morphism (P i) Q) :
    C(Q.Realization, (cylinderFamily P Q f).Realization) :=
  (⟨PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_family P Q f),
    PreAbstractSimplicialComplex.Realization.continuous_inclusion (oldTarget_le_family P Q f)⟩ :
      C((oldTarget P Q).Realization, (cylinderFamily P Q f).Realization)).comp
        (oldTargetHomeomorph P Q : C(Q.Realization, (oldTarget P Q).Realization))

open Classical in
private def blockInclusion (f : ∀ i, Morphism (P i) Q) (i : «I») :
    C((MappingCylinder.complex (f i)).Realization, (cylinderFamily P Q f).Realization) :=
  (⟨PreAbstractSimplicialComplex.Realization.inclusion (block_le_family P Q f i),
    PreAbstractSimplicialComplex.Realization.continuous_inclusion (block_le_family P Q f i)⟩ :
      C((block P Q f i).Realization, (cylinderFamily P Q f).Realization)).comp
        (blockHomeomorph P Q f i : C((MappingCylinder.complex (f i)).Realization,
          (block P Q f i).Realization))

private theorem oldInclusion_point (f : ∀ i, Morphism (P i) Q) (x : Q.Realization) :
    (oldInclusion P Q f x).point = x.point.map (Sum.inr : W → Labels (W := W) P) :=
  MappingCylinder.relabelMorphism_point Q Function.Embedding.inr x

private theorem blockInclusion_point (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (x : (MappingCylinder.complex (f i)).Realization) :
    (blockInclusion P Q f i x).point = x.point.map (tag P i) :=
  MappingCylinder.relabelMorphism_point (MappingCylinder.complex (f i)) (tag P i) x

private theorem oldInclusion_isClosedEmbedding (f : ∀ i, Morphism (P i) Q) :
    IsClosedEmbedding (oldInclusion P Q f) :=
  (PreAbstractSimplicialComplex.Realization.isClosedEmbedding_inclusion
    (oldTarget_le_family P Q f)).comp (oldTargetHomeomorph P Q).isClosedEmbedding

private theorem blockInclusion_isClosedEmbedding (f : ∀ i, Morphism (P i) Q) (i : «I») :
    IsClosedEmbedding (blockInclusion P Q f i) :=
  (PreAbstractSimplicialComplex.Realization.isClosedEmbedding_inclusion
    (block_le_family P Q f i)).comp (blockHomeomorph P Q f i).isClosedEmbedding

/-- The SAME old target point is present literally inside every tagged cylinder. -/
private theorem oldInBlock (f : ∀ i, Morphism (P i) Q) (i : «I») (q : Q.Realization) :
    blockHomeomorph P Q f i ((MappingCylinder.targetMorphism (f i)).realization q) =
      PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i)
        (oldTargetHomeomorph P Q q) := by
  apply PreAbstractSimplicialComplex.Realization.ext
  change ((MappingCylinder.relabelMorphism (MappingCylinder.complex (f i))
    (tag P i)).realization ((MappingCylinder.targetMorphism (f i)).realization q)).point =
      ((MappingCylinder.relabelMorphism Q Function.Embedding.inr).realization q).point
  rw [MappingCylinder.relabelMorphism_point, MappingCylinder.targetMorphism_point,
    MappingCylinder.relabelMorphism_point, Convexity.StdSimplex.map_map]
  rfl

open Classical in
private def blockRetraction (f : ∀ i, Morphism (P i) Q) (i : «I») :
    C((block P Q f i).Realization, Q.Realization) :=
  (MappingCylinder.retraction (f i)).comp
    (blockHomeomorph P Q f i).symm

private theorem blockRetraction_old (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (x : (oldTarget P Q).Realization) :
    blockRetraction P Q f i
        (PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i) x) =
      (oldTargetHomeomorph P Q).symm x := by
  let q := (oldTargetHomeomorph P Q).symm x
  have h := oldInBlock P Q f i q
  have hx : PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i) x =
      blockHomeomorph P Q f i ((MappingCylinder.targetMorphism (f i)).realization q) :=
    (h.trans (congrArg
      (PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i))
      ((oldTargetHomeomorph P Q).apply_symm_apply x))).symm
  change MappingCylinder.retraction (f i)
    ((blockHomeomorph P Q f i).symm
      (PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i) x)) = q
  rw [hx, (blockHomeomorph P Q f i).symm_apply_apply]
  exact MappingCylinder.retraction_target (f i) q

open Classical in
private def pieceRetractions (f : ∀ i, Morphism (P i) Q) :
    ∀ o, C((optionBlocks P Q f o).Realization, Q.Realization)
  | none => ⟨(oldTargetHomeomorph P Q).symm,
      (oldTargetHomeomorph P Q).symm.continuous⟩
  | some i => blockRetraction P Q f i

/-- Compatibility is DERIVED from the actual shared target and scalar retractions. -/
private theorem pieceRetractions_agree (f : ∀ i, Morphism (P i) Q) :
    ∀ o p, ∀ x : (optionBlocks P Q f o ⊓ optionBlocks P Q f p).Realization,
      pieceRetractions P Q f o (PreAbstractSimplicialComplex.Realization.inclusion inf_le_left x) =
        pieceRetractions P Q f p
          (PreAbstractSimplicialComplex.Realization.inclusion inf_le_right x) := by
  classical
  intro o p x
  cases o with
  | none =>
    cases p with
    | none => rfl
    | some j =>
      let y : (oldTarget P Q).Realization := ⟨x.point, x.support_mem.1⟩
      change (oldTargetHomeomorph P Q).symm y =
        blockRetraction P Q f j
          (PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f j) y)
      exact (blockRetraction_old P Q f j y).symm
  | some i =>
    cases p with
    | none =>
      let y : (oldTarget P Q).Realization := ⟨x.point, x.support_mem.2⟩
      change blockRetraction P Q f i
        (PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i) y) =
          (oldTargetHomeomorph P Q).symm y
      exact blockRetraction_old P Q f i y
    | some j =>
      by_cases hij : i = j
      · subst j
        rfl
      · have hy : x.point.weights.support ∈ oldTarget P Q := by
          rw [← oldTarget_intersection P Q f hij]
          exact x.support_mem
        let y : (oldTarget P Q).Realization := ⟨x.point, hy⟩
        exact (blockRetraction_old P Q f i y).trans (blockRetraction_old P Q f j y).symm

private theorem oldRange_iff (f : ∀ i, Morphism (P i) Q)
    (y : (cylinderFamily P Q f).Realization) :
    y ∈ Set.range (oldInclusion P Q f) ↔ y.point.weights.support ∈ oldTarget P Q := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (oldTargetHomeomorph P Q x).support_mem
  · intro hy
    let z : (oldTarget P Q).Realization := ⟨y.point, hy⟩
    refine ⟨(oldTargetHomeomorph P Q).symm z, ?_⟩
    apply PreAbstractSimplicialComplex.Realization.ext
    change (oldTargetHomeomorph P Q ((oldTargetHomeomorph P Q).symm z)).point = y.point
    rw [(oldTargetHomeomorph P Q).apply_symm_apply]

private theorem blockRange_iff (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (y : (cylinderFamily P Q f).Realization) :
    y ∈ Set.range (blockInclusion P Q f i) ↔ y.point.weights.support ∈ block P Q f i := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (blockHomeomorph P Q f i x).support_mem
  · intro hy
    let z : (block P Q f i).Realization := ⟨y.point, hy⟩
    refine ⟨(blockHomeomorph P Q f i).symm z, ?_⟩
    apply PreAbstractSimplicialComplex.Realization.ext
    change (blockHomeomorph P Q f i ((blockHomeomorph P Q f i).symm z)).point = y.point
    rw [(blockHomeomorph P Q f i).apply_symm_apply]

/-- The entire actual cylinder images intersect exactly in the unchanged old target image. -/
private theorem blockRange_intersection (f : ∀ i, Morphism (P i) Q) {i j : «I»} (hij : i ≠ j) :
    Set.range (blockInclusion P Q f i) ∩ Set.range (blockInclusion P Q f j) =
      Set.range (oldInclusion P Q f) := by
  ext y
  rw [Set.mem_inter_iff, blockRange_iff P Q f i, blockRange_iff P Q f j, oldRange_iff P Q f]
  rw [← oldTarget_intersection P Q f hij]
  rfl

private theorem oldBlock_global (f : ∀ i, Morphism (P i) Q) (i : «I») (q : Q.Realization) :
    blockInclusion P Q f i ((MappingCylinder.targetMorphism (f i)).realization q) =
      oldInclusion P Q f q := by
  change PreAbstractSimplicialComplex.Realization.inclusion (block_le_family P Q f i)
    (blockHomeomorph P Q f i ((MappingCylinder.targetMorphism (f i)).realization q)) =
      PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_family P Q f)
        (oldTargetHomeomorph P Q q)
  have h := congrArg
    (PreAbstractSimplicialComplex.Realization.inclusion (block_le_family P Q f i))
    (oldInBlock P Q f i q)
  simpa only [PreAbstractSimplicialComplex.Realization.inclusion_trans] using h

open Classical in
private def copiedInclusion (f : ∀ i, Morphism (P i) Q) (i : «I») :
    C((barycentricSubdivision (P i)).Realization, (cylinderFamily P Q f).Realization) :=
  (blockInclusion P Q f i).comp (MappingCylinder.domainMorphism (f i)).realization

private theorem copiedInclusion_isClosedEmbedding (f : ∀ i, Morphism (P i) Q) (i : «I») :
    IsClosedEmbedding (copiedInclusion P Q f i) :=
  (blockInclusion_isClosedEmbedding P Q f i).comp
    (MappingCylinder.isClosedEmbedding_domainMorphism (f i))

private theorem copied_old_disjoint (f : ∀ i, Morphism (P i) Q) (i : «I») :
    Disjoint (Set.range (copiedInclusion P Q f i)) (Set.range (oldInclusion P Q f)) := by
  rw [Set.disjoint_left]
  rintro y ⟨x, hx⟩ ⟨q, hq⟩
  have heq : (MappingCylinder.domainMorphism (f i)).realization x =
      (MappingCylinder.targetMorphism (f i)).realization q :=
    (blockInclusion_isClosedEmbedding P Q f i).injective
      (hx.trans ((oldBlock_global P Q f i q).trans hq).symm)
  exact (Set.disjoint_left.mp (MappingCylinder.domain_target_disjoint (f i)))
    ⟨x, rfl⟩ ⟨q, heq.symm⟩

private theorem copied_copied_disjoint (f : ∀ i, Morphism (P i) Q) {i j : «I»} (hij : i ≠ j) :
    Disjoint (Set.range (copiedInclusion P Q f i)) (Set.range (copiedInclusion P Q f j)) := by
  rw [Set.disjoint_left]
  rintro y ⟨x, hx⟩ ⟨z, hz⟩
  have hyi : y ∈ Set.range (blockInclusion P Q f i) :=
    ⟨(MappingCylinder.domainMorphism (f i)).realization x, hx⟩
  have hyj : y ∈ Set.range (blockInclusion P Q f j) :=
    ⟨(MappingCylinder.domainMorphism (f j)).realization z, hz⟩
  have hy : y ∈ Set.range (oldInclusion P Q f) := by
    rw [← blockRange_intersection P Q f hij]
    exact ⟨hyi, hyj⟩
  exact (Set.disjoint_left.mp (copied_old_disjoint P Q f i)) ⟨x, hx⟩ hy

private theorem cylinderFamily_faces (f : ∀ i, Morphism (P i) Q) (s : Finset (Labels (W := W) P)) :
    s ∈ cylinderFamily P Q f ↔ s ∈ oldTarget P Q ∨ ∃ i, s ∈ block P Q f i := by
  change s ∈ WeakFamilyUnionConstruction46.weakUnion (optionBlocks P Q f) ↔
    s ∈ oldTarget P Q ∨ ∃ i, s ∈ block P Q f i
  rw [WeakFamilyUnionConstruction46.mem_weakUnion (optionBlocks P Q f)]
  constructor
  · rintro ⟨o, ho⟩
    cases o with
    | none => exact Or.inl ho
    | some i => exact Or.inr ⟨i, ho⟩
  · rintro (ho | ⟨i, hi⟩)
    · exact ⟨none, ho⟩
    · exact ⟨some i, hi⟩

private theorem copiedInclusion_point (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (x : (barycentricSubdivision (P i)).Realization) :
    (copiedInclusion P Q f i x).point =
      (x.point.map (Sum.inl : Face (P i) → Face (P i) ⊕ W)).map (tag P i) := by
  change (blockInclusion P Q f i ((MappingCylinder.domainMorphism (f i)).realization x)).point =
    (x.point.map (Sum.inl : Face (P i) → Face (P i) ⊕ W)).map (tag P i)
  rw [blockInclusion_point, MappingCylinder.domainMorphism_point]

end TaggedFamilyComplexConstruction46

namespace FamilyCylinderRetractionConstruction46

open PreAbstractSimplicialComplex TaggedFamilyComplexConstruction46

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

open Classical in
private def familyRetraction (f : ∀ i, Morphism (P i) Q) :
    C((cylinderFamily P Q f).Realization, Q.Realization) :=
  WeakFamilyUnionConstruction46.unionDesc (optionBlocks P Q f)
    (pieceRetractions P Q f) (pieceRetractions_agree P Q f)

private theorem familyRetraction_old (f : ∀ i, Morphism (P i) Q) (q : Q.Realization) :
    familyRetraction P Q f (oldInclusion P Q f q) = q := by
  calc
    familyRetraction P Q f (oldInclusion P Q f q) =
        pieceRetractions P Q f none (oldTargetHomeomorph P Q q) :=
      WeakFamilyUnionConstruction46.unionDesc_component (optionBlocks P Q f)
        (pieceRetractions P Q f) (pieceRetractions_agree P Q f) none (oldTargetHomeomorph P Q q)
    _ = q := by
      change (oldTargetHomeomorph P Q).symm (oldTargetHomeomorph P Q q) = q
      exact (oldTargetHomeomorph P Q).symm_apply_apply q

private theorem familyRetraction_block (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (x : (MappingCylinder.complex (f i)).Realization) :
    familyRetraction P Q f (blockInclusion P Q f i x) = MappingCylinder.retraction (f i) x := by
  calc
    familyRetraction P Q f (blockInclusion P Q f i x) =
        pieceRetractions P Q f (some i) (blockHomeomorph P Q f i x) :=
      WeakFamilyUnionConstruction46.unionDesc_component (optionBlocks P Q f)
        (pieceRetractions P Q f) (pieceRetractions_agree P Q f) (some i)
        (blockHomeomorph P Q f i x)
    _ = MappingCylinder.retraction (f i) x := by
      change MappingCylinder.retraction (f i)
        ((blockHomeomorph P Q f i).symm (blockHomeomorph P Q f i x)) = _
      rw [(blockHomeomorph P Q f i).symm_apply_apply]

private theorem familyRetraction_copied (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (x : (barycentricSubdivision (P i)).Realization) :
    familyRetraction P Q f (copiedInclusion P Q f i x) =
      (f i).realization (barycentricHomeomorph (P i) x) := by
  change familyRetraction P Q f
      (blockInclusion P Q f i ((MappingCylinder.domainMorphism (f i)).realization x)) =
    (f i).realization (barycentricHomeomorph (P i) x)
  rw [familyRetraction_block]
  exact MappingCylinder.retraction_domain (f i) x

open Classical in
private def pieceHomotopy (f : ∀ i, Morphism (P i) Q) :
    ∀ o, ContinuousMap.Homotopy (WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) o)
      ((oldInclusion P Q f).comp (pieceRetractions P Q f o)) := by
  intro o
  cases o with
  | none =>
    let L : C((oldTarget P Q).Realization, (cylinderFamily P Q f).Realization) :=
      WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) none
    refine (ContinuousMap.Homotopy.refl L).cast rfl ?_
    apply ContinuousMap.ext
    intro x
    change L x = L (oldTargetHomeomorph P Q ((oldTargetHomeomorph P Q).symm x))
    rw [(oldTargetHomeomorph P Q).apply_symm_apply]
  | some i =>
    let R : C((block P Q f i).Realization,
        (MappingCylinder.complex (f i)).Realization) :=
      ⟨(blockHomeomorph P Q f i).symm, (blockHomeomorph P Q f i).symm.continuous⟩
    let H₀ := (MappingCylinder.deformation (f i)).compContinuousMap R
    let H := (ContinuousMap.Homotopy.refl (blockInclusion P Q f i)).comp H₀
    refine H.cast ?_ ?_
    · apply ContinuousMap.ext
      intro x
      change WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) (some i)
          (blockHomeomorph P Q f i ((blockHomeomorph P Q f i).symm x)) =
        WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) (some i) x
      rw [(blockHomeomorph P Q f i).apply_symm_apply]
    · apply ContinuousMap.ext
      intro x
      change blockInclusion P Q f i ((MappingCylinder.targetMorphism (f i)).realization
          (MappingCylinder.retraction (f i) ((blockHomeomorph P Q f i).symm x))) =
        oldInclusion P Q f (MappingCylinder.retraction (f i) ((blockHomeomorph P Q f i).symm x))
      exact oldBlock_global P Q f i _

private theorem pieceHomotopy_old (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (t : unitInterval) (x : (oldTarget P Q).Realization) :
    (pieceHomotopy P Q f (some i)).toContinuousMap
        (t, PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i) x) =
      (pieceHomotopy P Q f none).toContinuousMap (t, x) := by
  let q := (oldTargetHomeomorph P Q).symm x
  have h := oldInBlock P Q f i q
  have hx : (blockHomeomorph P Q f i).symm
      (PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i) x) =
        (MappingCylinder.targetMorphism (f i)).realization q := by
    apply (blockHomeomorph P Q f i).injective
    rw [(blockHomeomorph P Q f i).apply_symm_apply]
    exact (h.trans (congrArg
      (PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i))
      ((oldTargetHomeomorph P Q).apply_symm_apply x))).symm
  dsimp only [pieceHomotopy, ContinuousMap.Homotopy.cast, ContinuousMap.Homotopy.comp,
    ContinuousMap.Homotopy.compContinuousMap, ContinuousMap.Homotopy.refl]
  change blockInclusion P Q f i ((MappingCylinder.deformation (f i)).toContinuousMap
      (t, (blockHomeomorph P Q f i).symm
        (PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i) x))) =
    WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) none x
  have hfixed := MappingCylinder.deformation_target_fixed (f i) t q
  change (MappingCylinder.deformation (f i)).toContinuousMap
      (t, (MappingCylinder.targetMorphism (f i)).realization q) =
    (MappingCylinder.targetMorphism (f i)).realization q at hfixed
  rw [hx, hfixed]
  have hblock :
      blockInclusion P Q f i ((MappingCylinder.targetMorphism (f i)).realization q) =
        oldInclusion P Q f q := oldBlock_global P Q f i q
  have hold : oldInclusion P Q f q =
      WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) none x := by
    change WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) none
      (oldTargetHomeomorph P Q ((oldTargetHomeomorph P Q).symm x)) =
        WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) none x
    exact congrArg (WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) none)
      ((oldTargetHomeomorph P Q).apply_symm_apply x)
  exact hblock.trans hold

private theorem pieceHomotopy_agree (f : ∀ i, Morphism (P i) Q) :
    ∀ o p, ∀ x : (optionBlocks P Q f o ⊓ optionBlocks P Q f p).Realization,
      ∀ t : unitInterval,
        (pieceHomotopy P Q f o).toContinuousMap
            (t, PreAbstractSimplicialComplex.Realization.inclusion inf_le_left x) =
          (pieceHomotopy P Q f p).toContinuousMap
            (t, PreAbstractSimplicialComplex.Realization.inclusion inf_le_right x) := by
  classical
  intro o p x t
  cases o with
  | none =>
    cases p with
    | none => rfl
    | some j =>
      let y : (oldTarget P Q).Realization := ⟨x.point, x.support_mem.1⟩
      change (pieceHomotopy P Q f none).toContinuousMap (t, y) =
        (pieceHomotopy P Q f (some j)).toContinuousMap
          (t, PreAbstractSimplicialComplex.Realization.inclusion
            (oldTarget_le_block P Q f j) y)
      exact (pieceHomotopy_old P Q f j t y).symm
  | some i =>
    cases p with
    | none =>
      let y : (oldTarget P Q).Realization := ⟨x.point, x.support_mem.2⟩
      change (pieceHomotopy P Q f (some i)).toContinuousMap
          (t, PreAbstractSimplicialComplex.Realization.inclusion
            (oldTarget_le_block P Q f i) y) =
        (pieceHomotopy P Q f none).toContinuousMap (t, y)
      exact pieceHomotopy_old P Q f i t y
    | some j =>
      by_cases hij : i = j
      · subst j
        rfl
      · have hy : x.point.weights.support ∈ oldTarget P Q := by
          rw [← oldTarget_intersection P Q f hij]
          exact x.support_mem
        let y : (oldTarget P Q).Realization := ⟨x.point, hy⟩
        change (pieceHomotopy P Q f (some i)).toContinuousMap
            (t, PreAbstractSimplicialComplex.Realization.inclusion
              (oldTarget_le_block P Q f i) y) =
          (pieceHomotopy P Q f (some j)).toContinuousMap
            (t, PreAbstractSimplicialComplex.Realization.inclusion
              (oldTarget_le_block P Q f j) y)
        exact (pieceHomotopy_old P Q f i t y).trans
          (pieceHomotopy_old P Q f j t y).symm

open Classical in
private def curriedPieces (f : ∀ i, Morphism (P i) Q) :
    ∀ o, C((optionBlocks P Q f o).Realization,
      C(unitInterval, (cylinderFamily P Q f).Realization)) := by
  intro o
  let H : C((optionBlocks P Q f o).Realization × unitInterval,
      (cylinderFamily P Q f).Realization) :=
    ⟨fun z => (pieceHomotopy P Q f o).toContinuousMap (z.2, z.1),
      (pieceHomotopy P Q f o).toContinuousMap.continuous.comp
        (continuous_snd.prodMk continuous_fst)⟩
  exact H.curry

private theorem curriedPieces_agree (f : ∀ i, Morphism (P i) Q) :
    ∀ o p, ∀ x : (optionBlocks P Q f o ⊓ optionBlocks P Q f p).Realization,
      curriedPieces P Q f o (PreAbstractSimplicialComplex.Realization.inclusion inf_le_left x) =
        curriedPieces P Q f p
          (PreAbstractSimplicialComplex.Realization.inclusion inf_le_right x) := by
  intro o p x
  apply ContinuousMap.ext
  intro t
  exact pieceHomotopy_agree P Q f o p x t

open Classical in
private def curriedFamily (f : ∀ i, Morphism (P i) Q) :
    C((cylinderFamily P Q f).Realization, C(unitInterval, (cylinderFamily P Q f).Realization)) :=
  WeakFamilyUnionConstruction46.unionDesc (optionBlocks P Q f)
    (curriedPieces P Q f) (curriedPieces_agree P Q f)

private theorem curriedFamily_component (f : ∀ i, Morphism (P i) Q) (o : Option «I»)
    (x : (optionBlocks P Q f o).Realization) (t : unitInterval) :
    curriedFamily P Q f (WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) o x) t =
      (pieceHomotopy P Q f o).toContinuousMap (t, x) :=
  congrArg (fun g : C(unitInterval, (cylinderFamily P Q f).Realization) => g t)
    (WeakFamilyUnionConstruction46.unionDesc_component (optionBlocks P Q f)
      (curriedPieces P Q f) (curriedPieces_agree P Q f) o x)

open Classical in
/-- Ordinary joint continuity follows by weak-face descent and compact-open interval evaluation. -/
private def familyHomotopy (f : ∀ i, Morphism (P i) Q) :
    ContinuousMap.Homotopy (ContinuousMap.id (cylinderFamily P Q f).Realization)
      ((oldInclusion P Q f).comp (familyRetraction P Q f)) where
  toFun z := curriedFamily P Q f z.2 z.1
  continuous_toFun := ((curriedFamily P Q f).continuous.comp continuous_snd).eval continuous_fst
  map_zero_left x := by
    let o := WeakFamilyUnionConstruction46.sourceIndex (optionBlocks P Q f) x
    let y : (optionBlocks P Q f o).Realization :=
      ⟨x.point, WeakFamilyUnionConstruction46.sourceIndex_support (optionBlocks P Q f) x⟩
    let z : (cylinderFamily P Q f).Realization :=
      WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) o y
    have hz : z = x := by
      apply PreAbstractSimplicialComplex.Realization.ext
      rfl
    have hc : curriedFamily P Q f z 0 =
        (pieceHomotopy P Q f o).toContinuousMap (0, y) :=
      curriedFamily_component P Q f o y 0
    have hzero : (pieceHomotopy P Q f o).toContinuousMap (0, y) = z :=
      (pieceHomotopy P Q f o).map_zero_left y
    exact (congrArg (fun a : (cylinderFamily P Q f).Realization =>
      curriedFamily P Q f a 0) hz).symm.trans (hc.trans (hzero.trans hz))
  map_one_left x := by
    let o := WeakFamilyUnionConstruction46.sourceIndex (optionBlocks P Q f) x
    let y : (optionBlocks P Q f o).Realization :=
      ⟨x.point, WeakFamilyUnionConstruction46.sourceIndex_support (optionBlocks P Q f) x⟩
    let z : (cylinderFamily P Q f).Realization :=
      WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) o y
    have hz : z = x := by
      apply PreAbstractSimplicialComplex.Realization.ext
      rfl
    have hc : curriedFamily P Q f z 1 =
        (pieceHomotopy P Q f o).toContinuousMap (1, y) :=
      curriedFamily_component P Q f o y 1
    have hone : (pieceHomotopy P Q f o).toContinuousMap (1, y) =
        oldInclusion P Q f (pieceRetractions P Q f o y) :=
      (pieceHomotopy P Q f o).map_one_left y
    have hr : familyRetraction P Q f z = pieceRetractions P Q f o y :=
      WeakFamilyUnionConstruction46.unionDesc_component (optionBlocks P Q f)
        (pieceRetractions P Q f) (pieceRetractions_agree P Q f) o y
    exact (congrArg (fun a : (cylinderFamily P Q f).Realization =>
      curriedFamily P Q f a 1) hz).symm.trans (hc.trans (hone.trans
        (congrArg (oldInclusion P Q f)
          (hr.symm.trans (congrArg (familyRetraction P Q f) hz)))))

private theorem familyHomotopy_old (f : ∀ i, Morphism (P i) Q) (t : unitInterval)
    (q : Q.Realization) :
    (familyHomotopy P Q f).toContinuousMap (t, oldInclusion P Q f q) =
      oldInclusion P Q f q := by
  change curriedFamily P Q f (oldInclusion P Q f q) t = oldInclusion P Q f q
  change curriedFamily P Q f
      (WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) none
        (oldTargetHomeomorph P Q q)) t = oldInclusion P Q f q
  rw [curriedFamily_component P Q f none (oldTargetHomeomorph P Q q) t]
  dsimp only [pieceHomotopy, ContinuousMap.Homotopy.cast, ContinuousMap.Homotopy.refl]
  change WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) none
      (oldTargetHomeomorph P Q q) = oldInclusion P Q f q
  rfl

open Classical in
private def familyHomotopyRelativeOld (f : ∀ i, Morphism (P i) Q) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (cylinderFamily P Q f).Realization)
      ((oldInclusion P Q f).comp (familyRetraction P Q f)) (Set.range (oldInclusion P Q f)) where
  toHomotopy := familyHomotopy P Q f
  prop' t x hx := by
    obtain ⟨q, rfl⟩ := hx
    exact familyHomotopy_old P Q f t q

end FamilyCylinderRetractionConstruction46

namespace FamilyCylinderPushoutConstruction46

open CategoryTheory Limits PreAbstractSimplicialComplex TaggedFamilyComplexConstruction46

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

open Classical in
private def pieceMaps (f : ∀ i, Morphism (P i) Q) {Z : Type*} [TopologicalSpace Z]
    (g : C((oldTarget P Q).Realization, Z)) (h : ∀ i, C((block P Q f i).Realization, Z)) :
    ∀ o, C((optionBlocks P Q f o).Realization, Z)
  | none => g
  | some i => h i

private theorem pieceMaps_agree (f : ∀ i, Morphism (P i) Q)
    {Z : Type*} [TopologicalSpace Z] (g : C((oldTarget P Q).Realization, Z))
    (h : ∀ i, C((block P Q f i).Realization, Z))
    (hold : ∀ i, ∀ x : (oldTarget P Q).Realization,
      h i (PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i) x) = g x)
        :
    ∀ o p, ∀ x : (optionBlocks P Q f o ⊓ optionBlocks P Q f p).Realization,
      pieceMaps P Q f g h o (PreAbstractSimplicialComplex.Realization.inclusion inf_le_left x) =
        pieceMaps P Q f g h p (PreAbstractSimplicialComplex.Realization.inclusion inf_le_right x) :=
          by
  classical
  intro o p x
  cases o with
  | none =>
    cases p with
    | none => rfl
    | some j =>
      let y : (oldTarget P Q).Realization := ⟨x.point, x.support_mem.1⟩
      exact (hold j y).symm
  | some i =>
    cases p with
    | none =>
      let y : (oldTarget P Q).Realization := ⟨x.point, x.support_mem.2⟩
      exact hold i y
    | some j =>
      by_cases hij : i = j
      · subst j
        rfl
      · have hy : x.point.weights.support ∈ oldTarget P Q := by
          rw [← oldTarget_intersection P Q f hij]
          exact x.support_mem
        let y : (oldTarget P Q).Realization := ⟨x.point, hy⟩
        exact (hold i y).trans (hold j y).symm

open Classical in
private def overlapSum : TopCat.{max u v w} :=
  TopCat.of (Σ _ : «I», (oldTarget P Q).Realization)

open Classical in
private def blockSum (f : ∀ i, Morphism (P i) Q) : TopCat.{max u v w} :=
  TopCat.of (Σ i : «I», (block P Q f i).Realization)

open Classical in
private def overlapToBlocks (f : ∀ i, Morphism (P i) Q) :
    overlapSum P Q ⟶ blockSum P Q f :=
  TopCat.ofHom
    ⟨Sigma.map (id : «I» → «I»)
      (fun i => PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i)),
      Continuous.sigma_map (fun i =>
        PreAbstractSimplicialComplex.Realization.continuous_inclusion (oldTarget_le_block P Q f i))⟩

open Classical in
private def overlapFold :
    overlapSum P Q ⟶ TopCat.of (oldTarget P Q).Realization :=
  TopCat.ofHom ⟨fun p => p.2, continuous_sigma (fun _ => continuous_id)⟩

open Classical in
private def blocksToFamily (f : ∀ i, Morphism (P i) Q) :
    blockSum P Q f ⟶ TopCat.of (cylinderFamily P Q f).Realization :=
  TopCat.ofHom ⟨fun p => WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) (some p.1)
    p.2,
    continuous_sigma (fun i =>
      (WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) (some i)).continuous)⟩

open Classical in
private def oldToFamily (f : ∀ i, Morphism (P i) Q) :
    TopCat.of (oldTarget P Q).Realization ⟶ TopCat.of (cylinderFamily P Q f).Realization :=
  TopCat.ofHom (WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) none)

/-- No gluing presentation is supplied: its universal map is constructed by actual weak-face
  descent. -/
private theorem cylinderFamily_isPushout (f : ∀ i, Morphism (P i) Q) :
    IsPushout (overlapToBlocks P Q f) (overlapFold P Q)
      (blocksToFamily P Q f) (oldToFamily P Q f) := by
  let comm : CommSq (overlapToBlocks P Q f) (overlapFold P Q)
      (blocksToFamily P Q f) (oldToFamily P Q f) := by
    refine ⟨?_⟩
    apply TopCat.ext
    rintro ⟨i, x⟩
    apply PreAbstractSimplicialComplex.Realization.ext
    rfl
  apply IsPushout.of_isColimit' comm
  apply PushoutCocone.isColimitAux'
  intro s
  let g : C((oldTarget P Q).Realization, s.pt) := s.inr.hom
  let h : ∀ i, C((block P Q f i).Realization, s.pt) := fun i =>
    ⟨fun x => s.inl ⟨i, x⟩, s.inl.hom.continuous.comp (continuous_sigmaMk (i := i))⟩
  have hold : ∀ i, ∀ x : (oldTarget P Q).Realization,
      h i (PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i) x) = g x
        := by
    intro i x
    have hc := ConcreteCategory.congr_hom s.condition ⟨i, x⟩
    exact hc
  let d := TopCat.ofHom (WeakFamilyUnionConstruction46.unionDesc (optionBlocks P Q f)
    (pieceMaps P Q f g h) (pieceMaps_agree P Q f g h hold))
  refine ⟨d, ?_, ?_, ?_⟩
  · apply TopCat.ext
    rintro ⟨i, x⟩
    exact WeakFamilyUnionConstruction46.unionDesc_component (optionBlocks P Q f)
      (pieceMaps P Q f g h) (pieceMaps_agree P Q f g h hold) (some i) x
  · apply TopCat.ext
    intro x
    exact WeakFamilyUnionConstruction46.unionDesc_component (optionBlocks P Q f)
      (pieceMaps P Q f g h) (pieceMaps_agree P Q f g h hold) none x
  · intro m hmBlocks hmOld
    apply TopCat.hom_ext
    apply WeakFamilyUnionConstruction46.unionDesc_unique (optionBlocks P Q f)
      (pieceMaps P Q f g h) (pieceMaps_agree P Q f g h hold) m.hom
    intro o x
    cases o with
    | none => exact ConcreteCategory.congr_hom hmOld x
    | some i => exact ConcreteCategory.congr_hom hmBlocks ⟨i, x⟩

end FamilyCylinderPushoutConstruction46

namespace FamilyConeComplexConstruction46

open CategoryTheory PreAbstractSimplicialComplex TaggedFamilyComplexConstruction46

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

private abbrev ConeLabels := Labels (W := W) P ⊕ «I»

open Classical in
private def apexTag (i : «I») : PUnit.{s + 1} ↪ «I» :=
  ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩

open Classical in
private def coneTag (i : «I») : (Face (P i) ⊕ W) ⊕ PUnit.{max v w + 1} ↪ ConeLabels (W := W) P :=
  Function.Embedding.sumMap (tag P i) (apexTag.{u, max v w} i)

open Classical in
private def cylinderPart (f : ∀ i, Morphism (P i) Q) :
    PreAbstractSimplicialComplex (ConeLabels (W := W) P) :=
  MappingCylinder.relabelComplex (cylinderFamily P Q f) Function.Embedding.inl

open Classical in
private def attachedBlock (i : «I») : PreAbstractSimplicialComplex (ConeLabels (W := W) P) :=
  MappingCylinder.relabelComplex (MappingCylinder.coneComplex (MappingCylinder.domainComplex (P i)
    W))
    (coneTag (W := W) P i)

open Classical in
private def copiedBlock (i : «I») : PreAbstractSimplicialComplex (ConeLabels (W := W) P) :=
  MappingCylinder.relabelComplex (MappingCylinder.domainComplex (P i) W)
    ((tag P i).trans Function.Embedding.inl)

open Classical in
private def attachedFamily : PreAbstractSimplicialComplex (ConeLabels (W := W) P) := ⨆ i,
  attachedBlock (W := W) P i
open Classical in
private def copiedFamily : PreAbstractSimplicialComplex (ConeLabels (W := W) P) := ⨆ i, copiedBlock
  (W := W) P i

open Classical in
private def associatedFamily (f : ∀ i, Morphism (P i) Q) :
    PreAbstractSimplicialComplex (ConeLabels (W := W) P) := cylinderPart P Q f ⊔ attachedFamily (W
      := W) P

private theorem copied_le_cylinder (f : ∀ i, Morphism (P i) Q) (i : «I») :
    copiedBlock (W := W) P i ≤ cylinderPart P Q f := by
  classical
  let : DecidableEq (ConeLabels (W := W) P) := Classical.decEq _
  let : DecidableEq (Labels (W := W) P) := Classical.decEq _
  let : DecidableEq (Face (P i) ⊕ W) := Classical.decEq _
  intro s hs
  change ∃ a : Finset (Face (P i) ⊕ W),
    a ∈ MappingCylinder.domainComplex (P i) W ∧
      a.image ((tag P i).trans Function.Embedding.inl) = s at hs
  obtain ⟨a, ha, rfl⟩ := hs
  change ∃ b : Finset (Labels (W := W) P), b ∈ cylinderFamily P Q f ∧
    b.image Function.Embedding.inl = a.image ((tag P i).trans Function.Embedding.inl)
  refine ⟨a.image (tag P i), ?_, ?_⟩
  · apply block_le_family P Q f i
    change ∃ b : Finset (Face (P i) ⊕ W), b ∈ MappingCylinder.complex (f i) ∧
      b.image (tag P i) = a.image (tag P i)
    exact ⟨a, MappingCylinder.domainComplex_le (f i) ha, rfl⟩
  · rw [Finset.image_image]
    rfl

private theorem copied_le_attached (i : «I») :
    copiedBlock (W := W) P i ≤ attachedBlock (W := W) P i := by
  classical
  let : DecidableEq (ConeLabels (W := W) P) := Classical.decEq _
  let : DecidableEq (Face (P i) ⊕ W) := Classical.decEq _
  let : DecidableEq ((Face (P i) ⊕ W) ⊕ PUnit.{max v w + 1}) := Classical.decEq _
  intro s hs
  change ∃ a : Finset (Face (P i) ⊕ W),
    a ∈ MappingCylinder.domainComplex (P i) W ∧
      a.image ((tag P i).trans Function.Embedding.inl) = s at hs
  obtain ⟨a, ha, rfl⟩ := hs
  change ∃ b : Finset ((Face (P i) ⊕ W) ⊕ PUnit.{max v w + 1}),
    b ∈ MappingCylinder.coneComplex (MappingCylinder.domainComplex (P i) W) ∧
      b.image (coneTag (W := W) P i) =
        a.image ((tag P i).trans Function.Embedding.inl)
  refine ⟨a.image (Function.Embedding.inl : Face (P i) ⊕ W ↪
    (Face (P i) ⊕ W) ⊕ PUnit.{max v w + 1}), ?_, ?_⟩
  · apply MappingCylinder.cone_base_le (MappingCylinder.domainComplex (P i) W)
    change ∃ b : Finset (Face (P i) ⊕ W), b ∈ MappingCylinder.domainComplex (P i) W ∧
      b.image (Function.Embedding.inl : Face (P i) ⊕ W ↪
        (Face (P i) ⊕ W) ⊕ PUnit.{max v w + 1}) =
          a.image (Function.Embedding.inl : Face (P i) ⊕ W ↪
            (Face (P i) ⊕ W) ⊕ PUnit.{max v w + 1})
    exact ⟨a, ha, rfl⟩
  · rw [Finset.image_image]
    rfl

/-- No apex lies in the cylinder part; the whole intersection is the actual copied domain. -/
private theorem cylinder_attached_intersection (f : ∀ i, Morphism (P i) Q) (i : «I») :
    cylinderPart P Q f ⊓ attachedBlock (W := W) P i = copiedBlock (W := W) P i := by
  classical
  let : DecidableEq (ConeLabels (W := W) P) := Classical.decEq _
  let : DecidableEq (Labels (W := W) P) := Classical.decEq _
  let : DecidableEq ((Face (P i) ⊕ W) ⊕ PUnit.{max v w + 1}) := Classical.decEq _
  apply le_antisymm
  · intro s hs
    obtain ⟨b, hb, hcy⟩ := hs.1
    obtain ⟨a, ha, hcone⟩ := hs.2
    change b.image (Function.Embedding.inl : Labels (W := W) P ↪
      ConeLabels (W := W) P) = s at hcy
    change a.image (coneTag (W := W) P i) = s at hcone
    have hright : a.toRight = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hi : Sum.inr i ∈ a.image (coneTag (W := W) P i) :=
        Finset.mem_image.mpr ⟨Sum.inr p, Finset.mem_toRight.mp hp, rfl⟩
      have hi' : Sum.inr i ∈ b.image (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W :=
        W) P) := by
        rw [hcy, ← hcone]
        exact hi
      obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hi'
      cases heq
    have hnonempty : a.toLeft.Nonempty := by
      obtain ⟨x, hx⟩ := (MappingCylinder.mem_coneComplex _ _).mp ha |>.1
      cases x with
      | inl x => exact ⟨x, Finset.mem_toLeft.mpr hx⟩
      | inr x => exact False.elim (by simpa only [hright, Finset.notMem_empty] using
          (Finset.mem_toRight.mpr hx))
    have hbase : a.toLeft ∈ MappingCylinder.domainComplex (P i) W :=
      ((MappingCylinder.mem_coneComplex _ _).mp ha).2.resolve_right hnonempty.ne_empty
    refine ⟨a.toLeft, hbase, ?_⟩
    have hsplit : a.toLeft.disjSum a.toRight = a := Finset.toLeft_disjSum_toRight
    rw [hright, Finset.disjSum_empty, Finset.map_eq_image] at hsplit
    calc
      a.toLeft.image ((tag P i).trans Function.Embedding.inl) =
          (a.toLeft.image (Function.Embedding.inl : Face (P i) ⊕ W ↪
            (Face (P i) ⊕ W) ⊕ PUnit)).image (coneTag (W := W) P i) := by
        rw [Finset.image_image]
        rfl
      _ = a.image (coneTag (W := W) P i) := congrArg (fun t => t.image (coneTag (W := W) P i))
        hsplit
      _ = s := hcone
  · exact le_inf (copied_le_cylinder P Q f i) (copied_le_attached (W := W) P i)

open Classical in
private def familyIndex : ConeLabels (W := W) P → Option «I»
  | Sum.inl (Sum.inl a) => some a.1
  | Sum.inl (Sum.inr _) => none
  | Sum.inr i => some i

/-- Every actual attached-cone vertex keeps its own tag; old target vertices never enter it. -/
private theorem attached_index (i : «I») (s : Finset (ConeLabels (W := W) P)) (hs : s ∈
  attachedBlock (W := W) P i)
    (z : ConeLabels (W := W) P) (hz : z ∈ s) : familyIndex (W := W) P z = some i := by
  classical
  let : DecidableEq (ConeLabels (W := W) P) := Classical.decEq _
  let : DecidableEq (Face (P i) ⊕ W) := Classical.decEq _
  let : DecidableEq ((Face (P i) ⊕ W) ⊕ PUnit.{max v w + 1}) := Classical.decEq _
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  cases x with
  | inr p => rfl
  | inl y =>
    have hy : y ∈ a.toLeft := Finset.mem_toLeft.mpr hx
    have hbase : a.toLeft ∈ MappingCylinder.domainComplex (P i) W :=
      ((MappingCylinder.mem_coneComplex _ _).mp ha).2.resolve_right (by
        intro hempty
        simp only [hempty, Finset.notMem_empty] at hy)
    obtain ⟨b, hb, hbeq⟩ := hbase
    change b.image (Function.Embedding.inl : Face (P i) ↪ Face (P i) ⊕ W) =
      a.toLeft at hbeq
    have hy' : y ∈ b.image (Function.Embedding.inl : Face (P i) ↪ Face (P i) ⊕ W) := by
      rw [hbeq]
      exact hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy'
    rfl

private theorem attached_disjoint_faces {i j : «I»} (hij : i ≠ j) :
    attachedBlock (W := W) P i ⊓ attachedBlock (W := W) P j = ⊥ := by
  classical
  apply le_antisymm
  · intro s hs
    obtain ⟨z, hz⟩ := ((attachedBlock (W := W) P i).isRelLowerSet_faces hs.1).1
    exact hij (Option.some.inj ((attached_index (W := W) P i s hs.1 z hz).symm.trans
      (attached_index (W := W) P j s hs.2 z hz)))
  · exact bot_le

private theorem copiedFamily_le_cylinder (f : ∀ i, Morphism (P i) Q) :
    copiedFamily (W := W) P ≤ cylinderPart P Q f :=
  iSup_le (copied_le_cylinder P Q f)

private theorem copiedFamily_le_attached : copiedFamily (W := W) P ≤ attachedFamily (W := W) P :=
  iSup_le (fun i => (copied_le_attached (W := W) P i).trans (le_iSup (attachedBlock (W := W) P) i))

private theorem aggregate_intersection (f : ∀ i, Morphism (P i) Q) :
    cylinderPart P Q f ⊓ attachedFamily (W := W) P = copiedFamily (W := W) P := by
  classical
  apply le_antisymm
  · intro s hs
    obtain ⟨i, hi⟩ := (WeakFamilyUnionConstruction46.mem_weakUnion (attachedBlock (W := W) P) s).mp
      hs.2
    have hc : s ∈ copiedBlock (W := W) P i := by
      rw [← cylinder_attached_intersection P Q f i]
      exact ⟨hs.1, hi⟩
    exact (le_iSup (copiedBlock (W := W) P) i) hc
  · exact le_inf (copiedFamily_le_cylinder P Q f) (copiedFamily_le_attached (W := W) P)

/-- This is the actual ordinary weak-realization attachment pushout for the ENTIRE cone family. -/
private theorem associatedFamily_isPushout (f : ∀ i, Morphism (P i) Q) :
    CategoryTheory.IsPushout
      (TopCat.ofHom (MappingCylinder.inclusionMorphism (copiedFamily_le_cylinder P Q
        f)).realization)
      (TopCat.ofHom (MappingCylinder.inclusionMorphism (copiedFamily_le_attached (W := W)
        P)).realization)
      (TopCat.ofHom (MappingCylinder.inclusionMorphism
        (le_sup_left : cylinderPart P Q f ≤ associatedFamily P Q f)).realization)
      (TopCat.ofHom (MappingCylinder.inclusionMorphism
        (le_sup_right : attachedFamily (W := W) P ≤ associatedFamily P Q f)).realization) :=
  MappingCylinder.isPushout_union_of_intersection _ _ _ (aggregate_intersection P Q f) _ _

end FamilyConeComplexConstruction46

namespace FamilyConeComparisonsConstruction46

open CategoryTheory PreAbstractSimplicialComplex TaggedFamilyComplexConstruction46
  FamilyConeComplexConstruction46

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

open Classical in
private def sigmaHomeomorph {J : Type*} {X Y : J → Type*}
    [∀ j, TopologicalSpace (X j)] [∀ j, TopologicalSpace (Y j)]
    (e : ∀ j, X j ≃ₜ Y j) : (Σ j, X j) ≃ₜ (Σ j, Y j) where
  toFun := Sigma.map (id : J → J) (fun j => e j)
  invFun := Sigma.map (id : J → J) (fun j => (e j).symm)
  left_inv := by
    rintro ⟨j, x⟩
    change ⟨j, (e j).symm (e j x)⟩ = (⟨j, x⟩ : Σ j, X j)
    rw [(e j).symm_apply_apply]
  right_inv := by
    rintro ⟨j, y⟩
    change ⟨j, e j ((e j).symm y)⟩ = (⟨j, y⟩ : Σ j, Y j)
    rw [(e j).apply_symm_apply]
  continuous_toFun := Continuous.sigma_map (fun j => (e j).continuous)
  continuous_invFun := Continuous.sigma_map (fun j => (e j).symm.continuous)

private theorem copied_disjoint_faces {i j : «I»} (hij : i ≠ j) :
    copiedBlock (W := W) P i ⊓ copiedBlock (W := W) P j = ⊥ := by
  apply le_antisymm
  · rw [← attached_disjoint_faces (W := W) P hij]
    exact inf_le_inf (copied_le_attached (W := W) P i) (copied_le_attached (W := W) P j)
  · exact bot_le

open Classical in
private def copiedSigmaHomeomorph :
    (Σ i, (MappingCylinder.domainComplex (P i) W).Realization) ≃ₜ (copiedFamily (W := W)
      P).Realization :=
  (sigmaHomeomorph (fun i => MappingCylinder.relabelHomeomorph
    (MappingCylinder.domainComplex (P i) W) ((tag P i).trans Function.Embedding.inl))).trans
      (WeakFamilyUnionConstruction46.disjointUnionHomeomorph (copiedBlock (W := W) P)
        (fun _ _ hij => copied_disjoint_faces P hij))

open Classical in
private def scalarConeHomeomorph (i : «I») (hfinite : Finite (Face (P i))) :
    TopCat.cone (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization) ≃ₜ
      (attachedBlock (W := W) P i).Realization := by
  letI := hfinite
  letI := MappingCylinder.finiteFaces_domainComplex (P i) W
  exact (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex (P i) W)).trans
    (MappingCylinder.relabelHomeomorph
      (MappingCylinder.coneComplex (MappingCylinder.domainComplex (P i) W)) (coneTag (W := W) P i))

open Classical in
private def ordinaryConeSigmaHomeomorph (hfinite : ∀ i, Finite (Face (P i))) :
    (Σ i, TopCat.cone (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization)) ≃ₜ
      (attachedFamily (W := W) P).Realization :=
  (sigmaHomeomorph (fun i => scalarConeHomeomorph P i (hfinite i))).trans
    (WeakFamilyUnionConstruction46.disjointUnionHomeomorph (attachedBlock (W := W) P)
      (fun _ _ hij => attached_disjoint_faces (W := W) P hij))

private theorem copiedSigmaHomeomorph_point (i : «I»)
    (x : (MappingCylinder.domainComplex (P i) W).Realization) :
    (copiedSigmaHomeomorph P ⟨i, x⟩).point =
      x.point.map ((tag P i).trans Function.Embedding.inl) :=
  MappingCylinder.relabelMorphism_point (MappingCylinder.domainComplex (P i) W)
    ((tag P i).trans Function.Embedding.inl) x

private theorem coneSigmaHomeomorph_base (hfinite : ∀ i, Finite (Face (P i))) (i : «I»)
    (x : (MappingCylinder.domainComplex (P i) W).Realization) :
    ordinaryConeSigmaHomeomorph P hfinite
      ⟨i, TopCat.coneBase (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization) x⟩ =
        PreAbstractSimplicialComplex.Realization.inclusion (copiedFamily_le_attached (W := W) P)
          (copiedSigmaHomeomorph P ⟨i, x⟩) := by
  let := hfinite i
  let := MappingCylinder.finiteFaces_domainComplex (P i) W
  apply PreAbstractSimplicialComplex.Realization.ext
  change ((MappingCylinder.relabelMorphism
    (MappingCylinder.coneComplex (MappingCylinder.domainComplex (P i) W)) (coneTag (W := W) P
      i)).realization
      (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex (P i) W)
        (TopCat.coneBase (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization) x))).point
          = _
  rw [MappingCylinder.relabelMorphism_point, MappingCylinder.ordinaryConeHomeomorph_base,
    MappingCylinder.coneBaseMorphism_point,
    PreAbstractSimplicialComplex.Realization.inclusion_point, copiedSigmaHomeomorph_point,
    Convexity.StdSimplex.map_map]
  rfl

/-- The actual empty family has no copied-domain or cone points; the old cylinder is retained. -/
private theorem associatedFamily_empty_index (f : ∀ i, Morphism (P i) Q) [IsEmpty «I»] :
    associatedFamily P Q f = MappingCylinder.relabelComplex (oldTarget P Q) Function.Embedding.inl
      := by
  have hc : cylinderFamily P Q f = oldTarget P Q := cylinderFamily_empty_index P Q f
  have ha : attachedFamily (W := W) P = ⊥ := by
    apply le_antisymm
    · apply iSup_le
      intro i
      exact isEmptyElim i
    · exact bot_le
  change MappingCylinder.relabelComplex (cylinderFamily P Q f) Function.Embedding.inl ⊔
    attachedFamily (W := W) P = _
  rw [hc, ha, sup_bot_eq]

end FamilyConeComparisonsConstruction46

namespace OriginalCylinderSpanConstruction46

open CategoryTheory Limits PreAbstractSimplicialComplex TaggedFamilyComplexConstruction46
open FamilyCylinderPushoutConstruction46 FamilyConeComparisonsConstruction46

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

private abbrev LiftedBlocks (f : ∀ i, Morphism (P i) Q) :=
  Σ i, ULift.{max u v w} (MappingCylinder.complex (f i)).Realization

open Classical in
private def oldHomeomorph : ULift.{max u v w} Q.Realization ≃ₜ (oldTarget P Q).Realization :=
  Homeomorph.ulift.trans (oldTargetHomeomorph P Q)

open Classical in
private def overlapHomeomorph : (Σ _ : «I», ULift.{max u v w} Q.Realization) ≃ₜ overlapSum P Q :=
  sigmaHomeomorph (fun _ : «I» => oldHomeomorph P Q)

open Classical in
private def blocksHomeomorph (f : ∀ i, Morphism (P i) Q) :
    LiftedBlocks P Q f ≃ₜ blockSum P Q f :=
  sigmaHomeomorph (fun i => Homeomorph.ulift.trans (blockHomeomorph P Q f i))

open Classical in
private def actualBoundary (f : ∀ i, Morphism (P i) Q) :
    TopCat.of ((Σ _ : «I», ULift.{max u v w} Q.Realization)) ⟶ TopCat.of (LiftedBlocks P Q f) :=
  TopCat.ofHom ⟨Sigma.map (id : «I» → «I») (fun i q =>
      ULift.up ((MappingCylinder.targetMorphism (f i)).realization q.down)),
    Continuous.sigma_map (fun i => continuous_uliftUp.comp
      ((MappingCylinder.targetMorphism (f i)).realization.continuous.comp continuous_uliftDown))⟩

open Classical in
private def actualFold : TopCat.of ((Σ _ : «I», ULift.{max u v w} Q.Realization)) ⟶ TopCat.of
  (ULift.{max u v w} Q.Realization) :=
  TopCat.ofHom ⟨fun p => p.2, continuous_sigma (fun _ => continuous_id)⟩

open Classical in
private def actualBlocks (f : ∀ i, Morphism (P i) Q) :
    TopCat.of (LiftedBlocks P Q f) ⟶ TopCat.of (cylinderFamily P Q f).Realization :=
  TopCat.ofHom ⟨fun p => blockInclusion P Q f p.1 p.2.down,
    continuous_sigma (fun i => (blockInclusion P Q f i).continuous.comp continuous_uliftDown)⟩

open Classical in
private def actualOld (f : ∀ i, Morphism (P i) Q) :
    TopCat.of (ULift.{max u v w} Q.Realization) ⟶ TopCat.of (cylinderFamily P Q f).Realization :=
  TopCat.ofHom ⟨fun q => oldInclusion P Q f q.down,
    (oldInclusion P Q f).continuous.comp continuous_uliftDown⟩

/-- The unchanged scalar target maps and their actual family are the ordinary pushout span. -/
private theorem actualCylinderFamily_isPushout (f : ∀ i, Morphism (P i) Q) :
    IsPushout (actualBoundary P Q f) (actualFold.{u, v, w} Q) (actualBlocks P Q f) (actualOld P Q f)
      := by
  let e₁ : TopCat.of ((Σ _ : «I», ULift.{max u v w} Q.Realization)) ≅ overlapSum P Q :=
    TopCat.isoOfHomeo (overlapHomeomorph P Q)
  let e₂ : TopCat.of (LiftedBlocks P Q f) ≅ blockSum P Q f :=
    TopCat.isoOfHomeo (blocksHomeomorph P Q f)
  let e₃ : TopCat.of (ULift.{max u v w} Q.Realization) ≅ TopCat.of (oldTarget P Q).Realization :=
    TopCat.isoOfHomeo (oldHomeomorph P Q)
  refine (cylinderFamily_isPushout P Q f).of_iso' e₁ e₂ e₃ (Iso.refl _) ?_ ?_ ?_ ?_
  · apply ConcreteCategory.hom_ext
    rintro ⟨i, q⟩
    change (⟨i, PreAbstractSimplicialComplex.Realization.inclusion
      (oldTarget_le_block P Q f i) (oldTargetHomeomorph P Q q.down)⟩ :
        Σ k, (block P Q f k).Realization) =
      ⟨i, blockHomeomorph P Q f i ((MappingCylinder.targetMorphism (f i)).realization q.down)⟩
    exact congrArg (fun z : (block P Q f i).Realization =>
      (⟨i, z⟩ : Σ k, (block P Q f k).Realization)) (oldInBlock P Q f i q.down).symm
  · apply ConcreteCategory.hom_ext
    rintro ⟨i, q⟩
    rfl
  · apply ConcreteCategory.hom_ext
    rintro ⟨i, x⟩
    rfl
  · apply ConcreteCategory.hom_ext
    intro q
    rfl

end OriginalCylinderSpanConstruction46

namespace OrdinaryConeFamilyPushoutConstruction46

open CategoryTheory Limits PreAbstractSimplicialComplex TaggedFamilyComplexConstruction46
open FamilyConeComplexConstruction46 FamilyConeComparisonsConstruction46

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

open Classical in
private def domainSum (W : Type w) : TopCat.{max u v w} :=
  TopCat.of (Σ i, (MappingCylinder.domainComplex (P i) W).Realization)

open Classical in
private def coneSum (W : Type w) : TopCat.{max u v w} :=
  TopCat.of (Σ i, TopCat.cone (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization))

open Classical in
private def domainsToCylinder (f : ∀ i, Morphism (P i) Q) :
    domainSum P W ⟶ TopCat.of (cylinderFamily P Q f).Realization :=
  TopCat.ofHom ⟨fun p => blockInclusion P Q f p.1
      ((MappingCylinder.inclusionMorphism (MappingCylinder.domainComplex_le (f p.1))).realization
        p.2),
    continuous_sigma (fun i => (blockInclusion P Q f i).continuous.comp
      (MappingCylinder.inclusionMorphism (MappingCylinder.domainComplex_le (f
        i))).realization.continuous)⟩

open Classical in
private def domainsToCones : domainSum P W ⟶ coneSum P W :=
  TopCat.ofHom ⟨Sigma.map (id : «I» → «I») (fun i =>
      TopCat.coneBase (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization)),
    Continuous.sigma_map (fun i =>
      (TopCat.coneBase (TopCat.of (MappingCylinder.domainComplex (P i)
        W).Realization)).hom.continuous)⟩

open Classical in
private def cylinderToAssociated (f : ∀ i, Morphism (P i) Q) :
    TopCat.of (cylinderFamily P Q f).Realization ⟶ TopCat.of (associatedFamily P Q f).Realization :=
      by
  let h : (cylinderFamily P Q f).Realization ≃ₜ (cylinderPart P Q f).Realization :=
    MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
      (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)
  exact TopCat.ofHom ((⟨PreAbstractSimplicialComplex.Realization.inclusion le_sup_left,
    PreAbstractSimplicialComplex.Realization.continuous_inclusion le_sup_left⟩ :
      C((cylinderPart P Q f).Realization, (associatedFamily P Q f).Realization)).comp
        (⟨h, h.continuous⟩ :
          C((cylinderFamily P Q f).Realization, (cylinderPart P Q f).Realization)))

open Classical in
private def conesToAssociated (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) :
    coneSum P W ⟶ TopCat.of (associatedFamily P Q f).Realization :=
  TopCat.ofHom ((⟨PreAbstractSimplicialComplex.Realization.inclusion le_sup_right,
    PreAbstractSimplicialComplex.Realization.continuous_inclusion le_sup_right⟩ :
      C((attachedFamily (W := W) P).Realization, (associatedFamily P Q f).Realization)).comp
        (ordinaryConeSigmaHomeomorph (W := W) P hfinite :
          C((Σ i, TopCat.cone (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization)),
            (attachedFamily (W := W) P).Realization)))

/-- The genuine old copied domains, ordinary cones and actual cylinder-family space form a pushout.
-/
private theorem ordinaryConeFamily_isPushout (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) :
    IsPushout (domainsToCylinder P Q f) (domainsToCones P)
      (cylinderToAssociated P Q f) (conesToAssociated P Q f hfinite) := by
  let e₁ : domainSum P W ≅ TopCat.of (copiedFamily (W := W) P).Realization :=
    TopCat.isoOfHomeo (copiedSigmaHomeomorph P)
  let e₂ : TopCat.of (cylinderFamily P Q f).Realization ≅ TopCat.of (cylinderPart P Q f).Realization
    :=
    TopCat.isoOfHomeo (MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
      Function.Embedding.inl)
  let e₃ : coneSum P W ≅ TopCat.of (attachedFamily (W := W) P).Realization :=
    TopCat.isoOfHomeo (ordinaryConeSigmaHomeomorph P hfinite)
  refine (associatedFamily_isPushout P Q f).of_iso' e₁ e₂ e₃ (Iso.refl _) ?_ ?_ ?_ ?_
  · apply ConcreteCategory.hom_ext
    rintro ⟨i, x⟩
    apply PreAbstractSimplicialComplex.Realization.ext
    change ((MappingCylinder.inclusionMorphism (copiedFamily_le_cylinder P Q f)).realization
      (copiedSigmaHomeomorph (W := W) P ⟨i, x⟩)).point =
      (MappingCylinder.relabelHomeomorph (cylinderFamily P Q f) Function.Embedding.inl
        (blockInclusion P Q f i
          ((MappingCylinder.inclusionMorphism (MappingCylinder.domainComplex_le (f i))).realization
            x))).point
    rw [actualFamilyInclusionPoint, copiedSigmaHomeomorph_point]
    change x.point.map ((tag P i).trans Function.Embedding.inl) =
      ((MappingCylinder.relabelMorphism (cylinderFamily P Q f) Function.Embedding.inl).realization
        (blockInclusion P Q f i
          ((MappingCylinder.inclusionMorphism (MappingCylinder.domainComplex_le (f i))).realization
            x))).point
    rw [MappingCylinder.relabelMorphism_point, blockInclusion_point,
      actualFamilyInclusionPoint, Convexity.StdSimplex.map_map]
    rfl
  · apply ConcreteCategory.hom_ext
    rintro ⟨i, x⟩
    apply PreAbstractSimplicialComplex.Realization.ext
    change ((MappingCylinder.inclusionMorphism (copiedFamily_le_attached (W := W) P)).realization
      (copiedSigmaHomeomorph (W := W) P ⟨i, x⟩)).point =
        (ordinaryConeSigmaHomeomorph (W := W) P hfinite
          ⟨i, TopCat.coneBase (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization)
            x⟩).point
    rw [actualFamilyInclusionPoint]
    have h := congrArg (fun z : (attachedFamily (W := W) P).Realization => z.point)
      (coneSigmaHomeomorph_base (W := W) P hfinite i x).symm
    simpa only [PreAbstractSimplicialComplex.Realization.inclusion_point] using h
  · apply ConcreteCategory.hom_ext
    intro x
    apply PreAbstractSimplicialComplex.Realization.ext
    change ((MappingCylinder.inclusionMorphism
      (le_sup_left : cylinderPart P Q f ≤ associatedFamily P Q f)).realization
        (MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
          (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) x)).point =
      (PreAbstractSimplicialComplex.Realization.inclusion
        (le_sup_left : cylinderPart P Q f ≤ associatedFamily P Q f)
          (MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
            (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) x)).point
    let z : (cylinderPart P Q f).Realization :=
      MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
        (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) x
    have hz := actualFamilyInclusionPoint
      (le_sup_left : cylinderPart P Q f ≤ associatedFamily P Q f) z
    exact hz.trans
      (PreAbstractSimplicialComplex.Realization.inclusion_point
        (le_sup_left : cylinderPart P Q f ≤ associatedFamily P Q f) z).symm
  · apply ConcreteCategory.hom_ext
    intro x
    apply PreAbstractSimplicialComplex.Realization.ext
    change ((MappingCylinder.inclusionMorphism
      (le_sup_right : attachedFamily (W := W) P ≤ associatedFamily P Q f)).realization
        (ordinaryConeSigmaHomeomorph (W := W) P hfinite x)).point =
      (PreAbstractSimplicialComplex.Realization.inclusion
        (le_sup_right : attachedFamily (W := W) P ≤ associatedFamily P Q f)
          (ordinaryConeSigmaHomeomorph (W := W) P hfinite x)).point
    rw [actualFamilyInclusionPoint, PreAbstractSimplicialComplex.Realization.inclusion_point]

end OrdinaryConeFamilyPushoutConstruction46

namespace ScalarAssociatedConeLawsConstruction46

open PreAbstractSimplicialComplex TaggedFamilyComplexConstruction46 FamilyConeComplexConstruction46
open FamilyConeComparisonsConstruction46 OrdinaryConeFamilyPushoutConstruction46

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

private theorem scalarAssociated_le (f : ∀ i, Morphism (P i) Q) (i : «I») :
    MappingCylinder.relabelComplex (MappingCylinder.associatedCone (f i)) (coneTag (W := W) P i) ≤
      associatedFamily P Q f := by
  classical
  let : DecidableEq (Labels (W := W) P) := Classical.decEq _
  let : DecidableEq (ConeLabels (W := W) P) := Classical.decEq _
  let : DecidableEq ((Face (P i) ⊕ W) ⊕ PUnit.{max v w + 1}) := Classical.decEq _
  intro s hs
  obtain ⟨a, ha, rfl⟩ := hs
  rcases ha with hc | ht
  · obtain ⟨b, hb, rfl⟩ := hc
    have hleft : cylinderPart P Q f ≤ associatedFamily P Q f := le_sup_left
    apply hleft
    change ∃ c : Finset (Labels (W := W) P), c ∈ cylinderFamily P Q f ∧
      c.image (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) =
        (b.image (Function.Embedding.inl : Face (P i) ⊕ W ↪
          (Face (P i) ⊕ W) ⊕ PUnit.{max v w + 1})).image (coneTag (W := W) P i)
    refine ⟨b.image (tag P i), ?_, ?_⟩
    · apply block_le_family P Q f i
      change ∃ c : Finset (Face (P i) ⊕ W), c ∈ MappingCylinder.complex (f i) ∧
        c.image (tag P i) = b.image (tag P i)
      exact ⟨b, hb, rfl⟩
    · rw [Finset.image_image, Finset.image_image]
      rfl
  · have hright : attachedFamily (W := W) P ≤ associatedFamily P Q f := le_sup_right
    apply hright
    apply le_iSup (attachedBlock (W := W) P) i
    change ∃ c : Finset ((Face (P i) ⊕ W) ⊕ PUnit.{max v w + 1}),
      c ∈ MappingCylinder.coneComplex (MappingCylinder.domainComplex (P i) W) ∧
        c.image (coneTag (W := W) P i) = a.image (coneTag (W := W) P i)
    exact ⟨a, ht, rfl⟩

open Classical in
private def scalarAssociatedInclusion (f : ∀ i, Morphism (P i) Q) (i : «I») :
    C((MappingCylinder.associatedCone (f i)).Realization, (associatedFamily P Q f).Realization) :=
  (⟨PreAbstractSimplicialComplex.Realization.inclusion (scalarAssociated_le P Q f i),
    PreAbstractSimplicialComplex.Realization.continuous_inclusion (scalarAssociated_le P Q f i)⟩ :
      C((MappingCylinder.relabelComplex (MappingCylinder.associatedCone (f i)) (coneTag (W := W) P
        i)).Realization,
        (associatedFamily P Q f).Realization)).comp
      (MappingCylinder.relabelHomeomorph (MappingCylinder.associatedCone (f i))
        (coneTag (W := W) P i) :
          C((MappingCylinder.associatedCone (f i)).Realization,
            (MappingCylinder.relabelComplex (MappingCylinder.associatedCone (f i))
              (coneTag (W := W) P i)).Realization))

private theorem scalarAssociated_cylinder (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (x : (MappingCylinder.complex (f i)).Realization) :
    scalarAssociatedInclusion P Q f i ((MappingCylinder.cylinderToCone (f i)).realization x) =
      cylinderToAssociated P Q f (blockInclusion P Q f i x) := by
  apply PreAbstractSimplicialComplex.Realization.ext
  change ((MappingCylinder.relabelMorphism (MappingCylinder.associatedCone (f i)) (coneTag (W := W)
    P i)).realization
      ((MappingCylinder.cylinderToCone (f i)).realization x)).point =
    ((MappingCylinder.relabelMorphism (cylinderFamily P Q f) Function.Embedding.inl).realization
      (blockInclusion P Q f i x)).point
  rw [MappingCylinder.relabelMorphism_point, MappingCylinder.cylinderToCone_point,
    MappingCylinder.relabelMorphism_point, blockInclusion_point,
    Convexity.StdSimplex.map_map, Convexity.StdSimplex.map_map]
  rfl

private theorem scalarAssociated_ordinaryCone (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) (i : «I»)
    (x : TopCat.cone (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization)) :
    letI : Finite (Face (P i)) := hfinite i
    conesToAssociated P Q f hfinite ⟨i, x⟩ =
      scalarAssociatedInclusion P Q f i (MappingCylinder.ordinaryConeAttachment (f i) x) := by
  let := hfinite i
  let := MappingCylinder.finiteFaces_domainComplex (P i) W
  apply PreAbstractSimplicialComplex.Realization.ext
  change ((MappingCylinder.relabelMorphism
    (MappingCylinder.coneComplex (MappingCylinder.domainComplex (P i) W)) (coneTag (W := W) P
      i)).realization
      (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex (P i) W) x)).point =
    ((MappingCylinder.relabelMorphism (MappingCylinder.associatedCone (f i)) (coneTag (W := W) P
      i)).realization
      (MappingCylinder.ordinaryConeAttachment (f i) x)).point
  rw [MappingCylinder.relabelMorphism_point, MappingCylinder.relabelMorphism_point]
  change (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex (P i) W)
    x).point.map
      (coneTag (W := W) P i) =
    ((MappingCylinder.attachedConeMorphism (f i)).realization
      (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex (P i) W) x)).point.map
        (coneTag (W := W) P i)
  rw [MappingCylinder.attachedConeMorphism_point]

private theorem ordinaryCone_apex_point (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) (i : «I») :
    (conesToAssociated P Q f hfinite
      ⟨i, TopCat.conePoint (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization)
        PUnit.unit⟩).point =
        Convexity.StdSimplex.single (Sum.inr i : ConeLabels (W := W) P) := by
  let := hfinite i
  let := MappingCylinder.finiteFaces_domainComplex (P i) W
  change ((MappingCylinder.relabelMorphism
    (MappingCylinder.coneComplex (MappingCylinder.domainComplex (P i) W)) (coneTag (W := W) P
      i)).realization
      (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex (P i) W)
        (TopCat.conePoint (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization)
          PUnit.unit))).point = _
  rw [MappingCylinder.relabelMorphism_point, MappingCylinder.ordinaryConeHomeomorph_apex]
  change (Convexity.StdSimplex.single (Sum.inr PUnit.unit :
      (Face (P i) ⊕ W) ⊕ PUnit.{max v w + 1})).map (coneTag (W := W) P i) = _
  rw [Convexity.StdSimplex.map_single]
  rfl

private theorem scalarAssociated_point (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (x : (MappingCylinder.associatedCone (f i)).Realization) :
    (scalarAssociatedInclusion P Q f i x).point = x.point.map (coneTag (W := W) P i) :=
  MappingCylinder.relabelMorphism_point (MappingCylinder.associatedCone (f i)) (coneTag (W := W) P
    i) x

end ScalarAssociatedConeLawsConstruction46

namespace FamilyConeRangeGeometryConstruction46

open PreAbstractSimplicialComplex TaggedFamilyComplexConstruction46 FamilyConeComplexConstruction46
open FamilyConeComparisonsConstruction46 OrdinaryConeFamilyPushoutConstruction46

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

private theorem cylinderCone_point (f : ∀ i, Morphism (P i) Q) (x : (cylinderFamily P Q
  f).Realization) :
    (cylinderToAssociated P Q f x).point = x.point.map Function.Embedding.inl := by
  change ((MappingCylinder.relabelMorphism (cylinderFamily P Q f)
    (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)).realization x).point =
      x.point.map Function.Embedding.inl
  exact MappingCylinder.relabelMorphism_point (cylinderFamily P Q f)
    (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) x

private theorem domainsAssociated_point (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (x : (MappingCylinder.domainComplex (P i) W).Realization) :
    (cylinderToAssociated P Q f (domainsToCylinder P Q f ⟨i, x⟩)).point =
      x.point.map ((tag P i).trans Function.Embedding.inl) := by
  change (cylinderToAssociated P Q f
    (blockInclusion P Q f i
      ((MappingCylinder.inclusionMorphism (MappingCylinder.domainComplex_le (f i))).realization
        x))).point =
        x.point.map ((tag P i).trans Function.Embedding.inl)
  rw [cylinderCone_point, blockInclusion_point, actualFamilyInclusionPoint,
    Convexity.StdSimplex.map_map]
  rfl

private theorem cylinderCone_range_iff (f : ∀ i, Morphism (P i) Q)
    (y : (associatedFamily P Q f).Realization) :
    y ∈ Set.range (cylinderToAssociated P Q f) ↔ y.point.weights.support ∈ cylinderPart P Q f := by
  constructor
  · rintro ⟨x, rfl⟩
    change (MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
      (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) x).point.weights.support
        ∈
        cylinderPart P Q f
    exact (MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
      (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) x).support_mem
  · intro hy
    let z : (cylinderPart P Q f).Realization := ⟨y.point, hy⟩
    let h : (cylinderFamily P Q f).Realization ≃ₜ (cylinderPart P Q f).Realization :=
      MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
        (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)
    refine ⟨h.symm z, ?_⟩
    apply PreAbstractSimplicialComplex.Realization.ext
    change (h (h.symm z)).point = y.point
    rw [h.apply_symm_apply]

private theorem ordinaryCone_range_iff (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) (i : «I») (y : (associatedFamily P Q f).Realization) :
    y ∈ Set.range (fun x => conesToAssociated P Q f hfinite ⟨i, x⟩) ↔
      y.point.weights.support ∈ attachedBlock (W := W) P i := by
  constructor
  · rintro ⟨x, rfl⟩
    change (scalarConeHomeomorph (W := W) P i (hfinite i) x).point.weights.support ∈
      attachedBlock (W := W) P i
    exact (scalarConeHomeomorph (W := W) P i (hfinite i) x).support_mem
  · intro hy
    let z : (attachedBlock (W := W) P i).Realization := ⟨y.point, hy⟩
    let h : TopCat.cone (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization) ≃ₜ
        (attachedBlock (W := W) P i).Realization :=
      scalarConeHomeomorph (W := W) P i (hfinite i)
    refine ⟨h.symm z, ?_⟩
    apply PreAbstractSimplicialComplex.Realization.ext
    change (h (h.symm z)).point = y.point
    rw [h.apply_symm_apply]

private theorem copiedAssociated_range_iff (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (y : (associatedFamily P Q f).Realization) :
    y ∈ Set.range (fun x : (MappingCylinder.domainComplex (P i) W).Realization =>
        cylinderToAssociated P Q f (domainsToCylinder P Q f ⟨i, x⟩)) ↔
      y.point.weights.support ∈ copiedBlock (W := W) P i := by
  constructor
  · rintro ⟨x, rfl⟩
    let h : (MappingCylinder.domainComplex (P i) W).Realization ≃ₜ
        (copiedBlock (W := W) P i).Realization :=
      MappingCylinder.relabelHomeomorph (MappingCylinder.domainComplex (P i) W)
        ((tag P i).trans (Function.Embedding.inl :
          Labels (W := W) P ↪ ConeLabels (W := W) P))
    have hs := (h x).support_mem
    have hp : (h x).point = x.point.map ((tag P i).trans
        (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)) :=
      MappingCylinder.relabelMorphism_point (MappingCylinder.domainComplex (P i) W)
        ((tag P i).trans (Function.Embedding.inl :
          Labels (W := W) P ↪ ConeLabels (W := W) P)) x
    rw [hp] at hs
    have hpoint := domainsAssociated_point P Q f i x
    have hsupport := congrArg
      (fun q : Convexity.StdSimplex ℝ (ConeLabels (W := W) P) =>
        q.weights.support ∈ copiedBlock (W := W) P i) hpoint
    exact Eq.mpr hsupport hs
  · intro hy
    let z : (copiedBlock (W := W) P i).Realization := ⟨y.point, hy⟩
    let h : (MappingCylinder.domainComplex (P i) W).Realization ≃ₜ
        (copiedBlock (W := W) P i).Realization :=
      MappingCylinder.relabelHomeomorph (MappingCylinder.domainComplex (P i) W)
        ((tag P i).trans (Function.Embedding.inl :
          Labels (W := W) P ↪ ConeLabels (W := W) P))
    refine ⟨h.symm z, ?_⟩
    apply PreAbstractSimplicialComplex.Realization.ext
    rw [domainsAssociated_point]
    calc
      (h.symm z).point.map ((tag P i).trans Function.Embedding.inl) = (h (h.symm z)).point :=
        (MappingCylinder.relabelMorphism_point (MappingCylinder.domainComplex (P i) W)
          ((tag P i).trans Function.Embedding.inl) (h.symm z)).symm
      _ = z.point := congrArg PreAbstractSimplicialComplex.Realization.point (h.apply_symm_apply z)
      _ = y.point := rfl

private theorem ordinaryCone_cylinder_intersection (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) (i : «I») :
    Set.range (fun x => conesToAssociated P Q f hfinite ⟨i, x⟩) ∩
        Set.range (cylinderToAssociated P Q f) =
      Set.range (fun x : (MappingCylinder.domainComplex (P i) W).Realization =>
        cylinderToAssociated P Q f (domainsToCylinder P Q f ⟨i, x⟩)) := by
  ext y
  rw [Set.mem_inter_iff, ordinaryCone_range_iff P Q f hfinite i,
    cylinderCone_range_iff P Q f, copiedAssociated_range_iff P Q f i]
  rw [← cylinder_attached_intersection P Q f i]
  change (y.point.weights.support ∈ attachedBlock (W := W) P i ∧
    y.point.weights.support ∈ cylinderPart P Q f) ↔
      (y.point.weights.support ∈ cylinderPart P Q f ∧ y.point.weights.support ∈ attachedBlock (W :=
        W) P i)
  exact and_comm

private theorem ordinaryCones_disjoint (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) {i j : «I»} (hij : i ≠ j) :
    Disjoint (Set.range (fun x => conesToAssociated P Q f hfinite ⟨i, x⟩))
      (Set.range (fun x => conesToAssociated P Q f hfinite ⟨j, x⟩)) := by
  rw [Set.disjoint_left]
  intro y hyi hyj
  have hs : y.point.weights.support ∈ attachedBlock (W := W) P i ⊓ attachedBlock (W := W) P j :=
    ⟨(ordinaryCone_range_iff P Q f hfinite i y).mp hyi,
      (ordinaryCone_range_iff P Q f hfinite j y).mp hyj⟩
  rw [attached_disjoint_faces (W := W) P hij] at hs
  exact hs

private theorem associatedFamily_cover (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) :
    Set.range (cylinderToAssociated P Q f) ∪
        ⋃ i, Set.range (fun x => conesToAssociated P Q f hfinite ⟨i, x⟩) = Set.univ := by
  ext y
  constructor
  · intro _
    exact Set.mem_univ y
  · intro _
    rcases y.support_mem with hc | ha
    · exact Or.inl ((cylinderCone_range_iff P Q f y).mpr hc)
    · obtain ⟨i, hi⟩ := (WeakFamilyUnionConstruction46.mem_weakUnion (attachedBlock (W := W) P)
        y.point.weights.support).mp ha
      exact Or.inr (Set.mem_iUnion.mpr ⟨i, (ordinaryCone_range_iff P Q f hfinite i y).mpr hi⟩)

end FamilyConeRangeGeometryConstruction46

public section

namespace PreAbstractSimplicialComplex.MappingCylinder

open Classical in
/-- Attachment data for a family of maps `f i : P i → Q`: the family mapping cylinder and
mapping cone, their inclusions, the deformation retraction of the cylinder onto `Q`, and
the two attachment pushout squares. -/
structure FamilyAttachmentData {«I» : Type u} {V : «I» → Type v}
    (P : ∀ i, PreAbstractSimplicialComplex (V i)) {W : Type w}
    (Q : PreAbstractSimplicialComplex W) (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) where
  /-- Embeds the labels of the `i`-th cylinder into the family cylinder labels: a copied face
  `a` goes to `⟨i, a⟩` and an ambient target label is unchanged. -/
  tag : ∀ i, Face (P i) ⊕ W ↪ (Σ j, Face (P j)) ⊕ W
  /-- Labels the apex of the `i`-th cone by `i`. -/
  apexTag : ∀ _ : «I», PUnit.{max v w + 1} ↪ «I»
  tag_left : ∀ i, ∀ a : Face (P i), tag i (Sum.inl a) = Sum.inl ⟨i, a⟩
  tag_right : ∀ i, ∀ a : W, tag i (Sum.inr a) = Sum.inr a
  apex_tag : ∀ i, ∀ p : PUnit.{max v w + 1}, apexTag i p = i
  /-- The family mapping cylinder: `Q` together with every tagged cylinder `complex (f i)`. -/
  cylinder : PreAbstractSimplicialComplex ((Σ i, Face (P i)) ⊕ W)
  /-- The family mapping cone: the cylinder together with the cone on each tagged copied
  domain, with apex labelled `i`. -/
  cone : PreAbstractSimplicialComplex (((Σ i, Face (P i)) ⊕ W) ⊕ «I»)
  cylinder_faces : ∀ s, s ∈ cylinder ↔
    s ∈ Q.map (Function.Embedding.inr : W ↪ (Σ i, Face (P i)) ⊕ W) ∨
      ∃ i, s ∈ (complex (f i)).map (tag i)
  cone_faces : ∀ s, s ∈ cone ↔
    s ∈ cylinder.map Function.Embedding.inl ∨
      ∃ i, s ∈ (coneComplex (domainComplex (P i) W)).map
        (Function.Embedding.sumMap (tag i) (apexTag i))
  /-- The inclusion of `Q` into the family cylinder. -/
  old : C(Q.Realization, cylinder.Realization)
  /-- The inclusion of the `i`-th mapping cylinder `complex (f i)` into the family cylinder. -/
  block : ∀ i, C((complex (f i)).Realization, cylinder.Realization)
  /-- The inclusion of the `i`-th copied domain, the barycentric subdivision of `P i`. -/
  copied : ∀ i, C((barycentricSubdivision (P i)).Realization, cylinder.Realization)
  old_point : ∀ x, (old x).point = x.point.map (Sum.inr : W → (Σ i, Face (P i)) ⊕ W)
  block_point : ∀ i x, (block i x).point = x.point.map (tag i)
  copied_point : ∀ i x, (copied i x).point =
    (x.point.map (Sum.inl : Face (P i) → Face (P i) ⊕ W)).map (tag i)
  old_closed : IsClosedEmbedding old
  block_closed : ∀ i, IsClosedEmbedding (block i)
  copied_closed : ∀ i, IsClosedEmbedding (copied i)
  block_intersection : ∀ i j, i ≠ j → Set.range (block i) ∩ Set.range (block j) = Set.range old
  copied_old_disjoint : ∀ i, Disjoint (Set.range (copied i)) (Set.range old)
  copied_disjoint : ∀ i j, i ≠ j → Disjoint (Set.range (copied i)) (Set.range (copied j))
  /-- The retraction of the family cylinder onto `Q`; on each block it is that cylinder's
  retraction. -/
  retraction : C(cylinder.Realization, Q.Realization)
  retraction_old : ∀ x, retraction (old x) = x
  retraction_block : ∀ i x, retraction (block i x) = MappingCylinder.retraction (f i) x
  retraction_copied : ∀ i x, retraction (copied i x) = (f i).realization (barycentricHomeomorph (P
    i) x)
  /-- A homotopy from the identity to `old ∘ retraction`, fixing the image of `Q`. -/
  deformation : ContinuousMap.HomotopyRel (ContinuousMap.id cylinder.Realization)
    (old.comp retraction) (Set.range old)
  deformation_fixed : ∀ t : unitInterval, ∀ x, deformation (t, old x) = old x
  /-- On the `i`-th copy of `Q`, the inclusion of `Q` into the `i`-th mapping cylinder; a leg
  of `cylinder_pushout`. -/
  overlapMap : C((Σ _ : «I», ULift.{max u v w} Q.Realization),
    (Σ i, ULift.{max u v w} (complex (f i)).Realization))
  /-- The fold map from the `«I»`-indexed copies of `Q` to `Q`; a leg of `cylinder_pushout`. -/
  overlapFold : C((Σ _ : «I», ULift.{max u v w} Q.Realization), ULift.{max u v w} Q.Realization)
  /-- The map from the disjoint union of the mapping cylinders that is `block i` on the
  `i`-th summand. -/
  blocksMap : C((Σ i, ULift.{max u v w} (complex (f i)).Realization), cylinder.Realization)
  /-- The inclusion `old`, on the universe-lifted realization of `Q`. -/
  oldMap : C(ULift.{max u v w} Q.Realization, cylinder.Realization)
  overlapMap_apply : ∀ i q, overlapMap ⟨i, q⟩ = ⟨i, ULift.up ((targetMorphism (f i)).realization
    q.down)⟩
  overlapFold_apply : ∀ i q, overlapFold ⟨i, q⟩ = q
  blocksMap_apply : ∀ i x, blocksMap ⟨i, x⟩ = block i x.down
  oldMap_apply : ∀ x, oldMap x = old x.down
  cylinder_pushout : CategoryTheory.IsPushout (TopCat.ofHom overlapMap) (TopCat.ofHom overlapFold)
    (TopCat.ofHom blocksMap) (TopCat.ofHom oldMap)
  /-- The inclusion of the family cylinder into the family cone. -/
  cylinderCone : C(cylinder.Realization, cone.Realization)
  /-- The map from the disjoint union of the topological cones on the copied domains into the
  family cone, through each `associated i`. -/
  ordinaryCones : C((Σ i, TopCat.cone (TopCat.of (domainComplex (P i) W).Realization)),
    cone.Realization)
  /-- The inclusion of the `i`-th mapping cone `associatedCone (f i)` into the family cone. -/
  associated : ∀ i, C((associatedCone (f i)).Realization, cone.Realization)
  cylinderCone_point : ∀ x, (cylinderCone x).point = x.point.map Function.Embedding.inl
  associated_point : ∀ i x, (associated i x).point =
    x.point.map (Function.Embedding.sumMap (tag i) (apexTag i))
  associated_cylinder : ∀ i x, associated i ((cylinderToCone (f i)).realization x) = cylinderCone
    (block i x)
  ordinaryCones_apply : ∀ i,
    letI : Finite (Face (P i)) := hfinite i
    ∀ x, ordinaryCones ⟨i, x⟩ = associated i (ordinaryConeAttachment (f i) x)
  apex_point : ∀ i, (ordinaryCones
    ⟨i, TopCat.conePoint (TopCat.of (domainComplex (P i) W).Realization) PUnit.unit⟩).point =
      Convexity.StdSimplex.single (Sum.inr i : ((Σ i, Face (P i)) ⊕ W) ⊕ «I»)
  /-- The map from the disjoint union of the copied domains into the family cylinder,
  through each `block i`. -/
  domainsCylinder : C((Σ i, (domainComplex (P i) W).Realization), cylinder.Realization)
  /-- The inclusion of each copied domain as the base of its topological cone. -/
  domainsCones : C((Σ i, (domainComplex (P i) W).Realization),
    (Σ i, TopCat.cone (TopCat.of (domainComplex (P i) W).Realization)))
  domainsCylinder_apply : ∀ i x, domainsCylinder ⟨i, x⟩ =
    block i ((inclusionMorphism (domainComplex_le (f i))).realization x)
  domainsCones_apply : ∀ i x, domainsCones ⟨i, x⟩ =
    ⟨i, TopCat.coneBase (TopCat.of (domainComplex (P i) W).Realization) x⟩
  cone_pushout : CategoryTheory.IsPushout (TopCat.ofHom domainsCylinder) (TopCat.ofHom domainsCones)
    (TopCat.ofHom cylinderCone) (TopCat.ofHom ordinaryCones)
  cone_cylinder_intersection : ∀ i,
    Set.range (fun x => ordinaryCones ⟨i, x⟩) ∩ Set.range cylinderCone =
      Set.range (fun x : (domainComplex (P i) W).Realization => cylinderCone (domainsCylinder ⟨i,
        x⟩))
  cones_disjoint : ∀ i j, i ≠ j →
    Disjoint (Set.range (fun x => ordinaryCones ⟨i, x⟩)) (Set.range (fun x => ordinaryCones ⟨j, x⟩))
  cover : Set.range cylinderCone ∪ ⋃ i, Set.range (fun x => ordinaryCones ⟨i, x⟩) = Set.univ
  empty_family : IsEmpty «I» →
    cylinder = Q.map (Function.Embedding.inr : W ↪ (Σ i, Face (P i)) ⊕ W) ∧
      cone = (Q.map (Function.Embedding.inr : W ↪ (Σ i, Face (P i)) ⊕ W)).map Function.Embedding.inl


open Classical in
/-- Construct both actual tagged attachment spaces, their literal maps and
pushouts, and the jointly continuous cylinder deformation fixing all old Q. -/
def familyAttachments {«I» : Type u} {V : «I» → Type v}
    (P : ∀ i, PreAbstractSimplicialComplex (V i)) {W : Type w}
    (Q : PreAbstractSimplicialComplex W) (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) : FamilyAttachmentData P Q f hfinite := by
  refine
    { tag := TaggedFamilyComplexConstruction46.tag P
      apexTag := FamilyConeComplexConstruction46.apexTag.{u, max v w}
      tag_left := fun _ _ => rfl
      tag_right := fun _ _ => rfl
      apex_tag := fun _ _ => rfl
      cylinder := TaggedFamilyComplexConstruction46.cylinderFamily P Q f
      cone := FamilyConeComplexConstruction46.associatedFamily P Q f
      cylinder_faces := by
        intro s
        simpa only [TaggedFamilyComplexConstruction46.oldTarget,
          TaggedFamilyComplexConstruction46.block, actualFamilyRelabelComplex_eq_map] using
          TaggedFamilyComplexConstruction46.cylinderFamily_faces P Q f s
      cone_faces := ?_
      old := TaggedFamilyComplexConstruction46.oldInclusion P Q f
      block := TaggedFamilyComplexConstruction46.blockInclusion P Q f
      copied := TaggedFamilyComplexConstruction46.copiedInclusion P Q f
      old_point := TaggedFamilyComplexConstruction46.oldInclusion_point P Q f
      block_point := TaggedFamilyComplexConstruction46.blockInclusion_point P Q f
      copied_point := TaggedFamilyComplexConstruction46.copiedInclusion_point P Q f
      old_closed := TaggedFamilyComplexConstruction46.oldInclusion_isClosedEmbedding P Q f
      block_closed := TaggedFamilyComplexConstruction46.blockInclusion_isClosedEmbedding P Q f
      copied_closed := TaggedFamilyComplexConstruction46.copiedInclusion_isClosedEmbedding P Q f
      block_intersection := fun _ _ hij => TaggedFamilyComplexConstruction46.blockRange_intersection
        P Q f hij
      copied_old_disjoint := TaggedFamilyComplexConstruction46.copied_old_disjoint P Q f
      copied_disjoint := fun _ _ hij => TaggedFamilyComplexConstruction46.copied_copied_disjoint P Q
        f hij
      retraction := FamilyCylinderRetractionConstruction46.familyRetraction P Q f
      retraction_old := FamilyCylinderRetractionConstruction46.familyRetraction_old P Q f
      retraction_block := FamilyCylinderRetractionConstruction46.familyRetraction_block P Q f
      retraction_copied := FamilyCylinderRetractionConstruction46.familyRetraction_copied P Q f
      deformation := FamilyCylinderRetractionConstruction46.familyHomotopyRelativeOld P Q f
      deformation_fixed := FamilyCylinderRetractionConstruction46.familyHomotopy_old P Q f
      overlapMap := (OriginalCylinderSpanConstruction46.actualBoundary P Q f).hom
      overlapFold := (OriginalCylinderSpanConstruction46.actualFold.{u, v, w} Q).hom
      blocksMap := (OriginalCylinderSpanConstruction46.actualBlocks P Q f).hom
      oldMap := (OriginalCylinderSpanConstruction46.actualOld P Q f).hom
      overlapMap_apply := fun _ _ => rfl
      overlapFold_apply := fun _ _ => rfl
      blocksMap_apply := fun _ _ => rfl
      oldMap_apply := fun _ => rfl
      cylinder_pushout := OriginalCylinderSpanConstruction46.actualCylinderFamily_isPushout P Q f
      cylinderCone := (OrdinaryConeFamilyPushoutConstruction46.cylinderToAssociated P Q f).hom
      ordinaryCones := (OrdinaryConeFamilyPushoutConstruction46.conesToAssociated P Q f hfinite).hom
      associated := ScalarAssociatedConeLawsConstruction46.scalarAssociatedInclusion P Q f
      cylinderCone_point := FamilyConeRangeGeometryConstruction46.cylinderCone_point P Q f
      associated_point := ScalarAssociatedConeLawsConstruction46.scalarAssociated_point P Q f
      associated_cylinder := ScalarAssociatedConeLawsConstruction46.scalarAssociated_cylinder P Q f
      ordinaryCones_apply := ScalarAssociatedConeLawsConstruction46.scalarAssociated_ordinaryCone P
        Q f hfinite
      apex_point := ScalarAssociatedConeLawsConstruction46.ordinaryCone_apex_point P Q f hfinite
      domainsCylinder := (OrdinaryConeFamilyPushoutConstruction46.domainsToCylinder P Q f).hom
      domainsCones := (OrdinaryConeFamilyPushoutConstruction46.domainsToCones P).hom
      domainsCylinder_apply := fun _ _ => rfl
      domainsCones_apply := fun _ _ => rfl
      cone_pushout := OrdinaryConeFamilyPushoutConstruction46.ordinaryConeFamily_isPushout P Q f
        hfinite
      cone_cylinder_intersection :=
        FamilyConeRangeGeometryConstruction46.ordinaryCone_cylinder_intersection P Q f hfinite
      cones_disjoint := fun _ _ hij => FamilyConeRangeGeometryConstruction46.ordinaryCones_disjoint
        P Q f hfinite hij
      cover := FamilyConeRangeGeometryConstruction46.associatedFamily_cover P Q f hfinite
      empty_family := ?_ }
  · intro s
    change (s ∈ FamilyConeComplexConstruction46.cylinderPart P Q f ∨
      s ∈ FamilyConeComplexConstruction46.attachedFamily (W := W) P) ↔ _
    have hmem : s ∈ FamilyConeComplexConstruction46.attachedFamily (W := W) P ↔
        ∃ i, s ∈ FamilyConeComplexConstruction46.attachedBlock (W := W) P i :=
      WeakFamilyUnionConstruction46.mem_weakUnion
        (FamilyConeComplexConstruction46.attachedBlock (W := W) P) s
    rw [hmem]
    simp only [FamilyConeComplexConstruction46.cylinderPart,
      FamilyConeComplexConstruction46.attachedBlock, FamilyConeComplexConstruction46.coneTag,
      actualFamilyRelabelComplex_eq_map]
  · intro hI
    let := hI
    constructor
    · simpa only [TaggedFamilyComplexConstruction46.oldTarget,
        actualFamilyRelabelComplex_eq_map] using
        TaggedFamilyComplexConstruction46.cylinderFamily_empty_index P Q f
    · simpa only [FamilyConeComplexConstruction46.cylinderPart,
        TaggedFamilyComplexConstruction46.cylinderFamily_empty_index,
        TaggedFamilyComplexConstruction46.oldTarget, actualFamilyRelabelComplex_eq_map] using
        FamilyConeComparisonsConstruction46.associatedFamily_empty_index P Q f

end PreAbstractSimplicialComplex.MappingCylinder

public section

noncomputable section
set_option autoImplicit false
open Topology CategoryTheory CategoryTheory.Limits PreAbstractSimplicialComplex
open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder
open scoped Classical
namespace PreAbstractSimplicialComplex.MappingCylinder.SmallFamily



namespace Tagged

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

/-- Labels of the family cylinder: a copied face of some `P i`, tagged by `i`, or an ambient
target label in `W`. -/
abbrev Labels := (Σ i, Face (P i)) ⊕ W

/-- Embeds the labels of the `i`-th small cylinder into the family labels: a copied face `a`
goes to `⟨i, a⟩` and an ambient target label is unchanged. -/
def tag (i : «I») : Face (P i) ⊕ W ↪ Labels (W := W) P :=
  Function.Embedding.sumMap (Function.Embedding.sigmaMk (β := fun j => Face (P j)) i) (Function.Embedding.refl W)

/-- The target `Q`, relabelled into the family labels by `Sum.inr`. -/
@[expose] def oldTarget : PreAbstractSimplicialComplex (Labels (W := W) P) :=
  MappingCylinder.relabelComplex Q Function.Embedding.inr

/-- The `i`-th small mapping cylinder `smallCylinder (f i)`, relabelled into the family labels
by `tag`. -/
@[expose] def block (f : ∀ i, Morphism (P i) Q) (i : «I») :
    PreAbstractSimplicialComplex (Labels (W := W) P) :=
  MappingCylinder.relabelComplex (smallCylinder (f i)) (tag (W := W) P i)

private def optionBlocks (f : ∀ i, Morphism (P i) Q) :
    Option «I» → PreAbstractSimplicialComplex (Labels (W := W) P)
  | none => oldTarget P Q
  | some i => block P Q f i

/-- The actual old target is present even when the family has no index. -/
def cylinderFamily (f : ∀ i, Morphism (P i) Q) :
    PreAbstractSimplicialComplex (Labels (W := W) P) := ⨆ o, optionBlocks P Q f o

private theorem oldTarget_le_block (f : ∀ i, Morphism (P i) Q) (i : «I») :
    oldTarget P Q ≤ block P Q f i := by
  intro s hs
  obtain ⟨a, ha, rfl⟩ := hs
  refine ⟨a.image (Function.Embedding.inr : W ↪ Face (P i) ⊕ W), ?_, ?_⟩
  · apply small_target_le (f i)
    refine ⟨a, ha, ?_⟩
    simp only [← Finset.map_eq_image]
  · simp only [← Finset.map_eq_image, Finset.map_map]
    rfl

theorem oldTarget_le_family (f : ∀ i, Morphism (P i) Q) :
    oldTarget P Q ≤ cylinderFamily P Q f :=
  le_iSup (optionBlocks P Q f) none

theorem block_le_family (f : ∀ i, Morphism (P i) Q) (i : «I») :
    block P Q f i ≤ cylinderFamily P Q f :=
  le_iSup (optionBlocks P Q f) (some i)

private theorem cylinderFamily_empty_index (f : ∀ i, Morphism (P i) Q) [IsEmpty «I»] :
    cylinderFamily P Q f = oldTarget P Q := by
  apply le_antisymm
  · apply iSup_le
    intro o
    cases o with
    | none => exact le_rfl
    | some i => exact isEmptyElim i
  · exact oldTarget_le_family P Q f

private theorem copy_index_of_mem_image (i : «I») (s : Finset (Face (P i) ⊕ W))
    {k : «I»} (a : Face (P k))
    (h : Sum.inl (⟨k, a⟩ : Σ j, Face (P j)) ∈ s.image (tag (W := W) P i)) : k = i := by
  obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp h
  cases x with
  | inl b =>
    change (Sum.inl ⟨i, b⟩ : Labels (W := W) P) = Sum.inl ⟨k, a⟩ at heq
    have he : (⟨i, b⟩ : Σ j, Face (P j)) = ⟨k, a⟩ := Sum.inl.inj heq
    exact (congrArg Sigma.fst he).symm
  | inr b =>
    change (Sum.inr b : Labels (W := W) P) = Sum.inl ⟨k, a⟩ at heq
    cases heq

/-- Distinct tags force any common cylinder face to have no copied-domain coordinate. -/
private theorem oldTarget_intersection (f : ∀ i, Morphism (P i) Q) {i j : «I»} (hij : i ≠ j) :
    block P Q f i ⊓ block P Q f j = oldTarget P Q := by
  apply le_antisymm
  · intro s hs
    obtain ⟨a, ha, rfl⟩ := hs.1
    obtain ⟨b, hb, heq⟩ := hs.2
    simp only [← Finset.map_eq_image] at heq
    have hleft : a.toLeft = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hmem : Sum.inl (⟨i, x⟩ : Σ k, Face (P k)) ∈ a.image (tag (W := W) P i) :=
        Finset.mem_image.mpr ⟨Sum.inl x, Finset.mem_toLeft.mp hx, rfl⟩
      have hmem' : Sum.inl (⟨i, x⟩ : Σ k, Face (P k)) ∈ b.image (tag (W := W) P j) := by
        simp only [← Finset.map_eq_image] at hmem ⊢
        rw [heq]
        exact hmem
      exact hij (copy_index_of_mem_image P j b x hmem')
    have hQ : a.toRight ∈ Q := by
      have h := smallCylinder_le (f i) ha
      simpa only [MappingCylinder.hull, hleft, Finset.biUnion_empty, Finset.union_empty] using h.2.2
    refine ⟨a.toRight, hQ, ?_⟩
    have hsplit := (Finset.toLeft_disjSum_toRight (u := a))
    rw [hleft, Finset.empty_disjSum, Finset.map_eq_image] at hsplit
    have hmap : a.image (tag (W := W) P i) =
        a.toRight.image (Function.Embedding.inr : W ↪ Labels (W := W) P) := by
      calc
        a.image (tag (W := W) P i) =
            (a.toRight.image (Function.Embedding.inr : W ↪ Face (P i) ⊕ W)).image
              (tag (W := W) P i) := congrArg (fun t => t.image (tag (W := W) P i)) hsplit.symm
        _ = a.toRight.image (Function.Embedding.inr : W ↪ Labels (W := W) P) := by
          rw [Finset.image_image]
          rfl
    simpa only [← Finset.map_eq_image] using hmap.symm
  · exact le_inf (oldTarget_le_block P Q f i) (oldTarget_le_block P Q f j)

/-- The old target and each tagged block meet in the entire unchanged old target. -/
private theorem oldTarget_block_intersection (f : ∀ i, Morphism (P i) Q) (i : «I») :
    oldTarget P Q ⊓ block P Q f i = oldTarget P Q :=
  inf_eq_left.mpr (oldTarget_le_block P Q f i)

private def oldTargetHomeomorph : Q.Realization ≃ₜ (oldTarget P Q).Realization :=
  MappingCylinder.relabelHomeomorph Q Function.Embedding.inr

private def blockHomeomorph (f : ∀ i, Morphism (P i) Q) (i : «I») :
    (smallCylinder (f i)).Realization ≃ₜ (block P Q f i).Realization :=
  MappingCylinder.relabelHomeomorph (smallCylinder (f i)) (tag (W := W) P i)

/-- The inclusion of `Q` into the family cylinder, through `oldTarget`. -/
def oldInclusion (f : ∀ i, Morphism (P i) Q) :
    C(Q.Realization, (cylinderFamily P Q f).Realization) :=
  (⟨PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_family P Q f),
    PreAbstractSimplicialComplex.Realization.continuous_inclusion (oldTarget_le_family P Q f)⟩ :
      C((oldTarget P Q).Realization, (cylinderFamily P Q f).Realization)).comp
        (oldTargetHomeomorph P Q : C(Q.Realization, (oldTarget P Q).Realization))

/-- The inclusion of the `i`-th small mapping cylinder into the family cylinder, through
`block`. -/
def blockInclusion (f : ∀ i, Morphism (P i) Q) (i : «I») :
    C((smallCylinder (f i)).Realization, (cylinderFamily P Q f).Realization) :=
  (⟨PreAbstractSimplicialComplex.Realization.inclusion (block_le_family P Q f i),
    PreAbstractSimplicialComplex.Realization.continuous_inclusion (block_le_family P Q f i)⟩ :
      C((block P Q f i).Realization, (cylinderFamily P Q f).Realization)).comp
        (blockHomeomorph P Q f i : C((smallCylinder (f i)).Realization,
          (block P Q f i).Realization))

theorem oldInclusion_point (f : ∀ i, Morphism (P i) Q) (x : Q.Realization) :
    (oldInclusion P Q f x).point = x.point.map (Sum.inr : W → Labels (W := W) P) :=
  MappingCylinder.relabelMorphism_point Q Function.Embedding.inr x

theorem blockInclusion_point (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (x : (smallCylinder (f i)).Realization) :
    (blockInclusion P Q f i x).point = x.point.map (tag (W := W) P i) :=
  MappingCylinder.relabelMorphism_point (smallCylinder (f i)) (tag (W := W) P i) x

theorem oldInclusion_isClosedEmbedding (f : ∀ i, Morphism (P i) Q) :
    IsClosedEmbedding (oldInclusion P Q f) :=
  (PreAbstractSimplicialComplex.Realization.isClosedEmbedding_inclusion
    (oldTarget_le_family P Q f)).comp (oldTargetHomeomorph P Q).isClosedEmbedding

private theorem blockInclusion_isClosedEmbedding (f : ∀ i, Morphism (P i) Q) (i : «I») :
    IsClosedEmbedding (blockInclusion P Q f i) :=
  (PreAbstractSimplicialComplex.Realization.isClosedEmbedding_inclusion
    (block_le_family P Q f i)).comp (blockHomeomorph P Q f i).isClosedEmbedding

/-- The SAME old target point is present literally inside every tagged cylinder. -/
private theorem oldInBlock (f : ∀ i, Morphism (P i) Q) (i : «I») (q : Q.Realization) :
    blockHomeomorph P Q f i (smallOldTarget (f i) q) =
      PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i)
        (oldTargetHomeomorph P Q q) := by
  apply PreAbstractSimplicialComplex.Realization.ext
  change ((MappingCylinder.relabelMorphism (smallCylinder (f i))
    (tag (W := W) P i)).realization (smallOldTarget (f i) q)).point =
    ((MappingCylinder.relabelMorphism Q Function.Embedding.inr).realization q).point
  rw [MappingCylinder.relabelMorphism_point, smallOldTarget_point,
    MappingCylinder.relabelMorphism_point, Convexity.StdSimplex.map_map]
  rfl

private def blockRetraction (f : ∀ i, Morphism (P i) Q) (i : «I») :
    C((block P Q f i).Realization, Q.Realization) :=
  (smallRetraction (f i)).comp
    ((blockHomeomorph P Q f i).symm :
      C((block P Q f i).Realization, (smallCylinder (f i)).Realization))

private theorem blockRetraction_old (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (x : (oldTarget P Q).Realization) :
    blockRetraction P Q f i
        (PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i) x) =
      (oldTargetHomeomorph P Q).symm x := by
  let q := (oldTargetHomeomorph P Q).symm x
  have h := oldInBlock P Q f i q
  have hx : PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i) x =
      blockHomeomorph P Q f i (smallOldTarget (f i) q) :=
    (h.trans (congrArg
      (PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i))
      ((oldTargetHomeomorph P Q).apply_symm_apply x))).symm
  change smallRetraction (f i)
    ((blockHomeomorph P Q f i).symm
      (PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i) x)) = q
  rw [hx, (blockHomeomorph P Q f i).symm_apply_apply]
  exact smallRetraction_old (f i) q

private def pieceRetractions (f : ∀ i, Morphism (P i) Q) :
    ∀ o, C((optionBlocks P Q f o).Realization, Q.Realization)
  | none => ((oldTargetHomeomorph P Q).symm :
      C((oldTarget P Q).Realization, Q.Realization))
  | some i => blockRetraction P Q f i

/-- Compatibility is DERIVED from the actual shared target and scalar retractions. -/
private theorem pieceRetractions_agree (f : ∀ i, Morphism (P i) Q) :
    ∀ o p, ∀ x : (optionBlocks P Q f o ⊓ optionBlocks P Q f p).Realization,
      pieceRetractions P Q f o (PreAbstractSimplicialComplex.Realization.inclusion inf_le_left x) =
        pieceRetractions P Q f p
          (PreAbstractSimplicialComplex.Realization.inclusion inf_le_right x) := by
  intro o p x
  cases o with
  | none =>
    cases p with
    | none => rfl
    | some j =>
      let y : (oldTarget P Q).Realization := ⟨x.point, x.support_mem.1⟩
      change (oldTargetHomeomorph P Q).symm y =
        blockRetraction P Q f j (Realization.inclusion (oldTarget_le_block P Q f j) y)
      exact (blockRetraction_old P Q f j y).symm
  | some i =>
    cases p with
    | none =>
      let y : (oldTarget P Q).Realization := ⟨x.point, x.support_mem.2⟩
      change blockRetraction P Q f i (Realization.inclusion (oldTarget_le_block P Q f i) y) =
        (oldTargetHomeomorph P Q).symm y
      exact blockRetraction_old P Q f i y
    | some j =>
      by_cases hij : i = j
      · subst j
        rfl
      · have hy : x.point.weights.support ∈ oldTarget P Q := by
          rw [← oldTarget_intersection P Q f hij]
          exact x.support_mem
        let y : (oldTarget P Q).Realization := ⟨x.point, hy⟩
        exact (blockRetraction_old P Q f i y).trans (blockRetraction_old P Q f j y).symm

private theorem oldRange_iff (f : ∀ i, Morphism (P i) Q)
    (y : (cylinderFamily P Q f).Realization) :
    y ∈ Set.range (oldInclusion P Q f) ↔ y.point.weights.support ∈ oldTarget P Q := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (oldTargetHomeomorph P Q x).support_mem
  · intro hy
    let z : (oldTarget P Q).Realization := ⟨y.point, hy⟩
    refine ⟨(oldTargetHomeomorph P Q).symm z, ?_⟩
    apply PreAbstractSimplicialComplex.Realization.ext
    change (oldTargetHomeomorph P Q ((oldTargetHomeomorph P Q).symm z)).point = y.point
    rw [(oldTargetHomeomorph P Q).apply_symm_apply]

private theorem blockRange_iff (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (y : (cylinderFamily P Q f).Realization) :
    y ∈ Set.range (blockInclusion P Q f i) ↔ y.point.weights.support ∈ block P Q f i := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (blockHomeomorph P Q f i x).support_mem
  · intro hy
    let z : (block P Q f i).Realization := ⟨y.point, hy⟩
    refine ⟨(blockHomeomorph P Q f i).symm z, ?_⟩
    apply PreAbstractSimplicialComplex.Realization.ext
    change (blockHomeomorph P Q f i ((blockHomeomorph P Q f i).symm z)).point = y.point
    rw [(blockHomeomorph P Q f i).apply_symm_apply]

/-- The entire actual cylinder images intersect exactly in the unchanged old target image. -/
private theorem blockRange_intersection (f : ∀ i, Morphism (P i) Q) {i j : «I»} (hij : i ≠ j) :
    Set.range (blockInclusion P Q f i) ∩ Set.range (blockInclusion P Q f j) =
      Set.range (oldInclusion P Q f) := by
  ext y
  rw [Set.mem_inter_iff, blockRange_iff P Q f i, blockRange_iff P Q f j, oldRange_iff P Q f]
  rw [← oldTarget_intersection P Q f hij]
  rfl

private theorem oldBlock_global (f : ∀ i, Morphism (P i) Q) (i : «I») (q : Q.Realization) :
    blockInclusion P Q f i (smallOldTarget (f i) q) =
      oldInclusion P Q f q := by
  have h := congrArg
    (PreAbstractSimplicialComplex.Realization.inclusion (block_le_family P Q f i))
    (oldInBlock P Q f i q)
  change Realization.inclusion (block_le_family P Q f i)
      (blockHomeomorph P Q f i (smallOldTarget (f i) q)) =
    Realization.inclusion (oldTarget_le_family P Q f) (oldTargetHomeomorph P Q q)
  exact h

/-- The inclusion of the `i`-th copied domain, the barycentric subdivision of `P i`, into the
family cylinder through the `i`-th block. -/
def copiedInclusion (f : ∀ i, Morphism (P i) Q) (i : «I») :
    C((barycentricSubdivision (P i)).Realization, (cylinderFamily P Q f).Realization) :=
  (blockInclusion P Q f i).comp (smallCopiedDomain (f i))

theorem copiedInclusion_isClosedEmbedding (f : ∀ i, Morphism (P i) Q) (i : «I») :
    IsClosedEmbedding (copiedInclusion P Q f i) :=
  (blockInclusion_isClosedEmbedding P Q f i).comp
    (smallCopiedDomain_closed (f i))

theorem copied_old_disjoint (f : ∀ i, Morphism (P i) Q) (i : «I») :
    Disjoint (Set.range (copiedInclusion P Q f i)) (Set.range (oldInclusion P Q f)) := by
  rw [Set.disjoint_left]
  rintro y ⟨x, hx⟩ ⟨q, hq⟩
  have heq : smallCopiedDomain (f i) x =
      smallOldTarget (f i) q :=
    (blockInclusion_isClosedEmbedding P Q f i).injective
      (hx.trans ((oldBlock_global P Q f i q).trans hq).symm)
  exact (Set.disjoint_left.mp (smallCopied_old_disjoint (f i)))
    ⟨x, rfl⟩ ⟨q, heq.symm⟩

theorem copied_copied_disjoint (f : ∀ i, Morphism (P i) Q) {i j : «I»} (hij : i ≠ j) :
    Disjoint (Set.range (copiedInclusion P Q f i)) (Set.range (copiedInclusion P Q f j)) := by
  rw [Set.disjoint_left]
  rintro y ⟨x, hx⟩ ⟨z, hz⟩
  have hyi : y ∈ Set.range (blockInclusion P Q f i) :=
    ⟨smallCopiedDomain (f i) x, hx⟩
  have hyj : y ∈ Set.range (blockInclusion P Q f j) :=
    ⟨smallCopiedDomain (f j) z, hz⟩
  have hy : y ∈ Set.range (oldInclusion P Q f) := by
    rw [← blockRange_intersection P Q f hij]
    exact ⟨hyi, hyj⟩
  exact (Set.disjoint_left.mp (copied_old_disjoint P Q f i)) ⟨x, hx⟩ hy

private theorem cylinderFamily_faces (f : ∀ i, Morphism (P i) Q) (s : Finset (Labels (W := W) P)) :
    s ∈ cylinderFamily P Q f ↔ s ∈ oldTarget P Q ∨ ∃ i, s ∈ block P Q f i := by
  change s ∈ WeakFamilyUnionConstruction46.weakUnion (optionBlocks P Q f) ↔
    s ∈ oldTarget P Q ∨ ∃ i, s ∈ block P Q f i
  rw [WeakFamilyUnionConstruction46.mem_weakUnion (optionBlocks P Q f)]
  constructor
  · rintro ⟨o, ho⟩
    cases o with
    | none => exact Or.inl ho
    | some i => exact Or.inr ⟨i, ho⟩
  · rintro (ho | ⟨i, hi⟩)
    · exact ⟨none, ho⟩
    · exact ⟨some i, hi⟩

theorem copiedInclusion_point (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (x : (barycentricSubdivision (P i)).Realization) :
    (copiedInclusion P Q f i x).point =
      (x.point.map (Sum.inl : Face (P i) → Face (P i) ⊕ W)).map (tag (W := W) P i) := by
  change (blockInclusion P Q f i (smallCopiedDomain (f i) x)).point = _
  rw [blockInclusion_point, smallCopiedDomain_point]

end Tagged

namespace Retraction

open PreAbstractSimplicialComplex Tagged

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

/-- The retraction of the family cylinder onto `Q`, glued over its pieces: the identity on
`oldTarget` and `smallRetraction (f i)` on the `i`-th block. -/
def familyRetraction (f : ∀ i, Morphism (P i) Q) :
    C((cylinderFamily P Q f).Realization, Q.Realization) :=
  WeakFamilyUnionConstruction46.unionDesc (optionBlocks P Q f)
    (pieceRetractions P Q f) (pieceRetractions_agree P Q f)

theorem familyRetraction_old (f : ∀ i, Morphism (P i) Q) (q : Q.Realization) :
    familyRetraction P Q f (oldInclusion P Q f q) = q := by
  calc
    familyRetraction P Q f (oldInclusion P Q f q) =
        pieceRetractions P Q f none (oldTargetHomeomorph P Q q) :=
      WeakFamilyUnionConstruction46.unionDesc_component (optionBlocks P Q f)
        (pieceRetractions P Q f) (pieceRetractions_agree P Q f) none (oldTargetHomeomorph P Q q)
    _ = q := by
      change (oldTargetHomeomorph P Q).symm (oldTargetHomeomorph P Q q) = q
      exact (oldTargetHomeomorph P Q).symm_apply_apply q

private theorem familyRetraction_block (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (x : (smallCylinder (f i)).Realization) :
    familyRetraction P Q f (blockInclusion P Q f i x) = smallRetraction (f i) x := by
  calc
    familyRetraction P Q f (blockInclusion P Q f i x) =
        pieceRetractions P Q f (some i) (blockHomeomorph P Q f i x) :=
      WeakFamilyUnionConstruction46.unionDesc_component (optionBlocks P Q f)
        (pieceRetractions P Q f) (pieceRetractions_agree P Q f) (some i)
        (blockHomeomorph P Q f i x)
    _ = smallRetraction (f i) x := by
      change smallRetraction (f i)
        ((blockHomeomorph P Q f i).symm (blockHomeomorph P Q f i x)) = _
      rw [(blockHomeomorph P Q f i).symm_apply_apply]

theorem familyRetraction_copied (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (x : (barycentricSubdivision (P i)).Realization) :
    familyRetraction P Q f (copiedInclusion P Q f i x) =
      (f i).realization (barycentricHomeomorph (P i) x) := by
  change familyRetraction P Q f (blockInclusion P Q f i (smallCopiedDomain (f i) x)) = _
  rw [familyRetraction_block]
  exact smallRetraction_copied (f i) x

private def pieceHomotopy (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) :
    ∀ o, ContinuousMap.Homotopy (WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) o)
      ((oldInclusion P Q f).comp (pieceRetractions P Q f o)) := by
  intro o
  cases o with
  | none =>
    let L := WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) none
    refine (ContinuousMap.Homotopy.refl L).cast rfl ?_
    apply ContinuousMap.ext
    intro x
    let y : (oldTarget P Q).Realization := ⟨x.point, x.support_mem⟩
    simpa only [L, WeakFamilyUnionConstruction46.inclusion,
      oldInclusion, pieceRetractions, ContinuousMap.comp_apply, ContinuousMap.coe_apply,
      ContinuousMap.coe_mk, optionBlocks] using!
      congrArg (fun z : (oldTarget P Q).Realization =>
        Realization.inclusion (oldTarget_le_family P Q f) z)
        ((oldTargetHomeomorph P Q).apply_symm_apply y).symm
  | some i =>
    letI : Finite (Face (P i)) := hfinite i
    let H₀ := (smallCylinderDeformation (f i)).toHomotopy.compContinuousMap
      ((blockHomeomorph P Q f i).symm :
        C((block P Q f i).Realization, (smallCylinder (f i)).Realization))
    let H := (ContinuousMap.Homotopy.refl (blockInclusion P Q f i)).comp H₀
    refine H.cast ?_ ?_
    · apply ContinuousMap.ext
      intro x
      change WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) (some i)
          (blockHomeomorph P Q f i ((blockHomeomorph P Q f i).symm x)) =
        WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) (some i) x
      rw [(blockHomeomorph P Q f i).apply_symm_apply]
    · apply ContinuousMap.ext
      intro x
      change blockInclusion P Q f i (smallOldTarget (f i)
          (smallRetraction (f i) ((blockHomeomorph P Q f i).symm x))) =
        oldInclusion P Q f (smallRetraction (f i) ((blockHomeomorph P Q f i).symm x))
      exact oldBlock_global P Q f i _

private theorem pieceHomotopy_old (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) (i : «I»)
    (t : unitInterval) (x : (oldTarget P Q).Realization) :
    (pieceHomotopy P Q f hfinite (some i)).toContinuousMap
        (t, PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i) x) =
      (pieceHomotopy P Q f hfinite none).toContinuousMap (t, x) := by
  let : Finite (Face (P i)) := hfinite i
  let q := (oldTargetHomeomorph P Q).symm x
  have h := oldInBlock P Q f i q
  have hx : (blockHomeomorph P Q f i).symm
      (PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i) x) =
        smallOldTarget (f i) q := by
    apply (blockHomeomorph P Q f i).injective
    rw [(blockHomeomorph P Q f i).apply_symm_apply]
    exact (h.trans (congrArg
      (PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i))
      ((oldTargetHomeomorph P Q).apply_symm_apply x))).symm
  simp only [pieceHomotopy]
  change blockInclusion P Q f i (smallCylinderDeformation (f i)
      (t, (blockHomeomorph P Q f i).symm
        (PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i) x))) =
    WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) none x
  rw [hx, smallCylinderDeformation_old]
  apply Realization.ext
  have h₁ := congrArg (fun z : (cylinderFamily P Q f).Realization => z.point)
    (oldBlock_global P Q f i q)
  have h₂ : (oldInclusion P Q f q).point = x.point := by
    simpa only [oldInclusion, ContinuousMap.comp_apply, ContinuousMap.coe_apply,
      ContinuousMap.coe_mk, Realization.inclusion_point, q] using!
      congrArg (fun z : (oldTarget P Q).Realization => z.point)
        ((oldTargetHomeomorph P Q).apply_symm_apply x)
  simpa only [WeakFamilyUnionConstruction46.inclusion, ContinuousMap.coe_mk,
    Realization.inclusion_point] using! h₁.trans h₂

private theorem pieceHomotopy_agree (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) :
    ∀ o p, ∀ x : (optionBlocks P Q f o ⊓ optionBlocks P Q f p).Realization,
      ∀ t : unitInterval,
        (pieceHomotopy P Q f hfinite o).toContinuousMap
            (t, PreAbstractSimplicialComplex.Realization.inclusion inf_le_left x) =
          (pieceHomotopy P Q f hfinite p).toContinuousMap
            (t, PreAbstractSimplicialComplex.Realization.inclusion inf_le_right x) := by
  intro o p x t
  cases o with
  | none =>
    cases p with
    | none => rfl
    | some j =>
      let y : (oldTarget P Q).Realization := ⟨x.point, x.support_mem.1⟩
      exact (pieceHomotopy_old P Q f hfinite j t y).symm
  | some i =>
    cases p with
    | none =>
      let y : (oldTarget P Q).Realization := ⟨x.point, x.support_mem.2⟩
      exact pieceHomotopy_old P Q f hfinite i t y
    | some j =>
      by_cases hij : i = j
      · subst j
        rfl
      · have hy : x.point.weights.support ∈ oldTarget P Q := by
          rw [← oldTarget_intersection P Q f hij]
          exact x.support_mem
        let y : (oldTarget P Q).Realization := ⟨x.point, hy⟩
        exact (pieceHomotopy_old P Q f hfinite i t y).trans (pieceHomotopy_old P Q f hfinite j t y).symm

private def curriedPieces (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) :
    ∀ o, C((optionBlocks P Q f o).Realization,
      C(unitInterval, (cylinderFamily P Q f).Realization)) := by
  intro o
  let H : C((optionBlocks P Q f o).Realization × unitInterval,
      (cylinderFamily P Q f).Realization) :=
    ⟨fun z => (pieceHomotopy P Q f hfinite o).toContinuousMap (z.2, z.1),
      (pieceHomotopy P Q f hfinite o).toContinuousMap.continuous.comp
        (continuous_snd.prodMk continuous_fst)⟩
  exact H.curry

private theorem curriedPieces_agree (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) :
    ∀ o p, ∀ x : (optionBlocks P Q f o ⊓ optionBlocks P Q f p).Realization,
      curriedPieces P Q f hfinite o (PreAbstractSimplicialComplex.Realization.inclusion inf_le_left x) =
        curriedPieces P Q f hfinite p (PreAbstractSimplicialComplex.Realization.inclusion inf_le_right x) := by
  intro o p x
  apply ContinuousMap.ext
  intro t
  exact pieceHomotopy_agree P Q f hfinite o p x t

private def curriedFamily (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) :
    C((cylinderFamily P Q f).Realization, C(unitInterval, (cylinderFamily P Q f).Realization)) :=
  WeakFamilyUnionConstruction46.unionDesc (optionBlocks P Q f)
    (curriedPieces P Q f hfinite) (curriedPieces_agree P Q f hfinite)

private theorem curriedFamily_component (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) (o : Option «I»)
    (x : (optionBlocks P Q f o).Realization) (t : unitInterval) :
    curriedFamily P Q f hfinite (WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) o x) t =
      (pieceHomotopy P Q f hfinite o).toContinuousMap (t, x) :=
  congrArg (fun g : C(unitInterval, (cylinderFamily P Q f).Realization) => g t)
    (WeakFamilyUnionConstruction46.unionDesc_component (optionBlocks P Q f)
      (curriedPieces P Q f hfinite) (curriedPieces_agree P Q f hfinite) o x)

/-- Ordinary joint continuity follows by weak-face descent and compact-open interval evaluation. -/
def familyHomotopy (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) :
    ContinuousMap.Homotopy (ContinuousMap.id (cylinderFamily P Q f).Realization)
      ((oldInclusion P Q f).comp (familyRetraction P Q f)) where
  toFun z := curriedFamily P Q f hfinite z.2 z.1
  continuous_toFun := ((curriedFamily P Q f hfinite).continuous.comp continuous_snd).eval continuous_fst
  map_zero_left x := by
    change curriedFamily P Q f hfinite x 0 = x
    let o := WeakFamilyUnionConstruction46.sourceIndex (optionBlocks P Q f) x
    let y : (optionBlocks P Q f o).Realization :=
      ⟨x.point, WeakFamilyUnionConstruction46.sourceIndex_support (optionBlocks P Q f) x⟩
    have hy : WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) o y = x :=
      Realization.ext rfl
    have hc : curriedFamily P Q f hfinite x 0 =
        (pieceHomotopy P Q f hfinite o).toContinuousMap (0, y) := by
      simpa only [hy] using! curriedFamily_component P Q f hfinite o y 0
    have hz : (pieceHomotopy P Q f hfinite o).toContinuousMap (0, y) = x := by
      simpa only [hy] using! (pieceHomotopy P Q f hfinite o).map_zero_left y
    exact hc.trans hz
  map_one_left x := by
    change curriedFamily P Q f hfinite x 1 = oldInclusion P Q f (familyRetraction P Q f x)
    let o := WeakFamilyUnionConstruction46.sourceIndex (optionBlocks P Q f) x
    let y : (optionBlocks P Q f o).Realization :=
      ⟨x.point, WeakFamilyUnionConstruction46.sourceIndex_support (optionBlocks P Q f) x⟩
    have hy : WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) o y = x :=
      Realization.ext rfl
    have hc : curriedFamily P Q f hfinite x 1 =
        (pieceHomotopy P Q f hfinite o).toContinuousMap (1, y) := by
      simpa only [hy] using! curriedFamily_component P Q f hfinite o y 1
    have hz : (pieceHomotopy P Q f hfinite o).toContinuousMap (1, y) =
        oldInclusion P Q f (pieceRetractions P Q f o y) :=
      (pieceHomotopy P Q f hfinite o).map_one_left y
    have hr : pieceRetractions P Q f o y = familyRetraction P Q f x := by
      simpa only [familyRetraction, hy] using!
        (WeakFamilyUnionConstruction46.unionDesc_component (optionBlocks P Q f)
          (pieceRetractions P Q f) (pieceRetractions_agree P Q f) o y).symm
    exact hc.trans (hz.trans (congrArg (fun z : Q.Realization => oldInclusion P Q f z) hr))

private theorem familyHomotopy_old (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) (t : unitInterval)
    (q : Q.Realization) :
    familyHomotopy P Q f hfinite (t, oldInclusion P Q f q) = oldInclusion P Q f q := by
  change curriedFamily P Q f hfinite
      (WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) none
        (oldTargetHomeomorph P Q q)) t = _
  simpa only [ContinuousMap.Homotopy.coe_toContinuousMap, pieceHomotopy,
    ContinuousMap.Homotopy.cast_apply, ContinuousMap.Homotopy.refl_apply,
    WeakFamilyUnionConstruction46.inclusion, oldInclusion, ContinuousMap.comp_apply] using!
    curriedFamily_component P Q f hfinite none (oldTargetHomeomorph P Q q) t

/-- A homotopy from the identity of the family cylinder to `oldInclusion ∘ familyRetraction`,
fixing the image of `Q`. -/
def familyHomotopyRelativeOld (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (cylinderFamily P Q f).Realization)
      ((oldInclusion P Q f).comp (familyRetraction P Q f)) (Set.range (oldInclusion P Q f)) where
  toHomotopy := familyHomotopy P Q f hfinite
  prop' t x hx := by
    obtain ⟨q, rfl⟩ := hx
    exact familyHomotopy_old P Q f hfinite t q

end Retraction

namespace CylinderPushout

open CategoryTheory Limits PreAbstractSimplicialComplex Tagged

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

private def pieceMaps (f : ∀ i, Morphism (P i) Q) {Z : Type*} [TopologicalSpace Z]
    (g : C((oldTarget P Q).Realization, Z)) (h : ∀ i, C((block P Q f i).Realization, Z)) :
    ∀ o, C((optionBlocks P Q f o).Realization, Z)
  | none => g
  | some i => h i

private theorem pieceMaps_agree (f : ∀ i, Morphism (P i) Q)
    {Z : Type*} [TopologicalSpace Z] (g : C((oldTarget P Q).Realization, Z))
    (h : ∀ i, C((block P Q f i).Realization, Z))
    (hold : ∀ i, ∀ x : (oldTarget P Q).Realization,
      h i (PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i) x) = g x) :
    ∀ o p, ∀ x : (optionBlocks P Q f o ⊓ optionBlocks P Q f p).Realization,
      pieceMaps P Q f g h o (PreAbstractSimplicialComplex.Realization.inclusion inf_le_left x) =
        pieceMaps P Q f g h p (PreAbstractSimplicialComplex.Realization.inclusion inf_le_right x) := by
  intro o p x
  cases o with
  | none =>
    cases p with
    | none => rfl
    | some j =>
      let y : (oldTarget P Q).Realization := ⟨x.point, x.support_mem.1⟩
      exact (hold j y).symm
  | some i =>
    cases p with
    | none =>
      let y : (oldTarget P Q).Realization := ⟨x.point, x.support_mem.2⟩
      exact hold i y
    | some j =>
      by_cases hij : i = j
      · subst j
        rfl
      · have hy : x.point.weights.support ∈ oldTarget P Q := by
          rw [← oldTarget_intersection P Q f hij]
          exact x.support_mem
        let y : (oldTarget P Q).Realization := ⟨x.point, hy⟩
        exact (hold i y).trans (hold j y).symm

private def overlapSum : TopCat.{max u v w} :=
  TopCat.of (Σ _ : «I», (oldTarget P Q).Realization)

private def blockSum (f : ∀ i, Morphism (P i) Q) : TopCat.{max u v w} :=
  TopCat.of (Σ i : «I», (block P Q f i).Realization)

private def overlapToBlocks (f : ∀ i, Morphism (P i) Q) :
    overlapSum P Q ⟶ blockSum P Q f :=
  TopCat.ofHom
    ⟨Sigma.map (id : «I» → «I»)
      (fun i => PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i)),
      Continuous.sigma_map (fun i =>
        PreAbstractSimplicialComplex.Realization.continuous_inclusion (oldTarget_le_block P Q f i))⟩

private def overlapFold :
    overlapSum P Q ⟶ TopCat.of (oldTarget P Q).Realization :=
  TopCat.ofHom ⟨fun p => p.2, continuous_sigma (fun _ => continuous_id)⟩

private def blocksToFamily (f : ∀ i, Morphism (P i) Q) :
    blockSum P Q f ⟶ TopCat.of (cylinderFamily P Q f).Realization :=
  TopCat.ofHom ⟨fun p => WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) (some p.1) p.2,
    continuous_sigma (fun i =>
      (WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) (some i)).continuous)⟩

private def oldToFamily (f : ∀ i, Morphism (P i) Q) :
    TopCat.of (oldTarget P Q).Realization ⟶ TopCat.of (cylinderFamily P Q f).Realization :=
  TopCat.ofHom (WeakFamilyUnionConstruction46.inclusion (optionBlocks P Q f) none)

/-- No gluing presentation is supplied: its universal map is constructed by actual weak-face descent. -/
private theorem cylinderFamily_isPushout (f : ∀ i, Morphism (P i) Q) :
    IsPushout (overlapToBlocks P Q f) (overlapFold P Q)
      (blocksToFamily P Q f) (oldToFamily P Q f) := by
  let comm : CommSq (overlapToBlocks P Q f) (overlapFold P Q)
      (blocksToFamily P Q f) (oldToFamily P Q f) := by
    refine ⟨?_⟩
    apply TopCat.ext
    rintro ⟨i, x⟩
    apply PreAbstractSimplicialComplex.Realization.ext
    rfl
  apply IsPushout.of_isColimit' comm
  apply PushoutCocone.isColimitAux'
  intro s
  let g : C((oldTarget P Q).Realization, s.pt) := s.inr.hom
  let h : ∀ i, C((block P Q f i).Realization, s.pt) := fun i =>
    ⟨fun x => s.inl ⟨i, x⟩, s.inl.hom.continuous.comp (continuous_sigmaMk (i := i))⟩
  have hold : ∀ i, ∀ x : (oldTarget P Q).Realization,
      h i (PreAbstractSimplicialComplex.Realization.inclusion (oldTarget_le_block P Q f i) x) = g x := by
    intro i x
    have hc := ConcreteCategory.congr_hom s.condition ⟨i, x⟩
    exact hc
  let d := TopCat.ofHom (WeakFamilyUnionConstruction46.unionDesc (optionBlocks P Q f)
    (pieceMaps P Q f g h) (pieceMaps_agree P Q f g h hold))
  refine ⟨d, ?_, ?_, ?_⟩
  · apply TopCat.ext
    rintro ⟨i, x⟩
    exact WeakFamilyUnionConstruction46.unionDesc_component (optionBlocks P Q f)
      (pieceMaps P Q f g h) (pieceMaps_agree P Q f g h hold) (some i) x
  · apply TopCat.ext
    intro x
    exact WeakFamilyUnionConstruction46.unionDesc_component (optionBlocks P Q f)
      (pieceMaps P Q f g h) (pieceMaps_agree P Q f g h hold) none x
  · intro m hmBlocks hmOld
    apply TopCat.hom_ext
    apply WeakFamilyUnionConstruction46.unionDesc_unique (optionBlocks P Q f)
      (pieceMaps P Q f g h) (pieceMaps_agree P Q f g h hold) m.hom
    intro o x
    cases o with
    | none => exact ConcreteCategory.congr_hom hmOld x
    | some i => exact ConcreteCategory.congr_hom hmBlocks ⟨i, x⟩

end CylinderPushout

namespace Cone

open CategoryTheory PreAbstractSimplicialComplex Tagged

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

/-- Labels of the family cone: the family-cylinder labels, plus an apex label `i` for each
index. -/
abbrev ConeLabels := Labels (W := W) P ⊕ «I»

private def apexTag (i : «I») : PUnit.{max v w + 1} ↪ «I» :=
  ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩

/-- Embeds the labels of the `i`-th small cone into the family-cone labels: cylinder labels by
`tag`, and the apex to `i`. -/
def coneTag (i : «I») : (Face (P i) ⊕ W) ⊕ PUnit.{max v w + 1} ↪ ConeLabels (W := W) P :=
  Function.Embedding.sumMap (tag (W := W) P i) (apexTag.{u, v, w} i)

/-- The family cylinder, relabelled into the family-cone labels by `Sum.inl`. -/
@[expose] def cylinderPart (f : ∀ i, Morphism (P i) Q) :
    PreAbstractSimplicialComplex (ConeLabels (W := W) P) :=
  MappingCylinder.relabelComplex (cylinderFamily P Q f)
    (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)

/-- The cone on the `i`-th copied domain, relabelled into the family-cone labels by
`coneTag`. -/
@[expose] def attachedBlock (i : «I») : PreAbstractSimplicialComplex (ConeLabels (W := W) P) :=
  MappingCylinder.relabelComplex (MappingCylinder.coneComplex (MappingCylinder.domainComplex (P i) W))
    (coneTag (W := W) P i)

private def copiedBlock (i : «I») : PreAbstractSimplicialComplex (ConeLabels (W := W) P) :=
  MappingCylinder.relabelComplex (MappingCylinder.domainComplex (P i) W)
    ((tag (W := W) P i).trans (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P))

private def attachedFamily : PreAbstractSimplicialComplex (ConeLabels (W := W) P) := ⨆ i, attachedBlock (W := W) P i
private def copiedFamily : PreAbstractSimplicialComplex (ConeLabels (W := W) P) := ⨆ i, copiedBlock (W := W) P i

/-- The family mapping cone: the family cylinder together with the cone on every tagged copied
domain. -/
@[expose] def associatedFamily (f : ∀ i, Morphism (P i) Q) :
    PreAbstractSimplicialComplex (ConeLabels (W := W) P) :=
  cylinderPart P Q f ⊔ ⨆ i, attachedBlock (W := W) P i

private theorem copied_le_cylinder (f : ∀ i, Morphism (P i) Q) (i : «I») :
    copiedBlock (W := W) P i ≤ cylinderPart P Q f := by
  intro s hs
  change s ∈ MappingCylinder.relabelComplex (MappingCylinder.domainComplex (P i) W)
    ((tag (W := W) P i).trans
      (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)) at hs
  obtain ⟨a, ha, rfl⟩ := hs
  refine ⟨a.image (tag (W := W) P i), ?_, ?_⟩
  · apply block_le_family P Q f i
    refine ⟨a, small_domain_le (f i) ha, ?_⟩
    simp only [← Finset.map_eq_image]
  · simp only [← Finset.map_eq_image, Finset.map_map]

private theorem copied_le_attached (i : «I») : copiedBlock (W := W) P i ≤ attachedBlock (W := W) P i := by
  intro s hs
  change s ∈ MappingCylinder.relabelComplex (MappingCylinder.domainComplex (P i) W)
    ((tag (W := W) P i).trans
      (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)) at hs
  obtain ⟨a, ha, rfl⟩ := hs
  refine ⟨a.image (Function.Embedding.inl : Face (P i) ⊕ W ↪
    (Face (P i) ⊕ W) ⊕ PUnit.{max v w + 1}), ?_, ?_⟩
  · apply MappingCylinder.cone_base_le (MappingCylinder.domainComplex (P i) W)
    refine ⟨a, ha, ?_⟩
    simp only [← Finset.map_eq_image]
  · simp only [← Finset.map_eq_image, Finset.map_map]
    rfl

/-- No apex lies in the cylinder part; the whole intersection is the actual copied domain. -/
private theorem cylinder_attached_intersection (f : ∀ i, Morphism (P i) Q) (i : «I») :
    cylinderPart P Q f ⊓ attachedBlock (W := W) P i = copiedBlock (W := W) P i := by
  apply le_antisymm
  · intro s hs
    have hcyMem : s ∈ MappingCylinder.relabelComplex (cylinderFamily P Q f)
        (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) := hs.1
    have hconeMem : s ∈ MappingCylinder.relabelComplex
        (MappingCylinder.coneComplex (MappingCylinder.domainComplex (P i) W))
        (coneTag (W := W) P i) := hs.2
    obtain ⟨b, hb, hcy⟩ := hcyMem
    obtain ⟨a, ha, hcone⟩ := hconeMem
    simp only [← Finset.map_eq_image] at hcy hcone
    have hright : a.toRight = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hi : Sum.inr i ∈ a.image (coneTag (W := W) P i) :=
        Finset.mem_image.mpr ⟨Sum.inr p, Finset.mem_toRight.mp hp, rfl⟩
      have hi' : Sum.inr i ∈ b.image (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) := by
        simp only [← Finset.map_eq_image] at hi ⊢
        rw [hcy, ← hcone]
        exact hi
      obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hi'
      cases heq
    have hnonempty : a.toLeft.Nonempty := by
      obtain ⟨x, hx⟩ :=
        ((MappingCylinder.coneComplex (MappingCylinder.domainComplex (P i) W)).isRelLowerSet_faces ha).1
      cases x with
      | inl x => exact ⟨x, Finset.mem_toLeft.mpr hx⟩
      | inr x => exact False.elim (by simpa only [hright, Finset.notMem_empty] using
          (Finset.mem_toRight.mpr hx))
    have hbase : a.toLeft ∈ MappingCylinder.domainComplex (P i) W :=
      ((MappingCylinder.mem_coneComplex _ _).mp ha).2.resolve_right hnonempty.ne_empty
    refine ⟨a.toLeft, hbase, ?_⟩
    have hsplit := (Finset.toLeft_disjSum_toRight (u := a))
    simp only [hright, Finset.disjSum_empty] at hsplit
    simp only [← Finset.map_eq_image]
    calc
      a.toLeft.map ((tag (W := W) P i).trans (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)) =
          (a.toLeft.map (Function.Embedding.inl : Face (P i) ⊕ W ↪
            (Face (P i) ⊕ W) ⊕ PUnit.{max v w + 1})).map (coneTag (W := W) P i) := by
        rw [Finset.map_map]
        rfl
      _ = a.map (coneTag (W := W) P i) := congrArg (fun t => t.map (coneTag (W := W) P i)) hsplit
      _ = s := hcone
  · exact le_inf (copied_le_cylinder P Q f i) (copied_le_attached (W := W) P i)

private def familyIndex : ConeLabels (W := W) P → Option «I»
  | Sum.inl (Sum.inl a) => some a.1
  | Sum.inl (Sum.inr _) => none
  | Sum.inr i => some i

/-- Every actual attached-cone vertex keeps its own tag; old target vertices never enter it. -/
private theorem attached_index (i : «I») (s : Finset (ConeLabels (W := W) P)) (hs : s ∈ attachedBlock (W := W) P i)
    (z : ConeLabels (W := W) P) (hz : z ∈ s) : familyIndex (W := W) P z = some i := by
  obtain ⟨a, ha, hsa⟩ := hs
  simp only [← Finset.map_eq_image] at hsa
  rw [← hsa] at hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
  cases x with
  | inr p => rfl
  | inl y =>
    have hy : y ∈ a.toLeft := by
      exact Finset.mem_toLeft.mpr hx
    have hbase : a.toLeft ∈ MappingCylinder.domainComplex (P i) W :=
      ((MappingCylinder.mem_coneComplex _ _).mp ha).2.resolve_right (by
        intro hempty
        simp only [hempty, Finset.notMem_empty] at hy)
    obtain ⟨b, hb, hbeq⟩ := hbase
    simp only [← Finset.map_eq_image] at hbeq
    have hy' : y ∈ b.image (Function.Embedding.inl : Face (P i) ↪ Face (P i) ⊕ W) := by
      simp only [← Finset.map_eq_image]
      rw [hbeq]
      exact hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy'
    rfl

private theorem attached_disjoint_faces {i j : «I»} (hij : i ≠ j) :
    attachedBlock (W := W) P i ⊓ attachedBlock (W := W) P j = ⊥ := by
  apply le_antisymm
  · intro s hs
    obtain ⟨z, hz⟩ := ((attachedBlock (W := W) P i).isRelLowerSet_faces hs.1).1
    exact hij (Option.some.inj ((attached_index (W := W) P i s hs.1 z hz).symm.trans
      (attached_index (W := W) P j s hs.2 z hz)))
  · exact bot_le

private theorem copiedFamily_le_cylinder (f : ∀ i, Morphism (P i) Q) :
    copiedFamily (W := W) P ≤ cylinderPart P Q f :=
  iSup_le (copied_le_cylinder P Q f)

private theorem copiedFamily_le_attached : copiedFamily (W := W) P ≤ attachedFamily (W := W) P :=
  iSup_le (fun i => (copied_le_attached (W := W) P i).trans (le_iSup (attachedBlock (W := W) P) i))

private theorem aggregate_intersection (f : ∀ i, Morphism (P i) Q) :
    cylinderPart P Q f ⊓ attachedFamily (W := W) P = copiedFamily (W := W) P := by
  apply le_antisymm
  · intro s hs
    obtain ⟨i, hi⟩ := (WeakFamilyUnionConstruction46.mem_weakUnion (attachedBlock (W := W) P) s).mp hs.2
    have hc : s ∈ copiedBlock (W := W) P i := by
      rw [← cylinder_attached_intersection P Q f i]
      exact ⟨hs.1, hi⟩
    exact (le_iSup (copiedBlock (W := W) P) i) hc
  · exact le_inf (copiedFamily_le_cylinder P Q f) (copiedFamily_le_attached (W := W) P)

/-- This is the actual ordinary weak-realization attachment pushout for the ENTIRE cone family. -/
private theorem associatedFamily_isPushout (f : ∀ i, Morphism (P i) Q) :
    CategoryTheory.IsPushout
      (TopCat.ofHom (MappingCylinder.inclusionMorphism (copiedFamily_le_cylinder P Q f)).realization)
      (TopCat.ofHom (MappingCylinder.inclusionMorphism (copiedFamily_le_attached (W := W) P)).realization)
      (TopCat.ofHom (MappingCylinder.inclusionMorphism
        (le_sup_left : cylinderPart P Q f ≤ associatedFamily P Q f)).realization)
      (TopCat.ofHom (MappingCylinder.inclusionMorphism
        (le_sup_right : attachedFamily (W := W) P ≤ associatedFamily P Q f)).realization) :=
  MappingCylinder.isPushout_union_of_intersection _ _ _ (aggregate_intersection P Q f) _ _

end Cone

namespace Comparisons

open CategoryTheory PreAbstractSimplicialComplex Tagged Cone

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

/-- The homeomorphism of sigma types induced by a family of homeomorphisms
`e j : X j ≃ₜ Y j`. -/
def sigmaHomeomorph {J : Type*} {X Y : J → Type*}
    [∀ j, TopologicalSpace (X j)] [∀ j, TopologicalSpace (Y j)]
    (e : ∀ j, X j ≃ₜ Y j) : (Σ j, X j) ≃ₜ (Σ j, Y j) :=
  FamilyConeComparisonsConstruction46.sigmaHomeomorph e

/-- The shared sigma homeomorphism evaluates on each original summand. -/
theorem sigmaHomeomorph_apply {J : Type*} {X Y : J → Type*}
    [∀ j, TopologicalSpace (X j)] [∀ j, TopologicalSpace (Y j)]
    (e : ∀ j, X j ≃ₜ Y j) (j : J) (x : X j) :
    sigmaHomeomorph e ⟨j, x⟩ = (⟨j, e j x⟩ : Σ j, Y j) := by rfl

/-- Its actual inverse evaluates on the same summand. -/
theorem sigmaHomeomorph_symm_apply {J : Type*} {X Y : J → Type*}
    [∀ j, TopologicalSpace (X j)] [∀ j, TopologicalSpace (Y j)]
    (e : ∀ j, X j ≃ₜ Y j) (j : J) (y : Y j) :
    (sigmaHomeomorph e).symm ⟨j, y⟩ = (⟨j, (e j).symm y⟩ : Σ j, X j) := by rfl

private theorem copied_disjoint_faces {i j : «I»} (hij : i ≠ j) :
    copiedBlock (W := W) P i ⊓ copiedBlock (W := W) P j = ⊥ := by
  apply le_antisymm
  · rw [← attached_disjoint_faces (W := W) P hij]
    exact inf_le_inf (copied_le_attached (W := W) P i) (copied_le_attached (W := W) P j)
  · exact bot_le

private def copiedSigmaHomeomorph :
    (Σ i, (MappingCylinder.domainComplex (P i) W).Realization) ≃ₜ (copiedFamily (W := W) P).Realization :=
  (sigmaHomeomorph (fun i => MappingCylinder.relabelHomeomorph
    (MappingCylinder.domainComplex (P i) W)
    ((tag (W := W) P i).trans
      (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)))).trans
      (show (Σ i, (MappingCylinder.relabelComplex (MappingCylinder.domainComplex (P i) W)
          ((tag (W := W) P i).trans
            (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P))).Realization) ≃ₜ
          (copiedFamily (W := W) P).Realization from by
        change (Σ i, (copiedBlock (W := W) P i).Realization) ≃ₜ
          (WeakFamilyUnionConstruction46.weakUnion (copiedBlock (W := W) P)).Realization
        exact WeakFamilyUnionConstruction46.disjointUnionHomeomorph (copiedBlock (W := W) P)
          (fun _ _ hij => copied_disjoint_faces (W := W) P hij))

private def scalarConeHomeomorph (i : «I») (hfinite : Finite (Face (P i))) :
    TopCat.cone (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization) ≃ₜ
      (attachedBlock (W := W) P i).Realization := by
  letI := hfinite
  letI := MappingCylinder.finiteFaces_domainComplex (P i) W
  let e : (MappingCylinder.coneComplex (MappingCylinder.domainComplex (P i) W)).Realization ≃ₜ
      (attachedBlock (W := W) P i).Realization := by
    change (MappingCylinder.coneComplex (MappingCylinder.domainComplex (P i) W)).Realization ≃ₜ
      (MappingCylinder.relabelComplex
        (MappingCylinder.coneComplex (MappingCylinder.domainComplex (P i) W))
        (coneTag (W := W) P i)).Realization
    exact MappingCylinder.relabelHomeomorph
      (MappingCylinder.coneComplex (MappingCylinder.domainComplex (P i) W)) (coneTag (W := W) P i)
  exact (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex (P i) W)).trans e

private def ordinaryConeSigmaHomeomorph (hfinite : ∀ i, Finite (Face (P i))) :
    (Σ i, TopCat.cone (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization)) ≃ₜ
      (attachedFamily (W := W) P).Realization :=
  (sigmaHomeomorph (fun i => scalarConeHomeomorph (W := W) P i (hfinite i))).trans
    (WeakFamilyUnionConstruction46.disjointUnionHomeomorph (attachedBlock (W := W) P)
      (fun _ _ hij => attached_disjoint_faces (W := W) P hij))

private theorem copiedSigmaHomeomorph_point (i : «I»)
    (x : (MappingCylinder.domainComplex (P i) W).Realization) :
    (copiedSigmaHomeomorph (W := W) P ⟨i, x⟩).point =
      x.point.map ((tag (W := W) P i).trans (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)) :=
  MappingCylinder.relabelMorphism_point (MappingCylinder.domainComplex (P i) W)
    ((tag (W := W) P i).trans (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)) x

private theorem coneSigmaHomeomorph_base (hfinite : ∀ i, Finite (Face (P i))) (i : «I»)
    (x : (MappingCylinder.domainComplex (P i) W).Realization) :
    ordinaryConeSigmaHomeomorph (W := W) P hfinite
      ⟨i, TopCat.coneBase (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization) x⟩ =
        PreAbstractSimplicialComplex.Realization.inclusion (copiedFamily_le_attached (W := W) P)
          (copiedSigmaHomeomorph (W := W) P ⟨i, x⟩) := by
  let := hfinite i
  let := MappingCylinder.finiteFaces_domainComplex (P i) W
  apply PreAbstractSimplicialComplex.Realization.ext
  change ((MappingCylinder.relabelMorphism
    (MappingCylinder.coneComplex (MappingCylinder.domainComplex (P i) W)) (coneTag (W := W) P i)).realization
      (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex (P i) W)
        (TopCat.coneBase (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization) x))).point = _
  rw [MappingCylinder.relabelMorphism_point, MappingCylinder.ordinaryConeHomeomorph_base,
    MappingCylinder.coneBaseMorphism_point, Realization.inclusion_point, copiedSigmaHomeomorph_point,
    Convexity.StdSimplex.map_map]
  rfl

/-- The actual empty family has no copied-domain or cone points; the old cylinder is retained. -/
private theorem associatedFamily_empty_index (f : ∀ i, Morphism (P i) Q) [IsEmpty «I»] :
    associatedFamily P Q f = MappingCylinder.relabelComplex (oldTarget P Q)
      (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) := by
  have hc : cylinderFamily P Q f = oldTarget P Q := cylinderFamily_empty_index P Q f
  have ha : attachedFamily (W := W) P = ⊥ := by
    apply le_antisymm
    · apply iSup_le
      intro i
      exact isEmptyElim i
    · exact bot_le
  change MappingCylinder.relabelComplex (cylinderFamily P Q f)
    (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) ⊔ attachedFamily (W := W) P = _
  rw [hc, ha, sup_bot_eq]

end Comparisons

namespace CylinderSpan

open CategoryTheory Limits PreAbstractSimplicialComplex Tagged
open CylinderPushout Comparisons

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

private abbrev LiftedBlocks (f : ∀ i, Morphism (P i) Q) :=
  Σ i, ULift.{max u v w} (smallCylinder (f i)).Realization

private def oldHomeomorph : ULift.{max u v w} Q.Realization ≃ₜ (oldTarget P Q).Realization :=
  Homeomorph.ulift.trans (oldTargetHomeomorph P Q)

private def overlapHomeomorph : (Σ _ : «I», ULift.{max u v w} Q.Realization) ≃ₜ overlapSum P Q :=
  sigmaHomeomorph (fun _ : «I» => oldHomeomorph P Q)

private def blocksHomeomorph (f : ∀ i, Morphism (P i) Q) :
    LiftedBlocks P Q f ≃ₜ blockSum P Q f :=
  sigmaHomeomorph (fun i => Homeomorph.ulift.trans (blockHomeomorph P Q f i))

private def actualBoundary (f : ∀ i, Morphism (P i) Q) :
    TopCat.of ((Σ _ : «I», ULift.{max u v w} Q.Realization)) ⟶ TopCat.of (LiftedBlocks P Q f) :=
  TopCat.ofHom ⟨Sigma.map (id : «I» → «I») (fun i q =>
      ULift.up (smallOldTarget (f i) q.down)),
    Continuous.sigma_map (fun i => continuous_uliftUp.comp
      ((smallOldTarget (f i)).continuous.comp continuous_uliftDown))⟩

private def actualFold :
    TopCat.of ((Σ _ : «I», ULift.{max u v w} Q.Realization)) ⟶ TopCat.of (ULift.{max u v w} Q.Realization) :=
  TopCat.ofHom ⟨fun p => p.2, continuous_sigma (fun _ => continuous_id)⟩

private def actualBlocks (f : ∀ i, Morphism (P i) Q) :
    TopCat.of (LiftedBlocks P Q f) ⟶ TopCat.of (cylinderFamily P Q f).Realization :=
  TopCat.ofHom ⟨fun p => blockInclusion P Q f p.1 p.2.down,
    continuous_sigma (fun i => (blockInclusion P Q f i).continuous.comp continuous_uliftDown)⟩

private def actualOld (f : ∀ i, Morphism (P i) Q) :
    TopCat.of (ULift.{max u v w} Q.Realization) ⟶ TopCat.of (cylinderFamily P Q f).Realization :=
  TopCat.ofHom ⟨fun q => oldInclusion P Q f q.down,
    (oldInclusion P Q f).continuous.comp continuous_uliftDown⟩

/-- The unchanged scalar target maps and their actual family are the ordinary pushout span. -/
private theorem actualCylinderFamily_isPushout (f : ∀ i, Morphism (P i) Q) :
    IsPushout (actualBoundary P Q f) (actualFold.{u, v, w} Q) (actualBlocks P Q f) (actualOld P Q f) := by
  let e₁ : TopCat.of ((Σ _ : «I», ULift.{max u v w} Q.Realization)) ≅ overlapSum P Q :=
    TopCat.isoOfHomeo (overlapHomeomorph P Q)
  let e₂ : TopCat.of (LiftedBlocks P Q f) ≅ blockSum P Q f :=
    TopCat.isoOfHomeo (blocksHomeomorph P Q f)
  let e₃ : TopCat.of (ULift.{max u v w} Q.Realization) ≅ TopCat.of (oldTarget P Q).Realization :=
    TopCat.isoOfHomeo (oldHomeomorph P Q)
  refine (cylinderFamily_isPushout P Q f).of_iso' e₁ e₂ e₃ (Iso.refl _) ?_ ?_ ?_ ?_
  · apply ConcreteCategory.hom_ext
    rintro ⟨i, q⟩
    change (⟨i, Realization.inclusion (oldTarget_le_block P Q f i)
        (oldTargetHomeomorph P Q q.down)⟩ : Σ i, (block P Q f i).Realization) =
      ⟨i, blockHomeomorph P Q f i (smallOldTarget (f i) q.down)⟩
    exact congrArg (fun z : (block P Q f i).Realization =>
      (⟨i, z⟩ : Σ i, (block P Q f i).Realization)) (oldInBlock P Q f i q.down).symm
  · apply ConcreteCategory.hom_ext
    rintro ⟨i, q⟩
    rfl
  · apply ConcreteCategory.hom_ext
    rintro ⟨i, x⟩
    rfl
  · apply ConcreteCategory.hom_ext
    intro q
    rfl

end CylinderSpan

namespace ConePushout

open CategoryTheory Limits PreAbstractSimplicialComplex Tagged
open Cone Comparisons

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

/-- The disjoint union of the copied domains `domainComplex (P i) W`, as a space. -/
abbrev domainSum (W : Type w) : TopCat.{max u v w} :=
  TopCat.of (Σ i, (MappingCylinder.domainComplex (P i) W).Realization)

/-- The disjoint union of the topological cones on the copied domains. -/
abbrev coneSum (W : Type w) : TopCat.{max u v w} :=
  TopCat.of (Σ i, TopCat.cone (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization))

/-- The map from the disjoint union of the copied domains into the family cylinder that
includes the `i`-th copied domain through `blockInclusion`. -/
def domainsToCylinder (f : ∀ i, Morphism (P i) Q) :
    domainSum P W ⟶ TopCat.of (cylinderFamily P Q f).Realization :=
  TopCat.ofHom ⟨fun p => blockInclusion P Q f p.1
      ((MappingCylinder.inclusionMorphism (small_domain_le (f p.1))).realization p.2),
    continuous_sigma (fun i => (blockInclusion P Q f i).continuous.comp
      (MappingCylinder.inclusionMorphism (small_domain_le (f i))).realization.continuous)⟩

/-- The inclusion of each copied domain as the base of its topological cone. -/
def domainsToCones : domainSum P W ⟶ coneSum P W :=
  TopCat.ofHom ⟨Sigma.map (id : «I» → «I») (fun i =>
      TopCat.coneBase (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization)),
    Continuous.sigma_map (fun i =>
      (TopCat.coneBase (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization)).hom.continuous)⟩

/-- The actual copied domain maps into its original scalar small-cylinder block. -/
theorem domainsToCylinder_apply (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (x : (MappingCylinder.domainComplex (P i) W).Realization) :
    domainsToCylinder P Q f ⟨i, x⟩ =
      blockInclusion P Q f i
        ((MappingCylinder.inclusionMorphism (small_domain_le (f i))).realization x) := by rfl

/-- The actual map into the family of ordinary cones is the literal cone-base map. -/
theorem domainsToCones_apply (i : «I»)
    (x : (MappingCylinder.domainComplex (P i) W).Realization) :
    domainsToCones P ⟨i, x⟩ =
      (⟨i, TopCat.coneBase (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization) x⟩ :
        coneSum P W) := by rfl

/-- The inclusion of the family cylinder into the family mapping cone, relabelling by
`Sum.inl`. -/
def cylinderToAssociated (f : ∀ i, Morphism (P i) Q) :
    TopCat.of (cylinderFamily P Q f).Realization ⟶ TopCat.of (associatedFamily P Q f).Realization :=
  TopCat.ofHom
    { toFun := fun x => Realization.inclusion
        (le_sup_left : cylinderPart P Q f ≤ associatedFamily P Q f)
        (MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
          (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) x)
      continuous_toFun := (Realization.continuous_inclusion le_sup_left).comp
        (MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
          (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)).continuous }

/-- The family cylinder enters its associated cone by the actual relabeling and inclusion. -/
theorem cylinderToAssociated_apply (f : ∀ i, Morphism (P i) Q)
    (x : (cylinderFamily P Q f).Realization) :
    cylinderToAssociated P Q f x =
      Realization.inclusion
        (show MappingCylinder.relabelComplex (cylinderFamily P Q f)
            (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) ≤
          associatedFamily P Q f from by exact le_sup_left)
        (MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
          (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) x) := by rfl

/-- The actual family-cylinder inclusion into the associated cone is a closed embedding. -/
theorem cylinderToAssociated_isClosedEmbedding (f : ∀ i, Morphism (P i) Q) :
    IsClosedEmbedding (cylinderToAssociated P Q f).hom := by
  change IsClosedEmbedding (fun x : (cylinderFamily P Q f).Realization =>
    Realization.inclusion (le_sup_left : cylinderPart P Q f ≤ associatedFamily P Q f)
      (MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
        (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) x))
  exact (Realization.isClosedEmbedding_inclusion le_sup_left).comp
    (MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
      (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)).isClosedEmbedding

/-- The map from the disjoint union of the topological cones on the copied domains into the
family mapping cone, identifying each cone with its attached block. -/
def conesToAssociated (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) :
    coneSum P W ⟶ TopCat.of (associatedFamily P Q f).Realization :=
  TopCat.ofHom ((⟨PreAbstractSimplicialComplex.Realization.inclusion le_sup_right,
    PreAbstractSimplicialComplex.Realization.continuous_inclusion le_sup_right⟩ :
      C((attachedFamily (W := W) P).Realization, (associatedFamily P Q f).Realization)).comp
        (ordinaryConeSigmaHomeomorph (W := W) P hfinite :
          C((Σ i, TopCat.cone (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization)),
            (attachedFamily (W := W) P).Realization)))

/-- The genuine old copied domains, ordinary cones and actual cylinder-family space form a pushout. -/
theorem ordinaryConeFamily_isPushout (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) :
    IsPushout (domainsToCylinder P Q f) (domainsToCones P)
      (cylinderToAssociated P Q f) (conesToAssociated P Q f hfinite) := by
  let e₁ : domainSum P W ≅ TopCat.of (copiedFamily (W := W) P).Realization :=
    TopCat.isoOfHomeo (copiedSigmaHomeomorph (W := W) P)
  let e₂ : TopCat.of (cylinderFamily P Q f).Realization ≅ TopCat.of (cylinderPart P Q f).Realization :=
    TopCat.isoOfHomeo (show (cylinderFamily P Q f).Realization ≃ₜ (cylinderPart P Q f).Realization from by
      change (cylinderFamily P Q f).Realization ≃ₜ
        (MappingCylinder.relabelComplex (cylinderFamily P Q f)
          (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)).Realization
      exact MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
        (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P))
  let e₃ : coneSum P W ≅ TopCat.of (attachedFamily (W := W) P).Realization :=
    TopCat.isoOfHomeo (ordinaryConeSigmaHomeomorph (W := W) P hfinite)
  refine (associatedFamily_isPushout P Q f).of_iso' e₁ e₂ e₃ (Iso.refl _) ?_ ?_ ?_ ?_
  · apply ConcreteCategory.hom_ext
    rintro ⟨i, x⟩
    change (MappingCylinder.inclusionMorphism (copiedFamily_le_cylinder P Q f)).realization
        (copiedSigmaHomeomorph (W := W) P ⟨i, x⟩) =
      MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
        (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)
        (blockInclusion P Q f i
          ((MappingCylinder.inclusionMorphism (small_domain_le (f i))).realization x))
    apply Realization.ext
    have hb : (blockInclusion P Q f i
        ((MappingCylinder.inclusionMorphism (small_domain_le (f i))).realization x)).point =
        x.point.map (tag (W := W) P i) := by
      simpa only [actualFamilyInclusionPoint] using!
        blockInclusion_point P Q f i
          ((MappingCylinder.inclusionMorphism (small_domain_le (f i))).realization x)
    have hr : ((MappingCylinder.relabelMorphism (cylinderFamily P Q f)
        (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)).realization
        (blockInclusion P Q f i
          ((MappingCylinder.inclusionMorphism (small_domain_le (f i))).realization x))).point =
        x.point.map ((tag (W := W) P i).trans
          (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)) := by
      simpa only [hb, Convexity.StdSimplex.map_map] using!
        MappingCylinder.relabelMorphism_point (cylinderFamily P Q f)
          (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)
          (blockInclusion P Q f i
            ((MappingCylinder.inclusionMorphism (small_domain_le (f i))).realization x))
    have hp := (copiedSigmaHomeomorph_point (W := W) P i x).trans hr.symm
    simpa only [actualFamilyInclusionPoint, ← Homeomorph.coe_toEquiv,
      MappingCylinder.relabelHomeomorph, Equiv.coe_ofBijective,
      Equiv.ofBijective_apply] using! hp
  · apply ConcreteCategory.hom_ext
    rintro ⟨i, x⟩
    change (MappingCylinder.inclusionMorphism (copiedFamily_le_attached (W := W) P)).realization
        (copiedSigmaHomeomorph (W := W) P ⟨i, x⟩) =
      ordinaryConeSigmaHomeomorph (W := W) P hfinite
        ⟨i, TopCat.coneBase (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization) x⟩
    apply Realization.ext
    have hp := congrArg (fun z : (attachedFamily (W := W) P).Realization => z.point)
      (coneSigmaHomeomorph_base (W := W) P hfinite i x).symm
    simpa only [actualFamilyInclusionPoint, Realization.inclusion_point] using! hp
  · apply ConcreteCategory.hom_ext
    intro x
    change (MappingCylinder.inclusionMorphism
        (le_sup_left : cylinderPart P Q f ≤ associatedFamily P Q f)).realization
        (MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
          (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) x) =
      Realization.inclusion (le_sup_left : cylinderPart P Q f ≤ associatedFamily P Q f)
        (MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
          (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) x)
    apply Realization.ext
    simpa only [Realization.inclusion_point] using!
      actualFamilyInclusionPoint
        (le_sup_left : cylinderPart P Q f ≤ associatedFamily P Q f)
        (MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
          (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) x)
  · apply ConcreteCategory.hom_ext
    intro x
    change (MappingCylinder.inclusionMorphism
        (le_sup_right : attachedFamily (W := W) P ≤ associatedFamily P Q f)).realization
        (ordinaryConeSigmaHomeomorph (W := W) P hfinite x) =
      Realization.inclusion (le_sup_right : attachedFamily (W := W) P ≤ associatedFamily P Q f)
        (ordinaryConeSigmaHomeomorph (W := W) P hfinite x)
    apply Realization.ext
    simpa only [Realization.inclusion_point] using!
      actualFamilyInclusionPoint
        (le_sup_right : attachedFamily (W := W) P ≤ associatedFamily P Q f)
        (ordinaryConeSigmaHomeomorph (W := W) P hfinite x)

end ConePushout

namespace ScalarCone

open PreAbstractSimplicialComplex Tagged Cone
open Comparisons ConePushout

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

private theorem scalarAssociated_le (f : ∀ i, Morphism (P i) Q) (i : «I») :
    MappingCylinder.relabelComplex (smallAssociatedCone (f i)) (coneTag (W := W) P i) ≤
      associatedFamily P Q f := by
  intro s hs
  obtain ⟨a, ha, hsa⟩ := hs
  simp only [← Finset.map_eq_image] at hsa
  rw [← hsa]
  rcases ha with hc | ht
  · obtain ⟨b, hb, hba⟩ := hc
    simp only [← Finset.map_eq_image] at hba
    rw [← hba]
    have hblock : b.map (tag (W := W) P i) ∈ cylinderFamily P Q f :=
      block_le_family P Q f i ⟨b, hb, by simp only [← Finset.map_eq_image]⟩
    have hcy : (b.map (tag (W := W) P i)).map
        (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) ∈ cylinderPart P Q f :=
      ⟨b.map (tag (W := W) P i), hblock, by simp only [← Finset.map_eq_image]⟩
    have heq : (b.map (Function.Embedding.inl : Face (P i) ⊕ W ↪
        (Face (P i) ⊕ W) ⊕ PUnit.{max v w + 1})).map (coneTag (W := W) P i) =
      (b.map (tag (W := W) P i)).map
        (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) := by
      rw [Finset.map_map, Finset.map_map]
      rfl
    rw [heq]
    dsimp only [associatedFamily]
    exact Or.inl hcy
  · have hblock : a.map (coneTag (W := W) P i) ∈ attachedBlock (W := W) P i :=
      ⟨a, ht, by simp only [← Finset.map_eq_image]⟩
    have hfamily : a.map (coneTag (W := W) P i) ∈ attachedFamily (W := W) P :=
      (WeakFamilyUnionConstruction46.mem_weakUnion (attachedBlock (W := W) P) _).2
        ⟨i, hblock⟩
    dsimp only [associatedFamily]
    exact Or.inr hfamily

/-- The inclusion of the `i`-th small mapping cone `smallAssociatedCone (f i)` into the family
mapping cone, relabelled by `coneTag`. -/
def scalarAssociatedInclusion (f : ∀ i, Morphism (P i) Q) (i : «I») :
    C((smallAssociatedCone (f i)).Realization, (associatedFamily P Q f).Realization) :=
  (⟨PreAbstractSimplicialComplex.Realization.inclusion (scalarAssociated_le P Q f i),
    PreAbstractSimplicialComplex.Realization.continuous_inclusion (scalarAssociated_le P Q f i)⟩ :
      C((MappingCylinder.relabelComplex (smallAssociatedCone (f i)) (coneTag (W := W) P i)).Realization,
        (associatedFamily P Q f).Realization)).comp
      (MappingCylinder.relabelHomeomorph (smallAssociatedCone (f i)) (coneTag (W := W) P i) :
        C((smallAssociatedCone (f i)).Realization,
          (MappingCylinder.relabelComplex (smallAssociatedCone (f i)) (coneTag (W := W) P i)).Realization))

private theorem scalarAssociated_cylinder (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (x : (smallCylinder (f i)).Realization) :
    scalarAssociatedInclusion P Q f i (smallIntoCone (f i) x) =
      cylinderToAssociated P Q f (blockInclusion P Q f i x) := by
  apply PreAbstractSimplicialComplex.Realization.ext
  change ((MappingCylinder.relabelMorphism (smallAssociatedCone (f i)) (coneTag (W := W) P i)).realization
      (smallIntoCone (f i) x)).point =
    ((MappingCylinder.relabelMorphism (cylinderFamily P Q f) Function.Embedding.inl).realization
      (blockInclusion P Q f i x)).point
  rw [MappingCylinder.relabelMorphism_point, smallIntoCone_point,
    MappingCylinder.relabelMorphism_point, blockInclusion_point,
    Convexity.StdSimplex.map_map, Convexity.StdSimplex.map_map]
  rfl

theorem scalarAssociated_ordinaryCone (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) (i : «I»)
    (x : TopCat.cone (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization)) :
    letI : Finite (Face (P i)) := hfinite i
    conesToAssociated P Q f hfinite ⟨i, x⟩ =
      scalarAssociatedInclusion P Q f i (smallOrdinaryConeAttachment (f i) x) := by
  let := hfinite i
  let := MappingCylinder.finiteFaces_domainComplex (P i) W
  apply PreAbstractSimplicialComplex.Realization.ext
  change ((MappingCylinder.relabelMorphism
    (MappingCylinder.coneComplex (MappingCylinder.domainComplex (P i) W)) (coneTag (W := W) P i)).realization
      (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex (P i) W) x)).point =
    ((MappingCylinder.relabelMorphism (smallAssociatedCone (f i)) (coneTag (W := W) P i)).realization
      (smallOrdinaryConeAttachment (f i) x)).point
  rw [MappingCylinder.relabelMorphism_point, MappingCylinder.relabelMorphism_point]
  have hp := smallOrdinaryConeAttachment_point (f i) x
  exact congrArg (fun q : Convexity.StdSimplex ℝ
      ((Face (P i) ⊕ W) ⊕ PUnit.{max v w + 1}) =>
        q.map (coneTag (W := W) P i)) hp.symm

private theorem ordinaryCone_apex_point (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) (i : «I») :
    (conesToAssociated P Q f hfinite
      ⟨i, TopCat.conePoint (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization)
        (PUnit.unit : PUnit.{max v w + 1})⟩).point =
        Convexity.StdSimplex.single (Sum.inr i : ConeLabels (W := W) P) := by
  let := hfinite i
  let := MappingCylinder.finiteFaces_domainComplex (P i) W
  change ((MappingCylinder.relabelMorphism
    (MappingCylinder.coneComplex (MappingCylinder.domainComplex (P i) W)) (coneTag (W := W) P i)).realization
      (MappingCylinder.ordinaryConeHomeomorph (MappingCylinder.domainComplex (P i) W)
        (TopCat.conePoint (TopCat.of (MappingCylinder.domainComplex (P i) W).Realization)
          (PUnit.unit : PUnit.{max v w + 1})))).point = _
  rw [MappingCylinder.relabelMorphism_point, MappingCylinder.ordinaryConeHomeomorph_apex]
  change (Convexity.StdSimplex.single (Sum.inr (PUnit.unit : PUnit.{max v w + 1}) :
      (Face (P i) ⊕ W) ⊕ PUnit.{max v w + 1})).map (coneTag (W := W) P i) = _
  rw [Convexity.StdSimplex.map_single]
  rfl

theorem scalarAssociated_point (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (x : (smallAssociatedCone (f i)).Realization) :
    (scalarAssociatedInclusion P Q f i x).point = x.point.map (coneTag (W := W) P i) :=
  MappingCylinder.relabelMorphism_point (smallAssociatedCone (f i)) (coneTag (W := W) P i) x

end ScalarCone

namespace Geometry

open PreAbstractSimplicialComplex Tagged Cone
open Comparisons ConePushout

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

theorem cylinderCone_point (f : ∀ i, Morphism (P i) Q) (x : (cylinderFamily P Q f).Realization) :
    (cylinderToAssociated P Q f x).point = x.point.map Function.Embedding.inl := by
  simpa only [cylinderToAssociated, TopCat.ofHom, ConcreteCategory.hom_ofHom,
    ContinuousMap.coe_apply, ContinuousMap.coe_mk,
    Realization.inclusion_point, ← Homeomorph.coe_toEquiv,
    MappingCylinder.relabelHomeomorph, Equiv.coe_ofBijective, Equiv.ofBijective_apply, Equiv.ofBijective_apply] using!
    MappingCylinder.relabelMorphism_point (cylinderFamily P Q f)
      (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P) x


private theorem domainsAssociated_point (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (x : (MappingCylinder.domainComplex (P i) W).Realization) :
    (cylinderToAssociated P Q f (domainsToCylinder P Q f ⟨i, x⟩)).point =
      x.point.map ((tag (W := W) P i).trans (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P))  := by
  have hi : domainsToCylinder P Q f ⟨i, x⟩ =
      blockInclusion P Q f i ((MappingCylinder.inclusionMorphism (small_domain_le (f i))).realization x) := by
    rfl
  have hb : (domainsToCylinder P Q f ⟨i, x⟩).point = x.point.map (tag (W := W) P i) := by
    simpa only [hi, actualFamilyInclusionPoint] using!
      blockInclusion_point P Q f i
        ((MappingCylinder.inclusionMorphism (small_domain_le (f i))).realization x)
  have hc := cylinderCone_point P Q f (domainsToCylinder P Q f ⟨i, x⟩)
  simpa only [hb, Convexity.StdSimplex.map_map] using! hc

private theorem cylinderCone_range_iff (f : ∀ i, Morphism (P i) Q)
    (y : (associatedFamily P Q f).Realization) :
    y ∈ Set.range (cylinderToAssociated P Q f) ↔ y.point.weights.support ∈ cylinderPart P Q f := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [cylinderCone_point]
    have h := ((MappingCylinder.relabelMorphism (cylinderFamily P Q f)
      (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)).realization x).support_mem
    simpa only [MappingCylinder.relabelMorphism_point, cylinderPart] using! h
  · intro hy
    let z : (cylinderPart P Q f).Realization := ⟨y.point, hy⟩
    let h : (cylinderFamily P Q f).Realization ≃ₜ (cylinderPart P Q f).Realization := by
      change (cylinderFamily P Q f).Realization ≃ₜ
        (MappingCylinder.relabelComplex (cylinderFamily P Q f)
          (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)).Realization
      exact MappingCylinder.relabelHomeomorph (cylinderFamily P Q f)
        (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)
    refine ⟨h.symm z, ?_⟩
    apply PreAbstractSimplicialComplex.Realization.ext
    change (h (h.symm z)).point = y.point
    rw [h.apply_symm_apply]

private theorem ordinaryCone_range_iff (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) (i : «I») (y : (associatedFamily P Q f).Realization) :
    y ∈ Set.range (fun x => conesToAssociated P Q f hfinite ⟨i, x⟩) ↔
      y.point.weights.support ∈ attachedBlock (W := W) P i := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (scalarConeHomeomorph (W := W) P i (hfinite i) x).support_mem
  · intro hy
    let z : (attachedBlock (W := W) P i).Realization := ⟨y.point, hy⟩
    let h := scalarConeHomeomorph (W := W) P i (hfinite i)
    refine ⟨h.symm z, ?_⟩
    apply PreAbstractSimplicialComplex.Realization.ext
    change (h (h.symm z)).point = y.point
    rw [h.apply_symm_apply]

private theorem copiedAssociated_range_iff (f : ∀ i, Morphism (P i) Q) (i : «I»)
    (y : (associatedFamily P Q f).Realization) :
    y ∈ Set.range (fun x : (MappingCylinder.domainComplex (P i) W).Realization =>
        cylinderToAssociated P Q f (domainsToCylinder P Q f ⟨i, x⟩)) ↔
      y.point.weights.support ∈ copiedBlock (W := W) P i := by
  constructor
  · rintro ⟨x, rfl⟩
    have h := ((MappingCylinder.relabelMorphism (MappingCylinder.domainComplex (P i) W)
      ((tag (W := W) P i).trans
        (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P))).realization x).support_mem
    have hp := domainsAssociated_point P Q f i x
    simpa only [hp, copiedBlock, MappingCylinder.relabelMorphism_point] using! h
  · intro hy
    let z : (copiedBlock (W := W) P i).Realization := ⟨y.point, hy⟩
    let h := MappingCylinder.relabelHomeomorph (MappingCylinder.domainComplex (P i) W)
      ((tag (W := W) P i).trans (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P))
    refine ⟨h.symm z, ?_⟩
    apply PreAbstractSimplicialComplex.Realization.ext
    rw [domainsAssociated_point]
    calc
      (h.symm z).point.map ((tag (W := W) P i).trans
        (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)) =
        (h (h.symm z)).point :=
        (MappingCylinder.relabelMorphism_point (MappingCylinder.domainComplex (P i) W)
          ((tag (W := W) P i).trans
            (Function.Embedding.inl : Labels (W := W) P ↪ ConeLabels (W := W) P)) (h.symm z)).symm
      _ = z.point := congrArg PreAbstractSimplicialComplex.Realization.point (h.apply_symm_apply z)
      _ = y.point := rfl

private theorem ordinaryCone_cylinder_intersection (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) (i : «I») :
    Set.range (fun x => conesToAssociated P Q f hfinite ⟨i, x⟩) ∩
        Set.range (cylinderToAssociated P Q f) =
      Set.range (fun x : (MappingCylinder.domainComplex (P i) W).Realization =>
        cylinderToAssociated P Q f (domainsToCylinder P Q f ⟨i, x⟩)) := by
  ext y
  rw [Set.mem_inter_iff, ordinaryCone_range_iff P Q f hfinite i,
    cylinderCone_range_iff P Q f, copiedAssociated_range_iff P Q f i]
  rw [← cylinder_attached_intersection P Q f i]
  change (y.point.weights.support ∈ attachedBlock (W := W) P i ∧
    y.point.weights.support ∈ cylinderPart P Q f) ↔
      (y.point.weights.support ∈ cylinderPart P Q f ∧ y.point.weights.support ∈ attachedBlock (W := W) P i)
  exact and_comm

private theorem ordinaryCones_disjoint (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) {i j : «I»} (hij : i ≠ j) :
    Disjoint (Set.range (fun x => conesToAssociated P Q f hfinite ⟨i, x⟩))
      (Set.range (fun x => conesToAssociated P Q f hfinite ⟨j, x⟩)) := by
  rw [Set.disjoint_left]
  intro y hyi hyj
  have hs : y.point.weights.support ∈ attachedBlock (W := W) P i ⊓ attachedBlock (W := W) P j :=
    ⟨(ordinaryCone_range_iff P Q f hfinite i y).mp hyi,
      (ordinaryCone_range_iff P Q f hfinite j y).mp hyj⟩
  rw [attached_disjoint_faces (W := W) P hij] at hs
  exact hs

theorem associatedFamily_cover (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) :
    Set.range (cylinderToAssociated P Q f) ∪
        ⋃ i, Set.range (fun x => conesToAssociated P Q f hfinite ⟨i, x⟩) = Set.univ := by
  ext y
  constructor
  · intro _
    exact Set.mem_univ y
  · intro _
    rcases y.support_mem with hc | ha
    · exact Or.inl ((cylinderCone_range_iff P Q f y).mpr hc)
    · obtain ⟨i, hi⟩ := (WeakFamilyUnionConstruction46.mem_weakUnion (attachedBlock (W := W) P)
        y.point.weights.support).mp ha
      exact Or.inr (Set.mem_iUnion.mpr ⟨i, (ordinaryCone_range_iff P Q f hfinite i y).mpr hi⟩)

end Geometry

/- The dimension-controlled family has uniform face-cardinality bounds and
agrees with the full family on the old target and every copied domain. -/

namespace Bounds

open Tagged
open Retraction Cone

variable {«I» : Type u} {V : «I» → Type v} (P : ∀ i, PreAbstractSimplicialComplex (V i))
variable {W : Type w} (Q : PreAbstractSimplicialComplex W)

theorem cylinderFamily_face_card_le (f : ∀ i, Morphism (P i) Q) (M N : ℕ)
    (hP : ∀ i, ∀ a : Face (P i), a.val.card ≤ M)
    (hQ : ∀ a : Face Q, a.val.card ≤ N) (s : Face (cylinderFamily P Q f)) :
    s.val.card ≤ max (M + 1) N := by
  rcases (cylinderFamily_faces P Q f s.val).mp s.property with ho | ⟨i, hi⟩
  · rcases ho with ⟨a, ha, he⟩
    have hcard := (hQ ⟨a, ha⟩).trans (le_max_right (M + 1) N)
    rw [← he]
    simpa only [← Finset.map_eq_image, Finset.card_map] using hcard
  · rcases hi with ⟨a, ha, he⟩
    have hcard := small_all_face_card_le (f i) M N (hP i) hQ ⟨a, ha⟩
    rw [← he]
    simpa only [← Finset.map_eq_image, Finset.card_map] using hcard

theorem associatedFamily_face_card_le (f : ∀ i, Morphism (P i) Q) (M N : ℕ)
    (hP : ∀ i, ∀ a : Face (P i), a.val.card ≤ M)
    (hQ : ∀ a : Face Q, a.val.card ≤ N) (s : Face (associatedFamily P Q f)) :
    s.val.card ≤ max (M + 1) N := by
  rcases s.property with hc | ht
  · rcases hc with ⟨a, ha, he⟩
    have hcard := cylinderFamily_face_card_le P Q f M N hP hQ ⟨a, ha⟩
    rw [← he]
    simpa only [← Finset.map_eq_image, Finset.card_map] using hcard
  · rcases (WeakFamilyUnionConstruction46.mem_weakUnion (attachedBlock (W := W) P) s.val).mp ht
      with ⟨i, hi⟩
    rcases hi with ⟨a, ha, he⟩
    have hcard := (copiedCone_face_card_le M (hP i) ⟨a, ha⟩).trans (le_max_left (M + 1) N)
    rw [← he]
    simpa only [← Finset.map_eq_image, Finset.card_map] using hcard

theorem familyHomotopy_block (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) (i : «I») (t : unitInterval)
    (x : (smallCylinder (f i)).Realization) :
    letI : Finite (Face (P i)) := hfinite i
    familyHomotopy P Q f hfinite (t, blockInclusion P Q f i x) =
      blockInclusion P Q f i (smallCylinderDeformation (f i) (t, x))  := by
  let : Finite (Face (P i)) := hfinite i
  change curriedFamily P Q f hfinite (blockInclusion P Q f i x) t =
    blockInclusion P Q f i (smallCylinderDeformation (f i) (t, x))
  have hcomponent :
      curriedFamily P Q f hfinite (blockInclusion P Q f i x) t =
        (pieceHomotopy P Q f hfinite (some i)).toContinuousMap
          (t, blockHomeomorph P Q f i x) :=
    curriedFamily_component P Q f hfinite (some i) (blockHomeomorph P Q f i x) t
  have hinverse :
      (blockHomeomorph P Q f i).symm (blockHomeomorph P Q f i x) = x :=
    (blockHomeomorph P Q f i).symm_apply_apply x
  have hprojection :
      (smallCylinderDeformation (f i)).toHomotopy (t, x) =
        smallCylinderDeformation (f i) (t, x) :=
    congrFun (ContinuousMap.HomotopyWith.coe_toHomotopy
      (smallCylinderDeformation (f i))) (t, x)
  have hevaluation :
      (pieceHomotopy P Q f hfinite (some i)).toContinuousMap
          (t, blockHomeomorph P Q f i x) =
        blockInclusion P Q f i (smallCylinderDeformation (f i) (t, x)) := by
    change blockInclusion P Q f i
        ((smallCylinderDeformation (f i)).toHomotopy
          (t, (blockHomeomorph P Q f i).symm (blockHomeomorph P Q f i x))) =
      blockInclusion P Q f i (smallCylinderDeformation (f i) (t, x))
    rw [hinverse]
    exact congrArg (fun y : (smallCylinder (f i)).Realization => blockInclusion P Q f i y)
      hprojection
  exact Eq.trans hcomponent hevaluation

private theorem familyHomotopy_block_face_support (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) (i : «I»)
    (s : Face (smallCylinder (f i))) (t : unitInterval) (q : Convexity.StdSimplex ℝ s.val) :
    (familyHomotopy P Q f hfinite
      (t, blockInclusion P Q f i (Realization.faceMap (smallCylinder (f i)) s q))).point.weights.support ⊆
        (controlHalo (f i) s.val).image (tag (W := W) P i) := by
  let : Finite (Face (P i)) := hfinite i
  rw [familyHomotopy_block, blockInclusion_point, Convexity.StdSimplex.weights_map]
  exact Finsupp.mapDomain_support.trans
    (Finset.image_mono (tag (W := W) P i) (smallCylinderDeformation_face_support (f i) s t q))

private def originalFamilyData (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) : MappingCylinder.FamilyAttachmentData P Q f hfinite :=
  MappingCylinder.familyAttachments P Q f hfinite

private theorem originalFamily_tag (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) (i : «I») :
    (originalFamilyData P Q f hfinite).tag i = tag (W := W) P i := by
  apply Function.Embedding.ext
  intro z
  cases z with
  | inl a => exact (originalFamilyData P Q f hfinite).tag_left i a
  | inr b => exact (originalFamilyData P Q f hfinite).tag_right i b

private theorem cylinderFamily_into_original46 (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) :
    cylinderFamily P Q f ≤ (originalFamilyData P Q f hfinite).cylinder := by
  intro s hs
  apply ((originalFamilyData P Q f hfinite).cylinder_faces s).mpr
  rcases (cylinderFamily_faces P Q f s).mp hs with ho | ⟨i, hi⟩
  · left
    obtain ⟨a, ha, hsa⟩ := ho
    refine ⟨a, ha, ?_⟩
    simpa only [← Finset.map_eq_image] using! hsa
  · apply Or.inr
    refine ⟨i, ?_⟩
    rw [originalFamily_tag P Q f hfinite i]
    rcases hi with ⟨a, ha, rfl⟩
    refine ⟨a, smallCylinder_le (f i) ha, ?_⟩
    simp only [← Finset.map_eq_image]

private def smallFamilyIntoOriginal46 (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) :
    C((cylinderFamily P Q f).Realization, (originalFamilyData P Q f hfinite).cylinder.Realization) :=
  ⟨Realization.inclusion (cylinderFamily_into_original46 P Q f hfinite),
    Realization.continuous_inclusion (cylinderFamily_into_original46 P Q f hfinite)⟩

private theorem smallFamilyIntoOriginal46_closed (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) :
    IsClosedEmbedding (smallFamilyIntoOriginal46 P Q f hfinite) :=
  Realization.isClosedEmbedding_inclusion (cylinderFamily_into_original46 P Q f hfinite)

private theorem smallFamilyIntoOriginal46_old (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) (x : Q.Realization) :
    smallFamilyIntoOriginal46 P Q f hfinite (oldInclusion P Q f x) =
      (originalFamilyData P Q f hfinite).old x := by
  apply Realization.ext
  change (oldInclusion P Q f x).point = _
  rw [oldInclusion_point, (originalFamilyData P Q f hfinite).old_point]

private theorem smallFamilyIntoOriginal46_copied (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) (i : «I»)
    (x : (barycentricSubdivision (P i)).Realization) :
    smallFamilyIntoOriginal46 P Q f hfinite (copiedInclusion P Q f i x) =
      (originalFamilyData P Q f hfinite).copied i x := by
  apply Realization.ext
  change (copiedInclusion P Q f i x).point = _
  rw [copiedInclusion_point, (originalFamilyData P Q f hfinite).copied_point,
    originalFamily_tag P Q f hfinite i]

end Bounds
end PreAbstractSimplicialComplex.MappingCylinder.SmallFamily

end

public section
noncomputable section
open Topology CategoryTheory PreAbstractSimplicialComplex
open scoped Classical
namespace PreAbstractSimplicialComplex.MappingCylinder

/-- Attachment data for a family of maps `f i : P i → Q` built from small mapping cylinders:
the family mapping cylinder and cone, their inclusions, the deformation retraction onto `Q`,
and the two attachment pushout squares. -/
structure SmallFamilyAttachmentData {«I» : Type u} {V : «I» → Type v}
    (P : ∀ i, PreAbstractSimplicialComplex (V i)) {W : Type w}
    (Q : PreAbstractSimplicialComplex W) (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) where
  /-- Embeds the labels of the `i`-th cylinder into the family cylinder labels: a copied face
  `a` goes to `⟨i, a⟩` and an ambient target label is unchanged. -/
  tag : ∀ i, Face (P i) ⊕ W ↪ (Σ j, Face (P j)) ⊕ W
  /-- Labels the apex of the `i`-th cone by `i`. -/
  apexTag : ∀ _ : «I», PUnit.{max v w + 1} ↪ «I»
  tag_left : ∀ i, ∀ a : Face (P i), tag i (Sum.inl a) = Sum.inl ⟨i, a⟩
  tag_right : ∀ i, ∀ a : W, tag i (Sum.inr a) = Sum.inr a
  apex_tag : ∀ i, ∀ p : PUnit.{max v w + 1}, apexTag i p = i
  /-- The family mapping cylinder formed from the old target and the tagged small cylinders. -/
  cylinder : PreAbstractSimplicialComplex ((Σ i, Face (P i)) ⊕ W)
  /-- The family mapping cone: the cylinder together with the cone on each tagged copied
  domain, with apex labelled `i`. -/
  cone : PreAbstractSimplicialComplex (((Σ i, Face (P i)) ⊕ W) ⊕ «I»)
  cylinder_faces : ∀ s, s ∈ cylinder ↔
    s ∈ Q.map (Function.Embedding.inr : W ↪ (Σ i, Face (P i)) ⊕ W) ∨
      ∃ i, s ∈ (SmallCylinder.smallCylinder (f i)).map (tag i)
  cone_faces : ∀ s, s ∈ cone ↔
    s ∈ cylinder.map Function.Embedding.inl ∨
      ∃ i, s ∈ (coneComplex (domainComplex (P i) W)).map
        (Function.Embedding.sumMap (tag i) (apexTag i))
  /-- The inclusion of `Q` into the family cylinder. -/
  old : C(Q.Realization, cylinder.Realization)
  /-- The inclusion of the `i`-th small mapping cylinder into the family cylinder. -/
  block : ∀ i, C((SmallCylinder.smallCylinder (f i)).Realization, cylinder.Realization)
  /-- The inclusion of the `i`-th copied domain, the barycentric subdivision of `P i`. -/
  copied : ∀ i, C((barycentricSubdivision (P i)).Realization, cylinder.Realization)
  old_point : ∀ x, (old x).point = x.point.map (Sum.inr : W → (Σ i, Face (P i)) ⊕ W)
  block_point : ∀ i x, (block i x).point = x.point.map (tag i)
  copied_point : ∀ i x, (copied i x).point =
    (x.point.map (Sum.inl : Face (P i) → Face (P i) ⊕ W)).map (tag i)
  old_closed : IsClosedEmbedding old
  block_closed : ∀ i, IsClosedEmbedding (block i)
  copied_closed : ∀ i, IsClosedEmbedding (copied i)
  block_intersection : ∀ i j, i ≠ j → Set.range (block i) ∩ Set.range (block j) = Set.range old
  copied_old_disjoint : ∀ i, Disjoint (Set.range (copied i)) (Set.range old)
  copied_disjoint : ∀ i j, i ≠ j → Disjoint (Set.range (copied i)) (Set.range (copied j))
  /-- The retraction of the family cylinder onto `Q`; on each block it is that cylinder's
  retraction. -/
  retraction : C(cylinder.Realization, Q.Realization)
  retraction_old : ∀ x, retraction (old x) = x
  retraction_block : ∀ i x, retraction (block i x) = SmallCylinder.smallRetraction (f i) x
  retraction_copied : ∀ i x, retraction (copied i x) = (f i).realization (barycentricHomeomorph (P
    i) x)
  /-- A homotopy from the identity to `old ∘ retraction`, fixing the image of `Q`. -/
  deformation : ContinuousMap.HomotopyRel (ContinuousMap.id cylinder.Realization)
    (old.comp retraction) (Set.range old)
  deformation_fixed : ∀ t : unitInterval, ∀ x, deformation (t, old x) = old x
  /-- On the `i`-th copy of `Q`, the inclusion of `Q` into the `i`-th mapping cylinder; a leg
  of `cylinder_pushout`. -/
  overlapMap : C((Σ _ : «I», ULift.{max u v w} Q.Realization),
    (Σ i, ULift.{max u v w} (SmallCylinder.smallCylinder (f i)).Realization))
  /-- The fold map from the `«I»`-indexed copies of `Q` to `Q`; a leg of `cylinder_pushout`. -/
  overlapFold : C((Σ _ : «I», ULift.{max u v w} Q.Realization), ULift.{max u v w} Q.Realization)
  /-- The map from the disjoint union of the mapping cylinders that is `block i` on the
  `i`-th summand. -/
  blocksMap : C((Σ i, ULift.{max u v w} (SmallCylinder.smallCylinder (f i)).Realization), cylinder.Realization)
  /-- The inclusion `old`, on the universe-lifted realization of `Q`. -/
  oldMap : C(ULift.{max u v w} Q.Realization, cylinder.Realization)
  overlapMap_apply : ∀ i q, overlapMap ⟨i, q⟩ =
    ⟨i, ULift.up (SmallCylinder.smallOldTarget (f i) q.down)⟩
  overlapFold_apply : ∀ i q, overlapFold ⟨i, q⟩ = q
  blocksMap_apply : ∀ i x, blocksMap ⟨i, x⟩ = block i x.down
  oldMap_apply : ∀ x, oldMap x = old x.down
  cylinder_pushout : CategoryTheory.IsPushout (TopCat.ofHom overlapMap) (TopCat.ofHom overlapFold)
    (TopCat.ofHom blocksMap) (TopCat.ofHom oldMap)
  /-- The inclusion of the family cylinder into the family cone. -/
  cylinderCone : C(cylinder.Realization, cone.Realization)
  /-- The map from the disjoint union of the topological cones on the copied domains into the
  family cone, through each `associated i`. -/
  ordinaryCones : C((Σ i, TopCat.cone (TopCat.of (domainComplex (P i) W).Realization)),
    cone.Realization)
  /-- The inclusion of the `i`-th small mapping cone into the family cone. -/
  associated : ∀ i, C((SmallCylinder.smallAssociatedCone (f i)).Realization, cone.Realization)
  cylinderCone_point : ∀ x, (cylinderCone x).point = x.point.map Function.Embedding.inl
  associated_point : ∀ i x, (associated i x).point =
    x.point.map (Function.Embedding.sumMap (tag i) (apexTag i))
  associated_cylinder : ∀ i x, associated i (SmallCylinder.smallIntoCone (f i) x) = cylinderCone
    (block i x)
  ordinaryCones_apply : ∀ i,
    letI : Finite (Face (P i)) := hfinite i
    ∀ x, ordinaryCones ⟨i, x⟩ = associated i (SmallCylinder.smallOrdinaryConeAttachment (f i) x)
  apex_point : ∀ i, (ordinaryCones
    ⟨i, TopCat.conePoint (TopCat.of (domainComplex (P i) W).Realization) PUnit.unit⟩).point =
      Convexity.StdSimplex.single (Sum.inr i : ((Σ i, Face (P i)) ⊕ W) ⊕ «I»)
  /-- The map from the disjoint union of the copied domains into the family cylinder,
  through each `block i`. -/
  domainsCylinder : C((Σ i, (domainComplex (P i) W).Realization), cylinder.Realization)
  /-- The inclusion of each copied domain as the base of its topological cone. -/
  domainsCones : C((Σ i, (domainComplex (P i) W).Realization),
    (Σ i, TopCat.cone (TopCat.of (domainComplex (P i) W).Realization)))
  domainsCylinder_apply : ∀ i x, domainsCylinder ⟨i, x⟩ =
    block i ((inclusionMorphism (SmallCylinder.small_domain_le (f i))).realization x)
  domainsCones_apply : ∀ i x, domainsCones ⟨i, x⟩ =
    ⟨i, TopCat.coneBase (TopCat.of (domainComplex (P i) W).Realization) x⟩
  cone_pushout : CategoryTheory.IsPushout (TopCat.ofHom domainsCylinder) (TopCat.ofHom domainsCones)
    (TopCat.ofHom cylinderCone) (TopCat.ofHom ordinaryCones)
  cone_cylinder_intersection : ∀ i,
    Set.range (fun x => ordinaryCones ⟨i, x⟩) ∩ Set.range cylinderCone =
      Set.range (fun x : (domainComplex (P i) W).Realization => cylinderCone (domainsCylinder ⟨i,
        x⟩))
  cones_disjoint : ∀ i j, i ≠ j →
    Disjoint (Set.range (fun x => ordinaryCones ⟨i, x⟩)) (Set.range (fun x => ordinaryCones ⟨j, x⟩))
  cover : Set.range cylinderCone ∪ ⋃ i, Set.range (fun x => ordinaryCones ⟨i, x⟩) = Set.univ
  empty_family : IsEmpty «I» →
    cylinder = Q.map (Function.Embedding.inr : W ↪ (Σ i, Face (P i)) ⊕ W) ∧
      cone = (Q.map (Function.Embedding.inr : W ↪ (Σ i, Face (P i)) ⊕ W)).map Function.Embedding.inl

/-- The attachment data built in `SmallFamily`. Its `cylinder` is
`SmallFamily.Tagged.cylinderFamily` and its `cone` is `SmallFamily.Cone.associatedFamily`. -/
@[expose] def smallFamilyAttachments {«I» : Type u} {V : «I» → Type v}
    (P : ∀ i, PreAbstractSimplicialComplex (V i)) {W : Type w}
    (Q : PreAbstractSimplicialComplex W) (f : ∀ i, Morphism (P i) Q)
    (hfinite : ∀ i, Finite (Face (P i))) : SmallFamilyAttachmentData P Q f hfinite := by
  refine
    { tag := SmallFamily.Tagged.tag P
      apexTag := fun i => ⟨fun _ => i, by intro _ _ _; exact Subsingleton.elim _ _⟩
      tag_left := by
        exact fun _ _ => rfl
      tag_right := by
        exact fun _ _ => rfl
      apex_tag := by
        exact fun _ _ => rfl
      cylinder := SmallFamily.Tagged.cylinderFamily P Q f
      cone := SmallFamily.Cone.associatedFamily P Q f
      cylinder_faces := by
        intro s
        simpa only [SmallFamily.Tagged.oldTarget,
          SmallFamily.Tagged.block, actualFamilyRelabelComplex_eq_map] using
          SmallFamily.Tagged.cylinderFamily_faces P Q f s
      cone_faces := by
        intro s
        change (s ∈ SmallFamily.Cone.cylinderPart P Q f ∨
          s ∈ SmallFamily.Cone.attachedFamily (W := W) P) ↔ _
        have hmem : s ∈ SmallFamily.Cone.attachedFamily (W := W) P ↔
            ∃ i, s ∈ SmallFamily.Cone.attachedBlock (W := W) P i :=
          WeakFamilyUnionConstruction46.mem_weakUnion
            (SmallFamily.Cone.attachedBlock (W := W) P) s
        rw [hmem]
        simp only [SmallFamily.Cone.cylinderPart,
          SmallFamily.Cone.attachedBlock, SmallFamily.Cone.coneTag,
          SmallFamily.Cone.apexTag, actualFamilyRelabelComplex_eq_map]
      old := SmallFamily.Tagged.oldInclusion P Q f
      block := SmallFamily.Tagged.blockInclusion P Q f
      copied := SmallFamily.Tagged.copiedInclusion P Q f
      old_point := by
        exact SmallFamily.Tagged.oldInclusion_point P Q f
      block_point := by
        exact SmallFamily.Tagged.blockInclusion_point P Q f
      copied_point := by
        exact SmallFamily.Tagged.copiedInclusion_point P Q f
      old_closed := by
        exact SmallFamily.Tagged.oldInclusion_isClosedEmbedding P Q f
      block_closed := by
        exact SmallFamily.Tagged.blockInclusion_isClosedEmbedding P Q f
      copied_closed := by
        exact SmallFamily.Tagged.copiedInclusion_isClosedEmbedding P Q f
      block_intersection := by
        exact fun _ _ hij => SmallFamily.Tagged.blockRange_intersection
          P Q f hij
      copied_old_disjoint := by
        exact SmallFamily.Tagged.copied_old_disjoint P Q f
      copied_disjoint := by
        exact fun _ _ hij => SmallFamily.Tagged.copied_copied_disjoint P Q
          f hij
      retraction := SmallFamily.Retraction.familyRetraction P Q f
      retraction_old := by
        exact SmallFamily.Retraction.familyRetraction_old P Q f
      retraction_block := by
        exact SmallFamily.Retraction.familyRetraction_block P Q f
      retraction_copied := by
        exact SmallFamily.Retraction.familyRetraction_copied P Q f
      deformation := SmallFamily.Retraction.familyHomotopyRelativeOld P Q f hfinite
      deformation_fixed := by
        exact SmallFamily.Retraction.familyHomotopy_old P Q f hfinite
      overlapMap := ⟨Sigma.map (id : «I» → «I») (fun i q =>
        ULift.up (SmallCylinder.smallOldTarget (f i) q.down)), by
          exact Continuous.sigma_map (fun i => continuous_uliftUp.comp
            ((SmallCylinder.smallOldTarget (f i)).continuous.comp continuous_uliftDown))⟩
      overlapFold := ⟨fun p => p.2, by exact continuous_sigma (fun _ => continuous_id)⟩
      blocksMap := ⟨fun p => SmallFamily.Tagged.blockInclusion P Q f p.1 p.2.down, by
        exact continuous_sigma (fun i =>
          (SmallFamily.Tagged.blockInclusion P Q f i).continuous.comp continuous_uliftDown)⟩
      oldMap := ⟨fun q => SmallFamily.Tagged.oldInclusion P Q f q.down, by
        exact (SmallFamily.Tagged.oldInclusion P Q f).continuous.comp continuous_uliftDown⟩
      overlapMap_apply := by
        exact fun _ _ => rfl
      overlapFold_apply := by
        exact fun _ _ => rfl
      blocksMap_apply := by
        exact fun _ _ => rfl
      oldMap_apply := by
        exact fun _ => rfl
      cylinder_pushout := by
        exact SmallFamily.CylinderSpan.actualCylinderFamily_isPushout P Q f
      cylinderCone := (SmallFamily.ConePushout.cylinderToAssociated P Q f).hom
      ordinaryCones := (SmallFamily.ConePushout.conesToAssociated P Q f hfinite).hom
      associated := SmallFamily.ScalarCone.scalarAssociatedInclusion P Q f
      cylinderCone_point := by
        exact SmallFamily.Geometry.cylinderCone_point P Q f
      associated_point := by
        exact SmallFamily.ScalarCone.scalarAssociated_point P Q f
      associated_cylinder := by
        exact SmallFamily.ScalarCone.scalarAssociated_cylinder P Q f
      ordinaryCones_apply := by
        exact SmallFamily.ScalarCone.scalarAssociated_ordinaryCone P
          Q f hfinite
      apex_point := by
        exact SmallFamily.ScalarCone.ordinaryCone_apex_point P Q f hfinite
      domainsCylinder := (SmallFamily.ConePushout.domainsToCylinder P Q f).hom
      domainsCones := (SmallFamily.ConePushout.domainsToCones P).hom
      domainsCylinder_apply := by
        exact fun _ _ => rfl
      domainsCones_apply := by
        exact fun _ _ => rfl
      cone_pushout := by
        exact SmallFamily.ConePushout.ordinaryConeFamily_isPushout P Q f
          hfinite
      cone_cylinder_intersection := by
        exact
          SmallFamily.Geometry.ordinaryCone_cylinder_intersection P Q f hfinite
      cones_disjoint := by
        exact fun _ _ hij => SmallFamily.Geometry.ordinaryCones_disjoint
          P Q f hfinite hij
      cover := by
        exact SmallFamily.Geometry.associatedFamily_cover P Q f hfinite
      empty_family := by
        intro hI
        let := hI
        constructor
        · simpa only [SmallFamily.Tagged.oldTarget,
            actualFamilyRelabelComplex_eq_map] using
            SmallFamily.Tagged.cylinderFamily_empty_index P Q f
        · simpa only [SmallFamily.Cone.cylinderPart,
            SmallFamily.Tagged.cylinderFamily_empty_index,
            SmallFamily.Tagged.oldTarget, actualFamilyRelabelComplex_eq_map] using
            SmallFamily.Comparisons.associatedFamily_empty_index P Q f
    }

end PreAbstractSimplicialComplex.MappingCylinder

end
