/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.NDR
public import MathlibExt.Topology.Category.TopCat.QuotientPushout
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbedding
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Controlled deformation on an actual attached-space pushout

Given controlled NDR data on the original embedded pair and an arbitrary
attaching map into `X`, the canonical pushout inclusion of `X` carries
constructed controlled NDR data. The control is zero on `X`, and the endpoint
and homotopy are the identity there. On the other pushout leg they are the
original control, endpoint and deformation. Compatibility follows from the
original deformation being fixed on the attaching boundary.

No nonemptiness or separation condition on `X` is required. In particular,
the construction applies to the literal pair of an empty cell family.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Topology
open scoped unitInterval

universe u

namespace TopPair.NDRPushout

variable (P : TopPair.{u}) {X : TopCat.{u}} (a : P.snd ⟶ X)

/-- The actual canonical pushout of the original pair inclusion and attaching map. -/
def space : TopCat.{u} :=
  pushout P.map a

/-- The actual map from the original ambient pair space into the pushout. -/
def left : P.fst ⟶ space P a :=
  pushout.inl P.map a

/-- The actual inclusion of the original target of the attaching map. -/
def inclusion : X ⟶ space P a :=
  pushout.inr P.map a

theorem isPushout : IsPushout P.map a (left P a) (inclusion P a) :=
  IsPushout.of_hasPushout _ _

/-- The actual boundary gluing equality, evaluated at an original boundary point. -/
theorem gluing (b : P.snd) : left P a (P.map b) = inclusion P a (a b) :=
  ConcreteCategory.congr_hom (isPushout P a).w b

/-- Every pushout point comes from one of the two original spaces. -/
theorem exists_left_or_inclusion (y : space P a) :
    (∃ b : P.fst, left P a b = y) ∨ (∃ x : X, inclusion P a x = y) := by
  exact Types.eq_or_eq_of_isPushout ((isPushout P a).map (forget TopCat)) y

variable (d : NDRData P)

include d in
/-- Controlled data makes the original pair inclusion a closed embedding. -/
theorem pair_map_isClosedEmbedding : IsClosedEmbedding P.map :=
  ⟨P.isEmbedding_map, d.isClosed_range⟩

include d in
/-- The actual original-space pushout inclusion is a closed embedding. -/
theorem inclusion_isClosedEmbedding : IsClosedEmbedding (inclusion P a) :=
  TopCat.isClosedEmbedding_of_isPushout (isPushout P a)
    (pair_map_isClosedEmbedding P d)

/-- The pair formed by the actual original-space inclusion into the pushout. -/
def pair : TopPair.{u} :=
  TopPair.of (inclusion P a) (inclusion_isClosedEmbedding P a d).toIsEmbedding

/-- The original control, lifted only to place its codomain in the common universe. -/
def leftControl : P.fst ⟶ TopCat.I.{u} :=
  TopCat.ofHom
    ((TopCat.I.homeomorph.symm : C(unitInterval, TopCat.I.{u})).comp d.control)

/-- The control is identically zero on the original target space. -/
def sourceControl : X ⟶ TopCat.I.{u} :=
  TopCat.ofHom (ContinuousMap.const X (TopCat.I.homeomorph.{u}.symm 0))

theorem control_compatible :
    P.map ≫ leftControl P d = a ≫ sourceControl (X := X) := by
  apply TopCat.ext
  intro b
  change TopCat.I.homeomorph.{u}.symm (d.control (P.map b)) =
    TopCat.I.homeomorph.{u}.symm 0
  rw [(d.control_eq_zero_iff (P.map b)).mpr ⟨b, rfl⟩]

/-- The genuine descended control morphism into the lifted interval. -/
def controlHom : space P a ⟶ TopCat.I.{u} :=
  pushout.desc (leftControl P d) (sourceControl (X := X)) (control_compatible P a d)

/-- The constructed continuous control on the actual pushout. -/
def control : C(space P a, unitInterval) :=
  (TopCat.I.homeomorph : C(TopCat.I.{u}, unitInterval)).comp (controlHom P a d).hom

/-- The constructed control recovers the original control on the ambient leg. -/
theorem control_left (b : P.fst) : control P a d (left P a b) = d.control b := by
  have h : left P a ≫ controlHom P a d = leftControl P d :=
    pushout.inl_desc _ _ _
  have hb := ConcreteCategory.congr_hom h b
  change controlHom P a d (left P a b) =
    TopCat.I.homeomorph.{u}.symm (d.control b) at hb
  change TopCat.I.homeomorph.{u} (controlHom P a d (left P a b)) = d.control b
  exact (congrArg TopCat.I.homeomorph.{u} hb).trans
    (TopCat.I.homeomorph.{u}.apply_symm_apply (d.control b))

/-- The constructed control vanishes at every original-space point. -/
theorem control_inclusion (x : X) : control P a d (inclusion P a x) = 0 := by
  have h : inclusion P a ≫ controlHom P a d = sourceControl (X := X) :=
    pushout.inr_desc _ _ _
  have hx := ConcreteCategory.congr_hom h x
  change controlHom P a d (inclusion P a x) = TopCat.I.homeomorph.{u}.symm 0 at hx
  change TopCat.I.homeomorph.{u} (controlHom P a d (inclusion P a x)) = 0
  exact (congrArg TopCat.I.homeomorph.{u} hx).trans
    (TopCat.I.homeomorph.{u}.apply_symm_apply 0)

/-- The original endpoint fixes each original embedded boundary point. -/
theorem endpoint_boundary (b : P.snd) : d.endpoint (P.map b) = P.map b :=
  (d.deformation.fst_eq_snd ⟨b, rfl⟩).symm

/-- The endpoint on the ambient leg is the original endpoint followed by its actual inclusion. -/
def leftEndpoint : P.fst ⟶ space P a :=
  TopCat.ofHom d.endpoint ≫ left P a

theorem endpoint_compatible :
    P.map ≫ leftEndpoint P a d = a ≫ inclusion P a := by
  apply TopCat.ext
  intro b
  change left P a (d.endpoint (P.map b)) = inclusion P a (a b)
  rw [endpoint_boundary P d b]
  exact gluing P a b

/-- The constructed endpoint on the actual pushout, identical on the original space. -/
def endpoint : space P a ⟶ space P a :=
  pushout.desc (leftEndpoint P a d) (inclusion P a) (endpoint_compatible P a d)

theorem endpoint_left (b : P.fst) :
    endpoint P a d (left P a b) = left P a (d.endpoint b) := by
  exact ConcreteCategory.congr_hom (pushout.inl_desc
    (leftEndpoint P a d) (inclusion P a) (endpoint_compatible P a d)) b

theorem endpoint_inclusion (x : X) :
    endpoint P a d (inclusion P a x) = inclusion P a x := by
  exact ConcreteCategory.congr_hom (pushout.inr_desc
    (leftEndpoint P a d) (inclusion P a) (endpoint_compatible P a d)) x

/-- The original global deformation, followed by the actual ambient-leg map. -/
def leftDeformation : TopCat.Homotopy (left P a) (leftEndpoint P a d) :=
  (d.deformation.compContinuousMap (left P a).hom).toHomotopy.cast
    (ContinuousMap.comp_id _) (by
      simp only [leftEndpoint, TopCat.hom_comp, TopCat.hom_ofHom])

/-- The two actual leg homotopies agree throughout the attaching boundary. -/
theorem deformation_compatible (t : unitInterval) (b : P.snd) :
    leftDeformation P a d (t, P.map b) =
      TopCat.Homotopy.refl (inclusion P a) (t, a b) := by
  change left P a (d.deformation (t, P.map b)) = inclusion P a (a b)
  rw [d.deformation.eq_fst t ⟨b, rfl⟩]
  exact gluing P a b

/-- Descending the two original inclusion maps recovers the actual pushout identity. -/
theorem desc_identity :
    pushout.desc (left P a) (inclusion P a) (isPushout P a).w = 𝟙 (space P a) :=
  pushout.desc_inl_inr P.map a

/-- The actual compatible pushout homotopy, before recording its fixed locus. -/
def descDeformation :
    TopCat.Homotopy
      (pushout.desc (left P a) (inclusion P a) (isPushout P a).w)
      (endpoint P a d) :=
  TopCat.Homotopy.pushoutDesc (leftDeformation P a d)
    (TopCat.Homotopy.refl (inclusion P a))
    (isPushout P a).w (endpoint_compatible P a d) (deformation_compatible P a d)

/-- The constructed global deformation, fixed on the entire original-space image. -/
def deformation :
    ContinuousMap.HomotopyRel (ContinuousMap.id (space P a)) (endpoint P a d).hom
      (Set.range (inclusion P a)) where
  toFun := descDeformation P a d
  continuous_toFun := by
    exact (descDeformation P a d).continuous
  map_zero_left y := by
    exact ((descDeformation P a d).apply_zero y).trans
      (ConcreteCategory.congr_hom (desc_identity P a) y)
  map_one_left y := by
    exact (descDeformation P a d).apply_one y
  prop' t y hy := by
    rcases hy with ⟨x, rfl⟩
    change descDeformation P a d (t, inclusion P a x) = inclusion P a x
    exact TopCat.Homotopy.pushoutDesc_apply_inr (leftDeformation P a d)
      (TopCat.Homotopy.refl (inclusion P a))
      (isPushout P a).w (endpoint_compatible P a d) (deformation_compatible P a d) t x

/-- On the ambient leg, the constructed deformation is the original deformation. -/
theorem deformation_left (t : unitInterval) (b : P.fst) :
    deformation P a d (t, left P a b) = left P a (d.deformation (t, b)) := by
  change descDeformation P a d (t, left P a b) = left P a (d.deformation (t, b))
  exact TopCat.Homotopy.pushoutDesc_apply_inl (leftDeformation P a d)
    (TopCat.Homotopy.refl (inclusion P a))
    (isPushout P a).w (endpoint_compatible P a d) (deformation_compatible P a d) t b

/-- The constructed deformation fixes every original-space point at every time. -/
theorem deformation_inclusion (t : unitInterval) (x : X) :
    deformation P a d (t, inclusion P a x) = inclusion P a x :=
  (deformation P a d).eq_fst t ⟨x, rfl⟩

/-- The constructed control vanishes precisely on the original-space image. -/
theorem control_eq_zero_iff (y : space P a) :
    control P a d y = 0 ↔ y ∈ Set.range (inclusion P a) := by
  constructor
  · intro hy
    rcases exists_left_or_inclusion P a y with ⟨b, rfl⟩ | ⟨x, rfl⟩
    · rw [control_left] at hy
      obtain ⟨q, hq⟩ := (d.control_eq_zero_iff b).mp hy
      exact ⟨a q, (gluing P a q).symm.trans (congrArg (left P a) hq)⟩
    · exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact control_inclusion P a d x

/-- Control nonincrease descends from the actual source deformation. -/
theorem control_deformation_le (t : unitInterval) (y : space P a) :
    control P a d (deformation P a d (t, y)) ≤ control P a d y := by
  rcases exists_left_or_inclusion P a y with ⟨b, rfl⟩ | ⟨x, rfl⟩
  · simpa only [deformation_left, control_left] using d.control_deformation_le t b
  · simpa only [deformation_inclusion, control_inclusion] using (le_refl (0 : unitInterval))

/-- The endpoint reaches the original space wherever the descended control is less than one. -/
theorem endpoint_mem_range (y : space P a) (hy : control P a d y < 1) :
    endpoint P a d y ∈ Set.range (inclusion P a) := by
  rcases exists_left_or_inclusion P a y with ⟨b, rfl⟩ | ⟨x, rfl⟩
  · rw [control_left] at hy
    obtain ⟨q, hq⟩ := d.endpoint_mem_range b hy
    refine ⟨a q, ?_⟩
    exact (gluing P a q).symm.trans
      ((congrArg (left P a) hq).trans (endpoint_left P a d b).symm)
  · exact ⟨x, (endpoint_inclusion P a d x).symm⟩

/-- Constructed controlled NDR data for the actual original-space pushout inclusion. -/
def data : NDRData (pair P a d) where
  control := control P a d
  endpoint := (endpoint P a d).hom
  deformation := deformation P a d
  control_eq_zero_iff := by
    exact control_eq_zero_iff P a d
  control_deformation_le := by
    exact control_deformation_le P a d
  endpoint_mem_range := by
    exact endpoint_mem_range P a d

/-- The original-space preimage of the constructed controlled neighborhood is the whole space. -/
theorem inclusion_preimage_neighborhood :
    inclusion P a ⁻¹' (data P a d).neighborhood = Set.univ := by
  ext x
  change control P a d (inclusion P a x) < 1 ↔ x ∈ (Set.univ : Set X)
  rw [control_inclusion]
  simp only [zero_lt_one, Set.mem_univ]

/-- The ambient-leg preimage of the constructed neighborhood is the original controlled collar. -/
theorem left_preimage_neighborhood :
    left P a ⁻¹' (data P a d).neighborhood = d.neighborhood := by
  ext b
  change control P a d (left P a b) < 1 ↔ d.control b < 1
  rw [control_left]

/-- The constructed neighborhood is the whole original space together with
the actual source collars. -/
theorem neighborhood_eq_range_union_image :
    (data P a d).neighborhood =
      Set.range (inclusion P a) ∪ left P a '' d.neighborhood := by
  ext y
  constructor
  · intro hy
    rcases exists_left_or_inclusion P a y with ⟨b, rfl⟩ | ⟨x, rfl⟩
    · right
      refine ⟨b, ?_, rfl⟩
      change d.control b < 1
      change control P a d (left P a b) < 1 at hy
      rwa [control_left] at hy
    · exact Or.inl ⟨x, rfl⟩
  · rintro (⟨x, rfl⟩ | ⟨b, hb, rfl⟩)
    · change control P a d (inclusion P a x) < 1
      rw [control_inclusion]
      exact zero_lt_one
    · change control P a d (left P a b) < 1
      rw [control_left]
      exact hb

/-- The original-space section into the constructed controlled neighborhood. -/
def sourceSection : X ⟶ TopCat.of (data P a d).neighborhood :=
  TopPair.neighborhoodInclusion (pair P a d) (data P a d).neighborhood
    (data P a d).range_subset_neighborhood

/-- The constructed neighborhood retraction is exactly the identity after the original section. -/
theorem sourceSection_comp_retraction :
    sourceSection P a d ≫ (data P a d).retraction = 𝟙 X := by
  apply TopCat.ext
  intro x
  apply (inclusion_isClosedEmbedding P a d).injective
  have hm := (data P a d).map_retraction (sourceSection P a d x)
  change inclusion P a ((data P a d).retraction (sourceSection P a d x)) =
    endpoint P a d (inclusion P a x) at hm
  exact hm.trans (endpoint_inclusion P a d x)

end TopPair.NDRPushout

end

end
