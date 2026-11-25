/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.FieldFiniteGaloisNeighborhoods
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGeometricStalkExactness
public import Mathlib.CategoryTheory.Filtered.Final

/-! # The finite Galois section colimit and the original geometric stalk

The finite fields lie inside the prescribed separable closure. The original
étale objects and their arrows are retained; only geometric point indices
and original coefficient sections are lifted to the common universe.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- A pointed original spectrum arrow is the unique inclusion of the same subfields. -/
instance fieldFiniteGaloisNeighborhoodFunctor_full :
    (fieldFiniteGaloisNeighborhoodFunctor k Ω).Full where
  map_surjective {L M} a := by
    let r : Spec (.of M) ⟶ Spec (.of L) := a.unop.hom.left
    have hr : r ≫ Spec.algebraMap k L = Spec.algebraMap k M :=
      MorphismProperty.Over.w a.unop.hom
    let μ : L →ₐ[k] M := Spec.homEquivAlgHom ⟨r, hr⟩
    have hμ : Spec.map (CommRingCat.ofHom μ.toRingHom) = r := by
      change Spec.map (Spec.preimage r) = r
      exact Spec.map_preimage r
    have hz : Spec.algebraMap M Ω ≫ r = Spec.algebraMap L Ω :=
      congrArg (fun z => z.left) a.unop.map_val
    have hring : CommRingCat.ofHom μ.toRingHom ≫
        CommRingCat.ofHom (algebraMap M Ω) = CommRingCat.ofHom (algebraMap L Ω) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hμ]
      exact hz
    have hval (x : L) : (μ x : Ω) = (x : Ω) := by
      exact congrArg
        (fun f : CommRingCat.of L ⟶ CommRingCat.of Ω => f.hom x) hring
    have hLM : L ≤ M := by
      intro x hx
      have h := hval (⟨x, hx⟩ : L)
      change (μ (⟨x, hx⟩ : L)).val = x at h
      exact h ▸ (μ (⟨x, hx⟩ : L)).property
    have hinc : μ = IntermediateField.inclusion hLM := by
      apply AlgHom.ext
      intro x
      apply Subtype.ext
      exact hval x
    refine ⟨homOfLE hLM, ?_⟩
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hLM).toRingHom) = r
    rw [← hinc]
    exact hμ

/-- Finality follows from genuine original refinements and filtered neighborhoods. -/
instance fieldFiniteGaloisNeighborhoodFunctor_final :
    (fieldFiniteGaloisNeighborhoodFunctor k Ω).Final :=
  Functor.final_of_exists_of_isFiltered_of_fullyFaithful
    (fieldFiniteGaloisNeighborhoodFunctor k Ω)
    (fieldFiniteGaloisNeighborhoodFunctor_refines k Ω)

/-- The already constructed equivalence enlarges only the original point indices. -/
abbrev fieldGeometricElementsLiftEquivalence :
    FieldGeometricNeighborhoods k Ω ≌
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.Elements :=
  smallEtaleGeometricElementsLiftEquivalence.{u, w} (Spec.algebraMap k Ω)

/-- Its forward object is the same original neighborhood with its pointing lifted. -/
theorem fieldGeometricElementsLiftEquivalence_obj (a : FieldGeometricNeighborhoods k Ω) :
    (fieldGeometricElementsLiftEquivalence.{u, w} k Ω).functor.obj a =
      Functor.elementsMk _ a.obj (ULift.up a.val) := rfl

/-- Its projection retains all original étale objects and arrows. -/
theorem fieldGeometricElementsLiftEquivalence_comp_projection :
    (fieldGeometricElementsLiftEquivalence.{u, w} k Ω).functor ⋙
        Functor.Elements.π (smallEtaleGeometricPointCommon.{u, w}
          (Spec.algebraMap k Ω)).fiber =
      Functor.Elements.π (fieldGeometricPoint k Ω).fiber := rfl

/-- The same original finite subfields in the actual common point diagram. -/
abbrev fieldFiniteGaloisCommonNeighborhoodFunctor :=
  fieldFiniteGaloisNeighborhoodFunctor k Ω ⋙
    (fieldGeometricElementsLiftEquivalence.{u, w} k Ω).functor.op

instance fieldFiniteGaloisCommonNeighborhoodFunctor_final :
    (fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω).Final := by
  infer_instance

/-- Forget the pointing without changing any original object or restriction arrow. -/
abbrev fieldFiniteGaloisSectionsIndex :=
  fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω ⋙
    (Functor.Elements.π (smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).fiber).op

theorem fieldFiniteGaloisSectionsIndex_original :
    fieldFiniteGaloisSectionsIndex.{u, w} k Ω =
      fieldFiniteGaloisNeighborhoodFunctor k Ω ⋙
        (Functor.Elements.π (fieldGeometricPoint k Ω).fiber).op := rfl

/-- The actual original sections of every literal common-universe sheaf. -/
abbrev fieldFiniteGaloisSectionDiagram
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :=
  fieldFiniteGaloisSectionsIndex.{u, w} k Ω ⋙ Q.obj

theorem fieldFiniteGaloisSectionDiagram_obj
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (L : FiniteGaloisIntermediateField k Ω) :
    (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q).obj L =
      Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L)) := rfl

theorem fieldFiniteGaloisSectionDiagram_map
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    {L M : FiniteGaloisIntermediateField k Ω} (f : L ⟶ M) :
    (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q).map f =
      Q.obj.map (fieldFiniteGaloisInclusion k Ω (leOfHom f)).op := rfl

/-- Existence is derived from the already existing stalk colimit, one sheaf at a time. -/
instance fieldFiniteGaloisSectionDiagram_hasColimit
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    HasColimit (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) :=
  Functor.Final.comp_hasColimit
    (G := (Functor.Elements.π (smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).fiber).op ⋙ Q.obj)
    (fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω)

/-- One fixed additive comparison to the same actual common geometric stalk. -/
def fieldFiniteGaloisStalkIso
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    colimit (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) ≅
      (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).obj Q :=
  Functor.Final.colimitIso
    (fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω)
    ((Functor.Elements.π (smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).fiber).op ⋙ Q.obj)

/-- Every original stage injection goes to precisely its original germ. -/
@[reassoc]
theorem fieldFiniteGaloisStalkIso_ι_hom
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (L : FiniteGaloisIntermediateField k Ω) :
    colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L ≫
        (fieldFiniteGaloisStalkIso.{u, w} k Ω Q).hom =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj :=
  Functor.Final.ι_colimitIso_hom
    (fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω)
    ((Functor.Elements.π (smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).fiber).op ⋙ Q.obj) L

/-- The inverse comparison uses those same original germ injections. -/
@[reassoc]
theorem fieldFiniteGaloisStalkIso_germ_inv
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (L : FiniteGaloisIntermediateField k Ω) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj ≫
        (fieldFiniteGaloisStalkIso.{u, w} k Ω Q).inv =
      colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L :=
  Functor.Final.ι_colimitIso_inv
    (fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω)
    ((Functor.Elements.π (smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).fiber).op ⋙ Q.obj) L

/-- The map is the genuine induced colimit map of every original sheaf component. -/
def fieldFiniteGaloisStalkColimitMap
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q') :
    colimit (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) ⟶
      colimit (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q') :=
  colimMap (Functor.whiskerLeft (fieldFiniteGaloisSectionsIndex.{u, w} k Ω) τ.hom)

/-- This construction is a functor on every literal common-universe sheaf and map. -/
def fieldFiniteGaloisStalkColimit :
    Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} ⥤
      AddCommGrpCat.{max u w} where
  obj Q := colimit (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q)
  map τ := fieldFiniteGaloisStalkColimitMap.{u, w} k Ω τ
  map_id Q := by
    apply colimit.hom_ext
    intro L
    simp [fieldFiniteGaloisStalkColimitMap]
  map_comp τ σ := by
    apply colimit.hom_ext
    intro L
    simp [fieldFiniteGaloisStalkColimitMap, Category.assoc]

/-- The same stage maps commute with the comparison for every sheaf morphism. -/
theorem fieldFiniteGaloisStalkIso_naturality
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q') :
    fieldFiniteGaloisStalkColimitMap.{u, w} k Ω τ ≫
        (fieldFiniteGaloisStalkIso.{u, w} k Ω Q').hom =
      (fieldFiniteGaloisStalkIso.{u, w} k Ω Q).hom ≫
        (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map τ := by
  apply colimit.hom_ext
  intro L
  rw [← Category.assoc, fieldFiniteGaloisStalkColimitMap, ι_colimMap]
  rw [Category.assoc, fieldFiniteGaloisStalkIso_ι_hom]
  rw [← Category.assoc, fieldFiniteGaloisStalkIso_ι_hom]
  exact ((smallEtaleGeometricPointCommon.{u, w}
    (Spec.algebraMap k Ω)).toPresheafFiber_naturality τ.hom _ _).symm

/-- The fixed natural additive isomorphism on the full original common sheaf category. -/
def fieldFiniteGaloisStalkNatIso :
    fieldFiniteGaloisStalkColimit.{u, w} k Ω ≅
      smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω) :=
  NatIso.ofComponents (fieldFiniteGaloisStalkIso.{u, w} k Ω)
    (fieldFiniteGaloisStalkIso_naturality.{u, w} k Ω)

/-- The original coefficient sheaf is lifted once; its original section has its same germ. -/
theorem fieldFiniteGaloisStalkIso_original_section
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (L : FiniteGaloisIntermediateField k Ω)
    (c : F.obj.obj (op (fieldFiniteGaloisEtale k Ω L))) :
    (fieldFiniteGaloisStalkIso.{u, w} k Ω
      ((liftCoefficients.{u, w} (Spec (.of k))).obj F)).hom
      (colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) L (ULift.up c)) =
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
      (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L))
      ((liftCoefficients.{u, w} (Spec (.of k))).obj F).obj (ULift.up c) :=
  ConcreteCategory.congr_hom
    (fieldFiniteGaloisStalkIso_ι_hom.{u, w} k Ω
      ((liftCoefficients.{u, w} (Spec (.of k))).obj F) L) (ULift.up c)

/-- Every original coefficient map uses the same once-lifted natural comparison. -/
theorem fieldFiniteGaloisStalkIso_original_naturality
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (f : F ⟶ F') :
    fieldFiniteGaloisStalkColimitMap.{u, w} k Ω
        ((liftCoefficients.{u, w} (Spec (.of k))).map f) ≫
      (fieldFiniteGaloisStalkIso.{u, w} k Ω
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F')).hom =
    (fieldFiniteGaloisStalkIso.{u, w} k Ω
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F)).hom ≫
      (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map
        ((liftCoefficients.{u, w} (Spec (.of k))).map f) :=
  fieldFiniteGaloisStalkIso_naturality.{u, w} k Ω
    ((liftCoefficients.{u, w} (Spec (.of k))).map f)

/-- Its forward arrows remain the same actual original étale arrows. -/
theorem fieldGeometricElementsLiftEquivalence_map
    {a b : FieldGeometricNeighborhoods k Ω} (f : a ⟶ b) :
    ((fieldGeometricElementsLiftEquivalence.{u, w} k Ω).functor.map f).hom = f.hom := rfl

/-- The finite subfield has its same original pointing in the common diagram. -/
theorem fieldFiniteGaloisCommonNeighborhoodFunctor_obj
    (L : FiniteGaloisIntermediateField k Ω) :
    (fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω).obj L =
      op (Functor.elementsMk
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L))) := rfl

/-- Every common pointed arrow is the same original subfield restriction arrow. -/
theorem fieldFiniteGaloisCommonNeighborhoodFunctor_map
    {L M : FiniteGaloisIntermediateField k Ω} (f : L ⟶ M) :
    ((fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω).map f).unop.hom =
      fieldFiniteGaloisInclusion k Ω (leOfHom f) := rfl

/-- The fixed comparison is an actual additive equivalence of the original section colimit. -/
def fieldFiniteGaloisStalkAddEquiv
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (colimit (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) :
      AddCommGrpCat.{max u w}) ≃+
      (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).obj Q :=
  (fieldFiniteGaloisStalkIso.{u, w} k Ω Q).addCommGroupIsoToAddEquiv

/-- Every original common-coefficient section is sent to its actual geometric germ. -/
theorem fieldFiniteGaloisStalkAddEquiv_ι
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (L : FiniteGaloisIntermediateField k Ω)
    (c : Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L))) :
    fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q
      (colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L c) =
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
      (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj c :=
  ConcreteCategory.congr_hom (fieldFiniteGaloisStalkIso_ι_hom.{u, w} k Ω Q L) c

/-- Its inverse recovers the original injection of every such germ. -/
theorem fieldFiniteGaloisStalkAddEquiv_germ
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (L : FiniteGaloisIntermediateField k Ω)
    (c : Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L))) :
    (fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q).symm
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj c) =
    colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L c :=
  ConcreteCategory.congr_hom (fieldFiniteGaloisStalkIso_germ_inv.{u, w} k Ω Q L) c

/-- Each colimit stage map is the actual original sheaf component. -/
@[reassoc]
theorem fieldFiniteGaloisStalkColimitMap_ι
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q')
    (L : FiniteGaloisIntermediateField k Ω) :
    colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L ≫
        fieldFiniteGaloisStalkColimitMap.{u, w} k Ω τ =
      τ.hom.app (op (fieldFiniteGaloisEtale k Ω L)) ≫
        colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q') L :=
  ι_colimMap (Functor.whiskerLeft (fieldFiniteGaloisSectionsIndex.{u, w} k Ω) τ.hom) L

/-- All sheaf maps commute with the same additive comparison on every colimit element. -/
theorem fieldFiniteGaloisStalkAddEquiv_naturality
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q')
    (c : (colimit (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) :
      AddCommGrpCat.{max u w})) :
    fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q'
        (fieldFiniteGaloisStalkColimitMap.{u, w} k Ω τ c) =
      (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map τ
        (fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q c) :=
  ConcreteCategory.congr_hom (fieldFiniteGaloisStalkIso_naturality.{u, w} k Ω τ) c

/-- The same original map after one coefficient lift acts literally on its original stage. -/
theorem fieldFiniteGaloisStalkColimitMap_original_ι
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (f : F ⟶ F')
    (L : FiniteGaloisIntermediateField k Ω)
    (c : F.obj.obj (op (fieldFiniteGaloisEtale k Ω L))) :
    fieldFiniteGaloisStalkColimitMap.{u, w} k Ω
        ((liftCoefficients.{u, w} (Spec (.of k))).map f)
        (colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) L (ULift.up c)) =
      colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F')) L
        (ULift.up (f.hom.app (op (fieldFiniteGaloisEtale k Ω L)) c)) :=
  ConcreteCategory.congr_hom (fieldFiniteGaloisStalkColimitMap_ι.{u, w} k Ω
    ((liftCoefficients.{u, w} (Spec (.of k))).map f) L) (ULift.up c)

/-- All original and common indexing coordinates, and internally derived colimit existence. -/
def FieldFiniteGaloisColimitLaws : Prop :=
  (fieldFiniteGaloisNeighborhoodFunctor k Ω).Full ∧
  (fieldFiniteGaloisNeighborhoodFunctor k Ω).Faithful ∧
  (fieldFiniteGaloisNeighborhoodFunctor k Ω).Final ∧
  (∀ a : FieldGeometricNeighborhoods k Ω,
    (fieldGeometricElementsLiftEquivalence.{u, w} k Ω).functor.obj a =
      Functor.elementsMk _ a.obj (ULift.up a.val)) ∧
  (∀ (a b : FieldGeometricNeighborhoods k Ω) (f : a ⟶ b),
    ((fieldGeometricElementsLiftEquivalence.{u, w} k Ω).functor.map f).hom = f.hom) ∧
  (fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω).Final ∧
  (∀ L : FiniteGaloisIntermediateField k Ω,
    (fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω).obj L =
      op (Functor.elementsMk
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)))) ∧
  (∀ (L M : FiniteGaloisIntermediateField k Ω) (f : L ⟶ M),
    ((fieldFiniteGaloisCommonNeighborhoodFunctor.{u, w} k Ω).map f).unop.hom =
      fieldFiniteGaloisInclusion k Ω (leOfHom f)) ∧
  fieldFiniteGaloisSectionsIndex.{u, w} k Ω =
    fieldFiniteGaloisNeighborhoodFunctor k Ω ⋙
      (Functor.Elements.π (fieldGeometricPoint k Ω).fiber).op ∧
  (∀ Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w},
    HasColimit (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q)) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (L : FiniteGaloisIntermediateField k Ω),
    (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q).obj L =
      Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L))) ∧
  ∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (L M : FiniteGaloisIntermediateField k Ω) (f : L ⟶ M),
    (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q).map f =
      Q.obj.map (fieldFiniteGaloisInclusion k Ω (leOfHom f)).op

/-- The one fixed additive natural comparison retains all original germs and all maps. -/
def FieldFiniteGaloisStalkLaws : Prop :=
  let C := fieldFiniteGaloisStalkColimit.{u, w} k Ω
  let S := smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)
  let E := fieldFiniteGaloisStalkNatIso.{u, w} k Ω
  let Lc := liftCoefficients.{u, w} (Spec (.of k))
  (∀ Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w},
    E.app Q = fieldFiniteGaloisStalkIso.{u, w} k Ω Q) ∧
  (∀ Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w},
    C.map (𝟙 Q) = 𝟙 (C.obj Q)) ∧
  (∀ (Q Q' Q'' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (τ : Q ⟶ Q') (σ : Q' ⟶ Q''), C.map (τ ≫ σ) = C.map τ ≫ C.map σ) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (L : FiniteGaloisIntermediateField k Ω)
      (c : Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L))),
    fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q
        (colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L c) =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj c) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (L : FiniteGaloisIntermediateField k Ω)
      (c : Q.obj.obj (op (fieldFiniteGaloisEtale k Ω L))),
    (fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q).symm
        ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
          (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj c) =
      colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L c) ∧
  (∀ (Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (τ : Q ⟶ Q') (L : FiniteGaloisIntermediateField k Ω),
    colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) L ≫ C.map τ =
      τ.hom.app (op (fieldFiniteGaloisEtale k Ω L)) ≫
        colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q') L) ∧
  (∀ (Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (τ : Q ⟶ Q') (c : (colimit (fieldFiniteGaloisSectionDiagram.{u, w} k Ω Q) :
      AddCommGrpCat.{max u w})),
    fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q' (C.map τ c) =
      S.map τ (fieldFiniteGaloisStalkAddEquiv.{u, w} k Ω Q c)) ∧
  (∀ (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
      (L : FiniteGaloisIntermediateField k Ω)
      (c : F.obj.obj (op (fieldFiniteGaloisEtale k Ω L))),
    E.hom.app (Lc.obj F)
        (colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω (Lc.obj F)) L (ULift.up c)) =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L))
        (Lc.obj F).obj (ULift.up c)) ∧
  (∀ (F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}) (f : F ⟶ F'),
    C.map (Lc.map f) ≫ E.hom.app (Lc.obj F') =
      E.hom.app (Lc.obj F) ≫ S.map (Lc.map f)) ∧
  ∀ (F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}) (f : F ⟶ F')
      (L : FiniteGaloisIntermediateField k Ω)
      (c : F.obj.obj (op (fieldFiniteGaloisEtale k Ω L))),
    C.map (Lc.map f)
        (colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω (Lc.obj F)) L (ULift.up c)) =
      colimit.ι (fieldFiniteGaloisSectionDiagram.{u, w} k Ω (Lc.obj F')) L
        (ULift.up (f.hom.app (op (fieldFiniteGaloisEtale k Ω L)) c))

/-- Full finality, colimit existence and the one natural additive stalk comparison,
including every original coefficient sheaf after exactly one canonical lift. -/
theorem original_field_finite_galois_stalk_colimit :
    FieldFiniteGaloisColimitLaws.{u, w} k Ω ∧ FieldFiniteGaloisStalkLaws.{u, w} k Ω := by
  refine ⟨?_, ?_⟩
  · refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_, inferInstance,
      ?_, ?_, fieldFiniteGaloisSectionsIndex_original.{u, w} k Ω, ?_, ?_, ?_⟩
    · exact fieldGeometricElementsLiftEquivalence_obj.{u, w} k Ω
    · intro a b f
      exact fieldGeometricElementsLiftEquivalence_map.{u, w} k Ω f
    · exact fieldFiniteGaloisCommonNeighborhoodFunctor_obj.{u, w} k Ω
    · intro L M f
      exact fieldFiniteGaloisCommonNeighborhoodFunctor_map.{u, w} k Ω f
    · intro Q
      infer_instance
    · exact fieldFiniteGaloisSectionDiagram_obj.{u, w} k Ω
    · intro Q L M f
      exact fieldFiniteGaloisSectionDiagram_map.{u, w} k Ω Q f
  · refine ⟨fun _ => rfl,
      (fieldFiniteGaloisStalkColimit.{u, w} k Ω).map_id,
      (fun _ _ _ τ σ => (fieldFiniteGaloisStalkColimit.{u, w} k Ω).map_comp τ σ),
      fieldFiniteGaloisStalkAddEquiv_ι.{u, w} k Ω,
      fieldFiniteGaloisStalkAddEquiv_germ.{u, w} k Ω,
      (fun _ _ τ L => fieldFiniteGaloisStalkColimitMap_ι.{u, w} k Ω τ L),
      (fun _ _ τ c => fieldFiniteGaloisStalkAddEquiv_naturality.{u, w} k Ω τ c),
      fieldFiniteGaloisStalkIso_original_section.{u, w} k Ω,
      (fun _ _ f => fieldFiniteGaloisStalkIso_original_naturality.{u, w} k Ω f),
      (fun _ _ f L c => fieldFiniteGaloisStalkColimitMap_original_ι.{u, w} k Ω f L c)⟩

end AlgebraicGeometry.Scheme.DerivedSections
