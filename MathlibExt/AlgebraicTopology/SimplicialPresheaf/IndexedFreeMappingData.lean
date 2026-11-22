/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.DiagramScalarAdjunctions
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerEnrichment
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Whiskering

/-!
# Mapping-space adjunctions for indexed free simplicial diagrams

For a working-small, locally small indexing category, the free row functor is left adjoint to
row evaluation, and mapping out of a free simplicial space is naturally isomorphic to the
designated mapping space of the evaluated row. The comparisons preserve scalar tensor
transposes, endpoint and index actions, end projections and simplicial operators, and identify
the corresponding realization-weak precomposition tests.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped SimplicialSpace.Inner MonoidalClosed Simplicial

namespace SimplicialPresheaf.IndexedFreeMapping

-- Only this module's actual raw-end proofs opt into the explicit plain-end constructor.
-- Under-category end operations use the separately constructed public adjunctions.
attribute [local instance] SimplicialPresheaf.hasEnd

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original designated tensor retains its actual raw pair in every degree. -/
def designatedTensorIso (A : SimplicialSpace.{u}) :
    scalarTensor.obj A.diagram ⋙ SimplicialSpace.ofSimplicialObject ≅
      SimplicialSpace.innerTensorBifunctor.obj A :=
  NatIso.ofComponents (fun _ => InducedCategory.isoMk (Iso.refl _)) (by
    intro K L k
    apply InducedCategory.hom_ext
    apply NatTrans.ext
    funext m
    rfl)

set_option backward.isDefEq.respectTransparency false in
private def rawEndAdjunction (A : SimplicialSpace.{u}) :
    SimplicialSpace.innerTensorBifunctor.obj A ⊣
      SimplicialSpace.forget ⋙ innerHomFunctor.obj (op A.diagram) :=
  ((scalarTensorHomAdjunction A.diagram).comp
    SimplicialSpace.equivalenceSimplicialObject.symm.toAdjunction).ofNatIsoLeft
      (designatedTensorIso A)

set_option backward.isDefEq.respectTransparency false in
/-- The actual chosen and raw ends represent the same original designated tensor. -/
def rawEndNatIso (A : SimplicialSpace.{u}) :
    SimplicialSpace.forget ⋙ innerHomFunctor.obj (op A.diagram) ≅
      SimplicialSpace.innerHomFunctor.obj (op A) :=
  (rawEndAdjunction A).rightAdjointUniq
    (SimplicialSpace.innerTensorHomAdjunction₂.adj A)

set_option backward.isDefEq.respectTransparency false in
/-- The comparison at the original stored source and target diagrams. -/
abbrev rawEndIso (A B : SimplicialSpace.{u}) :
    innerHom A.diagram B.diagram ≅
      (SimplicialSpace.innerHomFunctor.obj (op A)).obj B :=
  (rawEndNatIso A).app B

set_option backward.isDefEq.respectTransparency false in
/-- Both original tensor transposes are retained for every scalar, not just vertices. -/
theorem rawEnd_transpose_laws (A B : SimplicialSpace.{u}) (K : SSet.{u}) :
    let a₀ := ((scalarTensorHomAdjunction A.diagram).comp
      SimplicialSpace.equivalenceSimplicialObject.symm.toAdjunction).ofNatIsoLeft
        (designatedTensorIso A)
    let a₁ := SimplicialSpace.innerTensorHomAdjunction₂.adj A
    (∀ g : K ⟶ innerHom A.diagram B.diagram,
      (a₁.homEquiv K B).symm (g ≫ (rawEndIso A B).hom) =
        (a₀.homEquiv K B).symm g) ∧
    (∀ h : K ⟶ (SimplicialSpace.innerHomFunctor.obj (op A)).obj B,
      (a₀.homEquiv K B).symm (h ≫ (rawEndIso A B).inv) =
        (a₁.homEquiv K B).symm h) := by
  let a₀ := rawEndAdjunction A
  let a₁ := SimplicialSpace.innerTensorHomAdjunction₂.adj A
  have hf (g : K ⟶ innerHom A.diagram B.diagram) :
      (a₁.homEquiv K B).symm (g ≫ (rawEndIso A B).hom) =
        (a₀.homEquiv K B).symm g := by
    change (a₁.homEquiv K B).symm
      (g ≫ (a₀.rightAdjointUniq a₁).hom.app B) = _
    rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
      Adjunction.rightAdjointUniq_hom_app_counit, Adjunction.homEquiv_counit]
  refine ⟨hf, ?_⟩
  intro h
  have h0 := hf (h ≫ (rawEndIso A B).inv)
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h0
  exact h0.symm

set_option backward.isDefEq.respectTransparency false in
private theorem rawEndAdjunction_inverse (A B : SimplicialSpace.{u})
    (K : SSet.{u}) (g : K ⟶ innerHom A.diagram B.diagram) :
    ((rawEndAdjunction A).homEquiv K B).symm g =
      InducedCategory.homMk ((scalarTensorHomEquiv A.diagram K B.diagram).symm g) := by
  rw [rawEndAdjunction, Adjunction.homEquiv_ofNatIsoLeft_symm_apply,
    Adjunction.comp_homEquiv]
  simp only [Equiv.symm_trans_apply, scalarTensorHomAdjunction_homEquiv]
  apply InducedCategory.hom_ext
  change (𝟙 _ ≫ (scalarTensorHomEquiv A.diagram K B.diagram).symm g) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem rawEnd_hom_representation (A B : SimplicialSpace.{u})
    (K : SSet.{u}) (g : K ⟶ innerHom A.diagram B.diagram) :
    g ≫ (rawEndIso A B).hom =
      SimplicialSpace.innerTensorHomEquiv K A B
        (InducedCategory.homMk
          ((scalarTensorHomEquiv A.diagram K B.diagram).symm g)) := by
  apply (SimplicialSpace.innerTensorHomEquiv K A B).symm.injective
  change ((SimplicialSpace.innerTensorHomAdjunction₂.adj A).homEquiv K B).symm
    (g ≫ (rawEndIso A B).hom) = _
  rw [(rawEnd_transpose_laws A B K).1 g]
  simp only [Equiv.symm_apply_apply]
  convert rawEndAdjunction_inverse A B K g using 1; rfl

set_option backward.isDefEq.respectTransparency false in
private theorem rawEnd_inv_representation (A B : SimplicialSpace.{u})
    (K : SSet.{u})
    (h : K ⟶ (SimplicialSpace.innerHomFunctor.obj (op A)).obj B) :
    (scalarTensorHomEquiv A.diagram K B.diagram).symm
        (h ≫ (rawEndIso A B).inv) =
      ((SimplicialSpace.innerTensorHomEquiv K A B).symm h).hom := by
  have h0 := (rawEnd_transpose_laws A B K).2 h
  change ((rawEndAdjunction A).homEquiv K B).symm
    (h ≫ (rawEndIso A B).inv) =
      (SimplicialSpace.innerTensorHomEquiv K A B).symm h at h0
  rw [rawEndAdjunction_inverse] at h0
  exact congrArg (fun f => f.hom) h0

set_option backward.isDefEq.respectTransparency false in
/-- Both exact original outer end projections identify the same scalar maps. -/
theorem rawEnd_projection_laws (A B : SimplicialSpace.{u})
    (m : SimplexCategoryᵒᵖ) :
    (rawEndIso A B).hom ≫ SimplicialSpace.innerHomπ A B m =
      innerHomπ A.diagram B.diagram m ∧
    (rawEndIso A B).inv ≫ innerHomπ A.diagram B.diagram m =
      SimplicialSpace.innerHomπ A B m := by
  let K := innerHom A.diagram B.diagram
  let q := (scalarTensorHomEquiv A.diagram K B.diagram).symm (𝟙 K)
  have h0 := rawEnd_hom_representation A B K (𝟙 K)
  simp only [Category.id_comp] at h0
  have hπ : (rawEndIso A B).hom ≫ SimplicialSpace.innerHomπ A B m =
      innerHomπ A.diagram B.diagram m := by
    have hc :
        SimplicialSpace.innerTensorHomEquiv K A B (InducedCategory.homMk q) ≫
          SimplicialSpace.innerHomπ A B m = curry (q.app m) :=
      SimplicialSpace.innerTensorHomEquiv_π K A B (InducedCategory.homMk q) m
    rw [h0, hc]
    have h := scalarTensorHomEquiv_π A.diagram K B.diagram q m
    simp only [q, Equiv.apply_symm_apply, Category.id_comp] at h
    exact h.symm
  refine ⟨hπ, ?_⟩
  rw [← hπ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Every original source/target map retains both actual comparison directions. -/
theorem rawEnd_naturality :
    (∀ {A A' : SimplicialSpace.{u}} (s : A ⟶ A') (B : SimplicialSpace.{u}),
      innerHomPre s.hom B.diagram ≫ (rawEndIso A B).hom =
        (rawEndIso A' B).hom ≫ (SimplicialSpace.innerHomFunctor.map s.op).app B ∧
      (SimplicialSpace.innerHomFunctor.map s.op).app B ≫ (rawEndIso A B).inv =
        (rawEndIso A' B).inv ≫ innerHomPre s.hom B.diagram) ∧
    (∀ (A : SimplicialSpace.{u}) {B B' : SimplicialSpace.{u}} (t : B ⟶ B'),
      innerHomPost A.diagram t.hom ≫ (rawEndIso A B').hom =
        (rawEndIso A B).hom ≫ (SimplicialSpace.innerHomFunctor.obj (op A)).map t ∧
      (SimplicialSpace.innerHomFunctor.obj (op A)).map t ≫ (rawEndIso A B').inv =
        (rawEndIso A B).inv ≫ innerHomPost A.diagram t.hom) := by
  constructor
  · intro A A' s B
    have hf : innerHomPre s.hom B.diagram ≫ (rawEndIso A B).hom =
        (rawEndIso A' B).hom ≫ (SimplicialSpace.innerHomFunctor.map s.op).app B := by
      apply SimplicialSpace.innerHom_ext A B
      intro m
      have hs : (SimplicialSpace.innerHomFunctor.map s.op).app B ≫
          SimplicialSpace.innerHomπ A B m =
        SimplicialSpace.innerHomπ A' B m ≫
          (pre (s.hom.app m)).app (B.diagram.obj m) :=
        SSet.simplicialSpacePointwiseHomπ_map_source s.hom B.diagram m
      rw [Category.assoc, (rawEnd_projection_laws A B m).1, innerHomPre_π,
        Category.assoc, hs, ← Category.assoc,
        (rawEnd_projection_laws A' B m).1]
    refine ⟨hf, ?_⟩
    have h := congrArg (fun q => (rawEndIso A' B).inv ≫ q ≫
      (rawEndIso A B).inv) hf
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using h.symm
  · intro A B B' t
    exact ⟨(rawEndNatIso A).hom.naturality t, (rawEndNatIso A).inv.naturality t⟩

set_option backward.isDefEq.respectTransparency false in
/-- The same comparison hom and inv commute with every original inner operator. -/
theorem rawEnd_operator_laws (A B : SimplicialSpace.{u})
    {n m : SimplexCategoryᵒᵖ} (ν : n ⟶ m) :
    (innerHom A.diagram B.diagram).map ν ≫ (rawEndIso A B).hom.app m =
      (rawEndIso A B).hom.app n ≫
        ((SimplicialSpace.innerHomFunctor.obj (op A)).obj B).map ν ∧
    ((SimplicialSpace.innerHomFunctor.obj (op A)).obj B).map ν ≫
        (rawEndIso A B).inv.app m =
      (rawEndIso A B).inv.app n ≫ (innerHom A.diagram B.diagram).map ν :=
  ⟨(rawEndIso A B).hom.naturality ν, (rawEndIso A B).inv.naturality ν⟩

set_option backward.isDefEq.respectTransparency false in
private def rawEndOverRawNatIso (A : SimplicialSpace.{u}) :
    innerHomFunctor.obj (op A.diagram) ≅
      SimplicialSpace.ofSimplicialObject ⋙ SimplicialSpace.innerHomFunctor.obj (op A) :=
  NatIso.ofComponents
    (fun B => rawEndIso A (SimplicialSpace.ofSimplicialObject.obj B))
    (by intro B B' b
        exact (rawEndNatIso A).hom.naturality
          (SimplicialSpace.ofSimplicialObject.map b))

variable {C : Type w} [Category.{v} C]

set_option backward.isDefEq.respectTransparency false in
/-- The same prescribed original row is wrapped without changing any raw component. -/
abbrev jointEval (c : C) :
    SimplicialPresheaf.{u} (C × SimplexCategory) ⥤ SimplicialSpace.{u} :=
  LocalizationDiagram.evaluation (J := SimplexCategory) c ⋙
    SimplicialSpace.ofSimplicialObject

variable [LocallySmall.{u} C]

set_option backward.isDefEq.respectTransparency false in
/-- Free evaluation has the full original outer diagram as its coefficient. -/
abbrev jointFree (c : C) :
    SimplicialSpace.{u} ⥤ SimplicialPresheaf.{u} (C × SimplexCategory) :=
  SimplicialSpace.forget ⋙ LocalizationDiagram.free (J := SimplexCategory) c

set_option backward.isDefEq.respectTransparency false in
/-- Both ordinary Hom directions are the actual native composite adjunction. -/
def jointFreeAdjunction (c : C) : jointFree c ⊣ jointEval c :=
  SimplicialSpace.equivalenceSimplicialObject.toAdjunction.comp
    (LocalizationDiagram.freeAdjunction (J := SimplexCategory) c)

set_option backward.isDefEq.respectTransparency false in
private theorem jointFreeAdjunction_hom (c : C) (A : SimplicialSpace.{u})
    (Z : SimplicialPresheaf.{u} (C × SimplexCategory))
    (f : (jointFree c).obj A ⟶ Z) :
    ((jointFreeAdjunction c).homEquiv A Z f).hom =
      (LocalizationDiagram.freeAdjunction (J := SimplexCategory) c).homEquiv
        A.diagram Z f := by
  rw [jointFreeAdjunction, Adjunction.comp_homEquiv]
  rw [Adjunction.homEquiv_unit]
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
private theorem jointFreeAdjunction_inv (c : C) (A : SimplicialSpace.{u})
    (Z : SimplicialPresheaf.{u} (C × SimplexCategory))
    (g : A ⟶ (jointEval c).obj Z) :
    ((jointFreeAdjunction c).homEquiv A Z).symm g =
      ((LocalizationDiagram.freeAdjunction (J := SimplexCategory) c).homEquiv
        A.diagram Z).symm g.hom := by
  apply ((LocalizationDiagram.freeAdjunction (J := SimplexCategory) c).homEquiv
    A.diagram Z).injective
  have h := jointFreeAdjunction_hom c A Z
    (((jointFreeAdjunction c).homEquiv A Z).symm g)
  simp only [Equiv.apply_symm_apply] at h
  simpa only [Equiv.apply_symm_apply] using h.symm

set_option backward.isDefEq.respectTransparency false in
/-- Actual unit/counit triangles and all four original ordinary Hom naturalities. -/
theorem jointFree_adjunction_laws (c : C) (A : SimplicialSpace.{u})
    (Z : SimplicialPresheaf.{u} (C × SimplexCategory)) :
    let a := jointFreeAdjunction c
    (jointFree c).map (a.unit.app A) ≫ a.counit.app ((jointFree c).obj A) = 𝟙 _ ∧
    a.unit.app ((jointEval c).obj Z) ≫
        (jointEval c).map (a.counit.app Z) = 𝟙 _ ∧
    (∀ {B B' : SimplicialSpace.{u}} (s : B ⟶ B')
      (X : SimplicialPresheaf.{u} (C × SimplexCategory))
      (f : (jointFree c).obj B' ⟶ X),
      a.homEquiv B X ((jointFree c).map s ≫ f) =
        s ≫ a.homEquiv B' X f) ∧
    (∀ (B : SimplicialSpace.{u})
      {X X' : SimplicialPresheaf.{u} (C × SimplexCategory)}
      (t : X ⟶ X') (f : (jointFree c).obj B ⟶ X),
      a.homEquiv B X' (f ≫ t) =
        a.homEquiv B X f ≫ (jointEval c).map t) ∧
    (∀ {B B' : SimplicialSpace.{u}} (s : B ⟶ B')
      (X : SimplicialPresheaf.{u} (C × SimplexCategory))
      (f : B' ⟶ (jointEval c).obj X),
      (a.homEquiv B X).symm (s ≫ f) =
        (jointFree c).map s ≫ (a.homEquiv B' X).symm f) ∧
    (∀ (B : SimplicialSpace.{u})
      {X X' : SimplicialPresheaf.{u} (C × SimplexCategory)}
      (t : X ⟶ X') (f : B ⟶ (jointEval c).obj X),
      (a.homEquiv B X').symm (f ≫ (jointEval c).map t) =
        (a.homEquiv B X).symm f ≫ t) := by
  let a := jointFreeAdjunction c
  exact ⟨a.left_triangle_components A, a.right_triangle_components Z,
    fun {_ _} s X f => a.homEquiv_naturality_left s f,
    fun B {_ _} t f => a.homEquiv_naturality_right f t,
    fun {_ _} s X f => a.homEquiv_naturality_left_symm s f,
    fun B {_ _} t f => a.homEquiv_naturality_right_symm f t⟩

variable [Small.{u} C]

set_option backward.isDefEq.respectTransparency false in
/-- The full-coefficient scalar tensor comparison retains its original factor order. -/
def tensorFreeIso (c : C) (A : SimplicialSpace.{u}) :
    SimplicialSpace.innerTensorBifunctor.obj A ⋙ jointFree c ≅
      scalarTensor.obj ((jointFree c).obj A) :=
  NatIso.ofComponents
    (fun K => LocalizationDiagram.freeTensorComponentIso
      (J := SimplexCategory) c A.diagram K)
    (by intro K L k
        exact (LocalizationDiagram.freeTensorIso
          (J := SimplexCategory) c A.diagram).hom.naturality k)

set_option backward.isDefEq.respectTransparency false in
omit [Small.{u} C] in
private theorem tensorFree_hom_inclusion (c e : C) (h : e ⟶ c)
    (A : SimplicialSpace.{u}) (K : SSet.{u}) :
    LocalizationDiagram.freeInclusion (J := SimplexCategory) c e h
        ((SimplicialSpace.innerTensor K).obj A).diagram ≫
      (LocalizationDiagram.evaluation (J := SimplexCategory) e).map
        ((tensorFreeIso c A).hom.app K) =
    (scalarTensorFixed (D := SimplexCategory) K).map
      (LocalizationDiagram.freeInclusion (J := SimplexCategory) c e h A.diagram) := by
  let E := LocalizationDiagram.curry (D := C) (J := SimplexCategory)
  let F := evaluationLeftAdjoint (SimplicialPresheaf.{u} SimplexCategory) (op c)
  let X := F.obj A.diagram
  let XK := F.obj ((scalarTensor.obj A.diagram).obj K)
  let YK := X ⋙ scalarTensorFixed (D := SimplexCategory) K
  let β := LocalizationDiagram.freeTensorNestedIso (J := SimplexCategory) c A.diagram K
  let γ := LocalizationDiagram.uncurryTensorIso (D := C) (J := SimplexCategory) K X
  have hn :=
    congrArg (fun t => t.app (op e)) (E.counitIso.inv.naturality β.hom).symm
  have hg :
      ((E.counitIso.inv.app YK).app (op e)) ≫ (E.functor.map γ.hom).app (op e) =
        (scalarTensorFixed (D := SimplexCategory) K).map
          ((E.counitIso.inv.app X).app (op e)) := by
    ext m n q
    rfl
  change Sigma.ι (fun _ : op c ⟶ op e => (scalarTensor.obj A.diagram).obj K) h.op ≫
      (E.counitIso.inv.app XK).app (op e) ≫
        ((E.functor.map (E.inverse.map β.hom)).app (op e) ≫
          (E.functor.map γ.hom).app (op e)) =
    (scalarTensorFixed (D := SimplexCategory) K).map
      (Sigma.ι (fun _ : op c ⟶ op e => A.diagram) h.op ≫
        (E.counitIso.inv.app X).app (op e))
  have hn' :
      (E.counitIso.inv.app XK).app (op e) ≫
        (E.functor.map (E.inverse.map β.hom)).app (op e) =
      β.hom.app (op e) ≫ (E.counitIso.inv.app YK).app (op e) := hn
  have h1 := congrArg (fun q =>
    Sigma.ι (fun _ : op c ⟶ op e => (scalarTensor.obj A.diagram).obj K) h.op ≫ q ≫
      (E.functor.map γ.hom).app (op e)) hn'
  have h2 := congrArg (fun q =>
    Sigma.ι (fun _ : op c ⟶ op e => (scalarTensor.obj A.diagram).obj K) h.op ≫
      β.hom.app (op e) ≫ q) hg
  have h3 := congrArg (fun q => q ≫
    (scalarTensorFixed (D := SimplexCategory) K).map
      ((E.counitIso.inv.app X).app (op e)))
    (LocalizationDiagram.tensorCoproductIso_hom_ι
      (J := SimplexCategory) c (op e) A.diagram K h.op)
  rw [(scalarTensorFixed (D := SimplexCategory) K).map_comp]
  convert h1.trans (h2.trans h3) using 1; simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
omit [Small.{u} C] in
private theorem tensorFree_inv_inclusion (c e : C) (h : e ⟶ c)
    (A : SimplicialSpace.{u}) (K : SSet.{u}) :
    (scalarTensorFixed (D := SimplexCategory) K).map
        (LocalizationDiagram.freeInclusion (J := SimplexCategory) c e h A.diagram) ≫
      (LocalizationDiagram.evaluation (J := SimplexCategory) e).map
        ((tensorFreeIso c A).inv.app K) =
    LocalizationDiagram.freeInclusion (J := SimplexCategory) c e h
      ((SimplicialSpace.innerTensor K).obj A).diagram := by
  let b := (LocalizationDiagram.evaluation (J := SimplexCategory) e).mapIso
    ((tensorFreeIso c A).app K)
  apply (cancel_mono b.hom).mp
  change _ ≫ (b.inv ≫ b.hom) = _ ≫ b.hom
  rw [Iso.inv_hom_id, Category.comp_id]
  exact (tensorFree_hom_inclusion c e h A K).symm

set_option backward.isDefEq.respectTransparency false in
omit [Small.{u} C] in
/-- Source, scalar, index and every actual free summand retain both tensor comparison legs. -/
theorem tensorFreeIso_laws (c : C) {A B : SimplicialSpace.{u}} (s : A ⟶ B)
    {K L : SSet.{u}} (k : K ⟶ L) {c' : C} (θ : c ⟶ c')
    (e : C) (h : e ⟶ c) :
    (jointFree c).map ((SimplicialSpace.innerTensor K).map s) ≫
        (tensorFreeIso c B).hom.app K =
      (tensorFreeIso c A).hom.app K ≫
        (scalarTensor.map ((jointFree c).map s)).app K ∧
    (tensorFreeIso c A).inv.app K ≫
        (jointFree c).map ((SimplicialSpace.innerTensor K).map s) =
      (scalarTensor.map ((jointFree c).map s)).app K ≫
        (tensorFreeIso c B).inv.app K ∧
    (jointFree c).map ((SimplicialSpace.innerTensorBifunctor.obj A).map k) ≫
        (tensorFreeIso c A).hom.app L =
      (tensorFreeIso c A).hom.app K ≫
        (scalarTensor.obj ((jointFree c).obj A)).map k ∧
    (scalarTensor.obj ((jointFree c).obj A)).map k ≫
        (tensorFreeIso c A).inv.app L =
      (tensorFreeIso c A).inv.app K ≫
        (jointFree c).map ((SimplicialSpace.innerTensorBifunctor.obj A).map k) ∧
    LocalizationDiagram.freeIndexMap (J := SimplexCategory) θ
        ((SimplicialSpace.innerTensor K).obj A).diagram ≫
          (tensorFreeIso c' A).hom.app K =
      (tensorFreeIso c A).hom.app K ≫
        (scalarTensor.map
          (LocalizationDiagram.freeIndexMap (J := SimplexCategory) θ A.diagram)).app K ∧
    (scalarTensor.map
        (LocalizationDiagram.freeIndexMap (J := SimplexCategory) θ A.diagram)).app K ≫
          (tensorFreeIso c' A).inv.app K =
      (tensorFreeIso c A).inv.app K ≫
        LocalizationDiagram.freeIndexMap (J := SimplexCategory) θ
          ((SimplicialSpace.innerTensor K).obj A).diagram ∧
    LocalizationDiagram.freeInclusion (J := SimplexCategory) c e h
        ((SimplicialSpace.innerTensor K).obj A).diagram ≫
      (LocalizationDiagram.evaluation (J := SimplexCategory) e).map
        ((tensorFreeIso c A).hom.app K) =
      (scalarTensorFixed (D := SimplexCategory) K).map
        (LocalizationDiagram.freeInclusion (J := SimplexCategory) c e h A.diagram) ∧
    (scalarTensorFixed (D := SimplexCategory) K).map
        (LocalizationDiagram.freeInclusion (J := SimplexCategory) c e h A.diagram) ≫
      (LocalizationDiagram.evaluation (J := SimplexCategory) e).map
        ((tensorFreeIso c A).inv.app K) =
      LocalizationDiagram.freeInclusion (J := SimplexCategory) c e h
        ((SimplicialSpace.innerTensor K).obj A).diagram := by
  have hs := LocalizationDiagram.freeTensorIso_source
    (J := SimplexCategory) c s.hom K
  have hi := LocalizationDiagram.freeTensorIso_index
    (J := SimplexCategory) θ A.diagram K
  have hs' :
      (jointFree c).map ((SimplicialSpace.innerTensor K).map s) ≫
        (tensorFreeIso c B).hom.app K =
      (tensorFreeIso c A).hom.app K ≫
        (scalarTensor.map ((jointFree c).map s)).app K := hs
  have hi' :
      LocalizationDiagram.freeIndexMap (J := SimplexCategory) θ
          ((SimplicialSpace.innerTensor K).obj A).diagram ≫
            (tensorFreeIso c' A).hom.app K =
      (tensorFreeIso c A).hom.app K ≫
        (scalarTensor.map
          (LocalizationDiagram.freeIndexMap (J := SimplexCategory) θ A.diagram)).app K := hi
  have hsInv : (tensorFreeIso c A).inv.app K ≫
        (jointFree c).map ((SimplicialSpace.innerTensor K).map s) =
      (scalarTensor.map ((jointFree c).map s)).app K ≫
        (tensorFreeIso c B).inv.app K := by
    apply (Iso.inv_comp_eq ((tensorFreeIso c A).app K)).mpr
    have h := (Iso.eq_comp_inv ((tensorFreeIso c B).app K)).mpr hs'
    convert h using 1 <;> rfl
  have hiInv : (scalarTensor.map
        (LocalizationDiagram.freeIndexMap (J := SimplexCategory) θ A.diagram)).app K ≫
          (tensorFreeIso c' A).inv.app K =
      (tensorFreeIso c A).inv.app K ≫
        LocalizationDiagram.freeIndexMap (J := SimplexCategory) θ
          ((SimplicialSpace.innerTensor K).obj A).diagram := by
    apply Eq.symm
    apply (Iso.inv_comp_eq ((tensorFreeIso c A).app K)).mpr
    have h := (Iso.eq_comp_inv ((tensorFreeIso c' A).app K)).mpr hi'
    convert h using 1 <;> rfl
  exact ⟨hs, hsInv, (tensorFreeIso c A).hom.naturality k,
    (tensorFreeIso c A).inv.naturality k, hi, hiInv,
    tensorFree_hom_inclusion c e h A K,
    tensorFree_inv_inclusion c e h A K⟩

set_option backward.isDefEq.respectTransparency false in
/-- The whole target-natural end comparison uses the original flat free object and wrapped row. -/
def rawMappingNatIso (c : C) (A : SimplicialSpace.{u}) :
    innerHomFunctor.obj (op ((jointFree c).obj A)) ≅
      jointEval c ⋙ SimplicialSpace.innerHomFunctor.obj (op A) :=
  LocalizationDiagram.freeHomNatIso (J := SimplexCategory) c A.diagram ≪≫
    Functor.isoWhiskerLeft (LocalizationDiagram.evaluation (J := SimplexCategory) c)
      (rawEndOverRawNatIso A) ≪≫
    (Functor.associator (LocalizationDiagram.evaluation (J := SimplexCategory) c)
      SimplicialSpace.ofSimplicialObject
      (SimplicialSpace.innerHomFunctor.obj (op A))).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual object component of the whole free-row comparison. -/
abbrev rawMappingIso (c : C) (A : SimplicialSpace.{u})
    (Z : SimplicialPresheaf.{u} (C × SimplexCategory)) :
    innerHom ((jointFree c).obj A) Z ≅
      (SimplicialSpace.innerHomFunctor.obj (op A)).obj ((jointEval c).obj Z) :=
  (rawMappingNatIso c A).app Z

set_option backward.isDefEq.respectTransparency false in
private theorem rawMappingIso_hom (c : C) (A : SimplicialSpace.{u})
    (Z : SimplicialPresheaf.{u} (C × SimplexCategory)) :
    (rawMappingIso c A Z).hom =
      (LocalizationDiagram.freeHomIso (J := SimplexCategory) c A.diagram Z).hom ≫
        (rawEndIso A ((jointEval c).obj Z)).hom := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem rawMappingIso_inv (c : C) (A : SimplicialSpace.{u})
    (Z : SimplicialPresheaf.{u} (C × SimplexCategory)) :
    (rawMappingIso c A Z).inv =
      (rawEndIso A ((jointEval c).obj Z)).inv ≫
        (LocalizationDiagram.freeHomIso (J := SimplexCategory) c A.diagram Z).inv := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every scalar map transposes through the same tensor comparison and actual free adjunction. -/
theorem rawMappingIso_transpose (c : C) (A : SimplicialSpace.{u})
    (K : SSet.{u}) (Z : SimplicialPresheaf.{u} (C × SimplexCategory))
    (g : K ⟶ innerHom ((jointFree c).obj A) Z) :
    g ≫ (rawMappingIso c A Z).hom =
      SimplicialSpace.innerTensorHomEquiv K A ((jointEval c).obj Z)
        ((jointFreeAdjunction c).homEquiv ((SimplicialSpace.innerTensor K).obj A) Z
          ((tensorFreeIso c A).hom.app K ≫
            (scalarTensorHomEquiv ((jointFree c).obj A) K Z).symm g)) := by
  have hg := LocalizationDiagram.freeHomIso_hom_characteristic
    (J := SimplexCategory) c A.diagram K Z g
  have hq := congrArg
    (scalarTensorHomEquiv A.diagram K
      ((LocalizationDiagram.evaluation (J := SimplexCategory) c).obj Z)).symm hg
  simp only [Equiv.symm_apply_apply] at hq
  have hr := rawEnd_hom_representation A ((jointEval c).obj Z) K
    (g ≫ (LocalizationDiagram.freeHomIso (J := SimplexCategory) c A.diagram Z).hom)
  calc
    _ = (g ≫ (LocalizationDiagram.freeHomIso (J := SimplexCategory) c A.diagram Z).hom) ≫
        (rawEndIso A ((jointEval c).obj Z)).hom := by
          rw [rawMappingIso_hom, Category.assoc]
    _ = _ := hr
    _ = _ := by
      congr 1
      apply InducedCategory.hom_ext
      have ho := jointFreeAdjunction_hom c ((SimplicialSpace.innerTensor K).obj A) Z
        ((tensorFreeIso c A).hom.app K ≫
          (scalarTensorHomEquiv ((jointFree c).obj A) K Z).symm g)
      convert hq.trans ho.symm using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse retains the original scalar, ordinary and tensor inverse maps. -/
theorem rawMappingIso_transpose_inverse (c : C) (A : SimplicialSpace.{u})
    (K : SSet.{u}) (Z : SimplicialPresheaf.{u} (C × SimplexCategory))
    (h : K ⟶ (SimplicialSpace.innerHomFunctor.obj (op A)).obj ((jointEval c).obj Z)) :
    h ≫ (rawMappingIso c A Z).inv =
      scalarTensorHomEquiv ((jointFree c).obj A) K Z
        ((tensorFreeIso c A).inv.app K ≫
          ((jointFreeAdjunction c).homEquiv
            ((SimplicialSpace.innerTensor K).obj A) Z).symm
              ((SimplicialSpace.innerTensorHomEquiv K A ((jointEval c).obj Z)).symm h)) := by
  let q := ((jointFreeAdjunction c).homEquiv
    ((SimplicialSpace.innerTensor K).obj A) Z).symm
      ((SimplicialSpace.innerTensorHomEquiv K A ((jointEval c).obj Z)).symm h)
  let t := (tensorFreeIso c A).inv.app K ≫ q
  have ht := rawMappingIso_transpose c A K Z
    (scalarTensorHomEquiv ((jointFree c).obj A) K Z t)
  simp only [Equiv.symm_apply_apply] at ht
  have hs : (tensorFreeIso c A).hom.app K ≫ t = q := by
    convert ((tensorFreeIso c A).app K).hom_inv_id_assoc q using 1; rfl
  rw [hs, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at ht
  apply (cancel_mono (rawMappingIso c A Z).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using ht.symm

set_option backward.isDefEq.respectTransparency false in
/-- Both original source directions retain the actual precomposition map and the same inverses. -/
theorem rawMappingIso_source (c : C) {A B : SimplicialSpace.{u}} (s : A ⟶ B)
    (Z : SimplicialPresheaf.{u} (C × SimplexCategory)) :
    innerHomPre ((jointFree c).map s) Z ≫ (rawMappingIso c A Z).hom =
      (rawMappingIso c B Z).hom ≫
        (SimplicialSpace.innerHomFunctor.map s.op).app ((jointEval c).obj Z) ∧
    (SimplicialSpace.innerHomFunctor.map s.op).app ((jointEval c).obj Z) ≫
        (rawMappingIso c A Z).inv =
      (rawMappingIso c B Z).inv ≫ innerHomPre ((jointFree c).map s) Z := by
  have hf : innerHomPre ((jointFree c).map s) Z ≫ (rawMappingIso c A Z).hom =
      (rawMappingIso c B Z).hom ≫
        (SimplicialSpace.innerHomFunctor.map s.op).app ((jointEval c).obj Z) := by
    have hs := LocalizationDiagram.freeHomIso_source
      (J := SimplexCategory) c s.hom Z
    have hr := (rawEnd_naturality.1 s ((jointEval c).obj Z)).1
    have h1 := congrArg (fun q => q ≫ (rawEndIso A ((jointEval c).obj Z)).hom) hs
    have h2 := congrArg (fun q =>
      (LocalizationDiagram.freeHomIso (J := SimplexCategory) c B.diagram Z).hom ≫ q) hr
    rw [rawMappingIso_hom, rawMappingIso_hom]
    convert h1.trans h2 using 1 <;> simp [Category.assoc, jointEval]
  refine ⟨hf, ?_⟩
  have h := congrArg (fun q => (rawMappingIso c B Z).inv ≫ q ≫
    (rawMappingIso c A Z).inv) hf
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using h.symm

set_option backward.isDefEq.respectTransparency false in
/-- Both original target directions are components of the same whole natural isomorphism. -/
theorem rawMappingIso_target (c : C) (A : SimplicialSpace.{u})
    {Z Z' : SimplicialPresheaf.{u} (C × SimplexCategory)} (t : Z ⟶ Z') :
    innerHomPost ((jointFree c).obj A) t ≫ (rawMappingIso c A Z').hom =
      (rawMappingIso c A Z).hom ≫
        (SimplicialSpace.innerHomFunctor.obj (op A)).map ((jointEval c).map t) ∧
    (SimplicialSpace.innerHomFunctor.obj (op A)).map ((jointEval c).map t) ≫
        (rawMappingIso c A Z').inv =
      (rawMappingIso c A Z).inv ≫ innerHomPost ((jointFree c).obj A) t :=
  ⟨(rawMappingNatIso c A).hom.naturality t,
    (rawMappingNatIso c A).inv.naturality t⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every original representing arrow retains its actual opposite restriction in both directions. -/
theorem rawMappingIso_index {c c' : C} (θ : c ⟶ c') (A : SimplicialSpace.{u})
    (Z : SimplicialPresheaf.{u} (C × SimplexCategory)) :
    innerHomPre (LocalizationDiagram.freeIndexMap (J := SimplexCategory) θ A.diagram) Z ≫
        (rawMappingIso c A Z).hom =
      (rawMappingIso c' A Z).hom ≫
        (SimplicialSpace.innerHomFunctor.obj (op A)).map
          (SimplicialSpace.ofSimplicialObject.map
            ((LocalizationDiagram.evaluationRestriction (J := SimplexCategory) θ).app Z)) ∧
    (SimplicialSpace.innerHomFunctor.obj (op A)).map
        (SimplicialSpace.ofSimplicialObject.map
          ((LocalizationDiagram.evaluationRestriction (J := SimplexCategory) θ).app Z)) ≫
            (rawMappingIso c A Z).inv =
      (rawMappingIso c' A Z).inv ≫
        innerHomPre (LocalizationDiagram.freeIndexMap (J := SimplexCategory) θ A.diagram) Z := by
  let r : (jointEval c').obj Z ⟶ (jointEval c).obj Z :=
    SimplicialSpace.ofSimplicialObject.map
    ((LocalizationDiagram.evaluationRestriction (J := SimplexCategory) θ).app Z)
  have hr := (rawEnd_naturality.2 A r).1
  have hn := LocalizationDiagram.freeHomIso_index
    (J := SimplexCategory) θ A.diagram Z
  have hf : innerHomPre
        (LocalizationDiagram.freeIndexMap (J := SimplexCategory) θ A.diagram) Z ≫
          (rawMappingIso c A Z).hom =
      (rawMappingIso c' A Z).hom ≫
        (SimplicialSpace.innerHomFunctor.obj (op A)).map r := by
    have h1 := congrArg (fun q => q ≫ (rawEndIso A ((jointEval c).obj Z)).hom) hn
    have h2 := congrArg (fun q =>
      (LocalizationDiagram.freeHomIso (J := SimplexCategory) c' A.diagram Z).hom ≫ q) hr
    rw [rawMappingIso_hom, rawMappingIso_hom]
    convert h1.trans h2 using 1 <;> simp only [Category.assoc]
  refine ⟨hf, ?_⟩
  have h := congrArg (fun q => (rawMappingIso c' A Z).inv ≫ q ≫
    (rawMappingIso c A Z).inv) hf
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using h.symm

set_option backward.isDefEq.respectTransparency false in
/-- All original inner operators commute with both maps of the actual free-row comparison. -/
theorem rawMappingIso_operator_laws (c : C) (A : SimplicialSpace.{u})
    (Z : SimplicialPresheaf.{u} (C × SimplexCategory))
    {n m : SimplexCategoryᵒᵖ} (ν : n ⟶ m) :
    (innerHom ((jointFree c).obj A) Z).map ν ≫ (rawMappingIso c A Z).hom.app m =
      (rawMappingIso c A Z).hom.app n ≫
        ((SimplicialSpace.innerHomFunctor.obj (op A)).obj ((jointEval c).obj Z)).map ν ∧
    ((SimplicialSpace.innerHomFunctor.obj (op A)).obj ((jointEval c).obj Z)).map ν ≫
        (rawMappingIso c A Z).inv.app m =
      (rawMappingIso c A Z).inv.app n ≫ (innerHom ((jointFree c).obj A) Z).map ν :=
  ⟨(rawMappingIso c A Z).hom.naturality ν,
    (rawMappingIso c A Z).inv.naturality ν⟩

set_option backward.isDefEq.respectTransparency false in
private theorem rawMapping_forward_projection (c : C) (A : SimplicialSpace.{u})
    (Z : SimplicialPresheaf.{u} (C × SimplexCategory)) (m : SimplexCategoryᵒᵖ) :
    (rawMappingIso c A Z).hom ≫ SimplicialSpace.innerHomπ A ((jointEval c).obj Z) m =
      innerHomπ ((jointFree c).obj A) Z (op (c, m.unop)) ≫
        (pre ((LocalizationDiagram.freeInclusion (J := SimplexCategory)
          c c (𝟙 c) A.diagram).app m)).app (Z.obj (op (c, m.unop))) := by
  let K := innerHom ((jointFree c).obj A) Z
  let q := (scalarTensorHomEquiv ((jointFree c).obj A) K Z).symm (𝟙 K)
  let f := (jointFreeAdjunction c).homEquiv
    ((SimplicialSpace.innerTensor K).obj A) Z
      ((tensorFreeIso c A).hom.app K ≫ q)
  have ht := rawMappingIso_transpose c A K Z (𝟙 K)
  simp only [Category.id_comp] at ht
  have hf : f.hom =
      (scalarTensorFixed (D := SimplexCategory) K).map
        (LocalizationDiagram.freeInclusion (J := SimplexCategory) c c (𝟙 c) A.diagram) ≫
          (LocalizationDiagram.evaluation (J := SimplexCategory) c).map q := by
    dsimp only [f]
    rw [jointFreeAdjunction_hom,
      LocalizationDiagram.freeAdjunction_hom_characteristic,
      Functor.map_comp, ← Category.assoc, tensorFree_hom_inclusion]
  let a : A.diagram.obj m ⟶ ((jointFree c).obj A).obj (op (c, m.unop)) :=
    (LocalizationDiagram.freeInclusion (J := SimplexCategory) c c (𝟙 c) A.diagram).app m
  let qm : ((jointFree c).obj A).obj (op (c, m.unop)) ⊗ K ⟶
      Z.obj (op (c, m.unop)) := q.app (op (c, m.unop))
  have hm : f.hom.app m = a ▷ K ≫ qm := by
    convert congrArg (fun t => t.app m) hf using 1; rfl
  have hc := curry_pre_app a qm
  have hq := scalarTensorHomEquiv_π ((jointFree c).obj A) K Z q (op (c, m.unop))
  simp only [q, Equiv.apply_symm_apply, Category.id_comp] at hq
  have hπ :
      SimplicialSpace.innerTensorHomEquiv K A ((jointEval c).obj Z) f ≫
        SimplicialSpace.innerHomπ A ((jointEval c).obj Z) m = curry (f.hom.app m) :=
    SimplicialSpace.innerTensorHomEquiv_π K A ((jointEval c).obj Z) f m
  rw [ht]
  change SimplicialSpace.innerTensorHomEquiv K A ((jointEval c).obj Z) f ≫ _ = _
  rw [hπ]
  calc
    _ = curry (a ▷ K ≫ qm) := congrArg curry hm
    _ = curry qm ≫ (pre a).app (Z.obj (op (c, m.unop))) := hc.symm
    _ = _ := by
      exact congrArg (fun t => t ≫ (pre a).app (Z.obj (op (c, m.unop)))) hq.symm

set_option backward.isDefEq.respectTransparency false in
private theorem rawMapping_inverse_projection (c e : C) (h : e ⟶ c)
    (A : SimplicialSpace.{u}) (Z : SimplicialPresheaf.{u} (C × SimplexCategory))
    (m : SimplexCategoryᵒᵖ) :
    (rawMappingIso c A Z).inv ≫ innerHomπ ((jointFree c).obj A) Z (op (e, m.unop)) ≫
        (pre ((LocalizationDiagram.freeInclusion (J := SimplexCategory)
          c e h A.diagram).app m)).app (Z.obj (op (e, m.unop))) =
      SimplicialSpace.innerHomπ A ((jointEval c).obj Z) m ≫
        (ihom (A.diagram.obj m)).map (Z.map
            (show (e, m.unop) ⟶ (c, m.unop) from (h, 𝟙 m.unop)).op) := by
  let K := (SimplicialSpace.innerHomFunctor.obj (op A)).obj ((jointEval c).obj Z)
  let f := (SimplicialSpace.innerTensorHomEquiv K A ((jointEval c).obj Z)).symm (𝟙 K)
  let q := (scalarTensorHomEquiv ((jointFree c).obj A) K Z).symm (rawMappingIso c A Z).inv
  let b := ((LocalizationDiagram.freeAdjunction (J := SimplexCategory) c).homEquiv
    ((SimplicialSpace.innerTensor K).obj A).diagram Z).symm f.hom
  have hq : q = (tensorFreeIso c A).inv.app K ≫ b := by
    have hx := rawMappingIso_transpose_inverse c A K Z (𝟙 K)
    simp only [Category.id_comp] at hx
    have hy := congrArg (scalarTensorHomEquiv ((jointFree c).obj A) K Z).symm hx
    simp only [Equiv.symm_apply_apply] at hy
    change q = (tensorFreeIso c A).inv.app K ≫
      ((jointFreeAdjunction c).homEquiv ((SimplicialSpace.innerTensor K).obj A) Z).symm f at hy
    rw [jointFreeAdjunction_inv] at hy
    exact hy
  have hn := LocalizationDiagram.freeAdjunction_inv_characteristic
    (J := SimplexCategory) c e h ((SimplicialSpace.innerTensor K).obj A).diagram Z f.hom
  have hi := tensorFree_inv_inclusion c e h A K
  have h1 := congrArg (fun t =>
    (scalarTensorFixed (D := SimplexCategory) K).map
      (LocalizationDiagram.freeInclusion (J := SimplexCategory) c e h A.diagram) ≫
        (LocalizationDiagram.evaluation (J := SimplexCategory) e).map t) hq
  have h2 := congrArg (fun t =>
    t ≫ (LocalizationDiagram.evaluation (J := SimplexCategory) e).map b) hi
  have hleg :
      (scalarTensorFixed (D := SimplexCategory) K).map
          (LocalizationDiagram.freeInclusion (J := SimplexCategory) c e h A.diagram) ≫
        (LocalizationDiagram.evaluation (J := SimplexCategory) e).map q =
      f.hom ≫
          ((LocalizationDiagram.curry (D := C) (J := SimplexCategory)).functor.obj Z).map h.op := by
    convert h1.trans (h2.trans hn) using 1
  let a : A.diagram.obj m ⟶ ((jointFree c).obj A).obj (op (e, m.unop)) :=
    (LocalizationDiagram.freeInclusion (J := SimplexCategory) c e h A.diagram).app m
  let qm : ((jointFree c).obj A).obj (op (e, m.unop)) ⊗ K ⟶
      Z.obj (op (e, m.unop)) := q.app (op (e, m.unop))
  let fm : A.diagram.obj m ⊗ K ⟶ Z.obj (op (c, m.unop)) := f.hom.app m
  let t : Z.obj (op (c, m.unop)) ⟶ Z.obj (op (e, m.unop)) :=
    Z.map (show (e, m.unop) ⟶ (c, m.unop) from (h, 𝟙 m.unop)).op
  have he : a ▷ K ≫ qm = fm ≫ t := by
    convert congrArg (fun g => g.app m) hleg using 1 <;> rfl
  have hc := curry_pre_app a qm
  have hn' := curry_natural_right fm t
  have hp := scalarTensorHomEquiv_π ((jointFree c).obj A) K Z q (op (e, m.unop))
  simp only [q, Equiv.apply_symm_apply] at hp
  have hπ :
      SimplicialSpace.innerTensorHomEquiv K A ((jointEval c).obj Z) f ≫
        SimplicialSpace.innerHomπ A ((jointEval c).obj Z) m = curry (f.hom.app m) :=
    SimplicialSpace.innerTensorHomEquiv_π K A ((jointEval c).obj Z) f m
  have hf : SimplicialSpace.innerHomπ A ((jointEval c).obj Z) m = curry fm := by
    simpa only [f, Equiv.apply_symm_apply, Category.id_comp] using hπ
  calc
    _ = curry qm ≫ (pre a).app (Z.obj (op (e, m.unop))) := by
      convert congrArg (fun g => g ≫ (pre a).app (Z.obj (op (e, m.unop)))) hp using 1; rfl
    _ = curry (a ▷ K ≫ qm) := hc
    _ = curry (fm ≫ t) := congrArg curry he
    _ = curry fm ≫ (ihom (A.diagram.obj m)).map t := hn'
    _ = _ := by
      exact congrArg (fun g => g ≫ (ihom (A.diagram.obj m)).map t) hf.symm

set_option backward.isDefEq.respectTransparency false in
/-- Forward evaluation and every original Hom-labelled inverse projection retain the whole ends. -/
theorem rawMappingIso_projection_laws (c : C) (A : SimplicialSpace.{u})
    (Z : SimplicialPresheaf.{u} (C × SimplexCategory)) (m : SimplexCategoryᵒᵖ) :
    (rawMappingIso c A Z).hom ≫ SimplicialSpace.innerHomπ A ((jointEval c).obj Z) m =
      innerHomπ ((jointFree c).obj A) Z (op (c, m.unop)) ≫
        (pre ((LocalizationDiagram.freeInclusion (J := SimplexCategory)
          c c (𝟙 c) A.diagram).app m)).app (Z.obj (op (c, m.unop))) ∧
    (∀ (e : C) (h : e ⟶ c),
      (rawMappingIso c A Z).inv ≫ innerHomπ ((jointFree c).obj A) Z (op (e, m.unop)) ≫
          (pre ((LocalizationDiagram.freeInclusion (J := SimplexCategory)
            c e h A.diagram).app m)).app (Z.obj (op (e, m.unop))) =
        SimplicialSpace.innerHomπ A ((jointEval c).obj Z) m ≫
          (ihom (A.diagram.obj m)).map (Z.map
              (show (e, m.unop) ⟶ (c, m.unop) from (h, 𝟙 m.unop)).op)) :=
  ⟨rawMapping_forward_projection c A Z m,
    fun e h => rawMapping_inverse_projection c e h A Z m⟩

set_option backward.isDefEq.respectTransparency false in
/-- The whole original precomposition Arrow uses the comparison at B and then A. -/
def precompArrowIso (c : C) {A B : SimplicialSpace.{u}} (s : A ⟶ B)
    (Z : SimplicialPresheaf.{u} (C × SimplexCategory)) :
    Arrow.mk (innerHomPre ((jointFree c).map s) Z) ≅
      Arrow.mk ((SimplicialSpace.innerHomFunctor.map s.op).app ((jointEval c).obj Z)) :=
  Arrow.isoMk (rawMappingIso c B Z) (rawMappingIso c A Z)
    (rawMappingIso_source c s Z).1.symm

set_option backward.isDefEq.respectTransparency false in
/-- Four fields, both original squares and both whole Arrow inverse laws hold on these same maps. -/
theorem precompArrowIso_laws (c : C) {A B : SimplicialSpace.{u}} (s : A ⟶ B)
    (Z : SimplicialPresheaf.{u} (C × SimplexCategory)) :
    (precompArrowIso c s Z).hom.left = (rawMappingIso c B Z).hom ∧
    (precompArrowIso c s Z).hom.right = (rawMappingIso c A Z).hom ∧
    (precompArrowIso c s Z).inv.left = (rawMappingIso c B Z).inv ∧
    (precompArrowIso c s Z).inv.right = (rawMappingIso c A Z).inv ∧
    innerHomPre ((jointFree c).map s) Z ≫ (precompArrowIso c s Z).hom.right =
      (precompArrowIso c s Z).hom.left ≫
        (SimplicialSpace.innerHomFunctor.map s.op).app ((jointEval c).obj Z) ∧
    (SimplicialSpace.innerHomFunctor.map s.op).app ((jointEval c).obj Z) ≫
        (precompArrowIso c s Z).inv.right =
      (precompArrowIso c s Z).inv.left ≫ innerHomPre ((jointFree c).map s) Z ∧
    (precompArrowIso c s Z).hom ≫ (precompArrowIso c s Z).inv = 𝟙 _ ∧
    (precompArrowIso c s Z).inv ≫ (precompArrowIso c s Z).hom = 𝟙 _ :=
  ⟨rfl, rfl, rfl, rfl, (rawMappingIso_source c s Z).1,
    (rawMappingIso_source c s Z).2,
    (precompArrowIso c s Z).hom_inv_id, (precompArrowIso c s Z).inv_hom_id⟩

set_option backward.isDefEq.respectTransparency false in
/-- Both object-level inverse laws hold on the original fixed-universe mapping objects. -/
theorem rawMappingIso_roundtrips (c : C) (A : SimplicialSpace.{u})
    (Z : SimplicialPresheaf.{u} (C × SimplexCategory)) :
    (rawMappingIso c A Z).hom ≫ (rawMappingIso c A Z).inv = 𝟙 _ ∧
    (rawMappingIso c A Z).inv ≫ (rawMappingIso c A Z).hom = 𝟙 _ :=
  ⟨(rawMappingIso c A Z).hom_inv_id, (rawMappingIso c A Z).inv_hom_id⟩

set_option backward.isDefEq.respectTransparency false in
/-- The same original raw scalar weak test transports through the actual whole Arrow. -/
theorem precomposition_weak_iff (c : C) {A B : SimplicialSpace.{u}} (s : A ⟶ B)
    (Z : SimplicialPresheaf.{u} (C × SimplexCategory)) :
    SSet.realizationWeakEquivalences
        (innerHomPre ((jointFree c).map s) Z) ↔
      SSet.realizationWeakEquivalences
        ((SimplicialSpace.innerHomFunctor.map s.op).app ((jointEval c).obj Z)) :=
  SSet.realizationWeakEquivalences.arrow_mk_iso_iff (precompArrowIso c s Z)

end SimplicialPresheaf.IndexedFreeMapping
