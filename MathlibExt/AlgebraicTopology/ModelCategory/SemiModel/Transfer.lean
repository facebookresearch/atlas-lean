/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The structural construction is adapted here to retain only the original
source-restricted Hom-colimit hypothesis in the right-lifting proof.
See NOTICE in the repository root for the original Mathlib attribution.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.SemiModel.Basic
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.RelativeSmallness
public import MathlibExt.AlgebraicTopology.ModelCategory.SmallGenerator
public import MathlibExt.CategoryTheory.MorphismProperty.PushoutProduct
public import Mathlib.CategoryTheory.SmallObject.Basic
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# Source-restricted small-object constructions and semi-model transfer

The geometric transfinite construction is available without any global
source-Hom preservation hypothesis. Its right lifting assertion below takes
preservation for the actual original cell diagram explicitly. This permits
White--Yau, arXiv:1503.06720v2, Definition 2.2.1 and Theorem 2.2.2, to retain
conditional free-J source smallness instead of asserting a full free-J
small-object argument.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe w u v

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open Category
open CategoryTheory.SmallObject

namespace HomotopicalAlgebra.SemiModel.RawSmallObject

variable {C : Type u} [Category.{v} C] (I : MorphismProperty C)

/-- Only the structural fields needed to construct the actual transfinite iteration. -/
class Geometry (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType] : Prop where
  /-- The actual arrow family is small at the working size. -/
  isSmall : I.IsSmall.{w}
  /-- The carrier is locally small at that same size. -/
  locallySmall : LocallySmall.{w} C
  /-- The actual pushouts exist. -/
  hasPushouts : HasPushouts C
  /-- The actual working-size coproducts exist. -/
  hasCoproducts : HasCoproducts.{w} C
  /-- The actual ordinal iteration colimits exist. -/
  hasIterationOfShape : HasIterationOfShape κ.ord.ToType C

instance (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [I.IsSmall.{w}] [LocallySmall.{w} C] [HasPushouts C]
    [HasCoproducts.{w} C] [HasIterationOfShape κ.ord.ToType C] : Geometry I κ where
  isSmall := inferInstance
  locallySmall := inferInstance
  hasPushouts := inferInstance
  hasCoproducts := inferInstance
  hasIterationOfShape := inferInstance

variable (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Geometry I κ]

include I κ

lemma isSmall : IsSmall.{w} I :=
  Geometry.isSmall κ

lemma locallySmall : LocallySmall.{w} C :=
  Geometry.locallySmall I κ

lemma hasIterationOfShape : HasIterationOfShape κ.ord.ToType C :=
  Geometry.hasIterationOfShape I

lemma hasPushouts : HasPushouts C :=
  Geometry.hasPushouts I κ

lemma hasCoproducts : HasCoproducts.{w} C :=
  Geometry.hasCoproducts I κ

lemma hasColimitsOfShape_discrete (X Y : C) (p : X ⟶ Y) :
    HasColimitsOfShape
      (Discrete (FunctorObjIndex I.homFamily p)) C := by
  have := locallySmall I κ
  have := isSmall I κ
  have := hasCoproducts I κ
  exact hasColimitsOfShape_of_equivalence
    (Discrete.equivalence (equivShrink.{w} _)).symm

/-- The successor structure on `Arrow C ⥤ Arrow C` corresponding
to the iterations of the natural transformation
`ε : 𝟭 (Arrow C) ⟶ SmallObject.functor I.homFamily`
(see the file `SmallObject.Construction`). -/
noncomputable def succStruct : SuccStruct (Arrow C ⥤ Arrow C) :=
  haveI := hasColimitsOfShape_discrete I κ
  haveI := hasPushouts I κ
  SuccStruct.ofNatTrans (ε I.homFamily)

set_option backward.isDefEq.respectTransparency.types false in
/-- For the successor structure `succStruct I κ` on `Arrow C ⥤ Arrow C`,
the morphism from an object to its successor induces
morphisms in `C` which consists in attaching `I`-cells. -/
noncomputable def attachCellsOfSuccStructProp
    {F G : Arrow C ⥤ Arrow C} {φ : F ⟶ G}
    (h : (succStruct I κ).prop φ) (f : Arrow C) :
    AttachCells.{w} I.homFamily (φ.app f).left :=
  haveI := locallySmall I κ
  haveI := isSmall I κ
  haveI := hasColimitsOfShape_discrete I κ
  haveI := hasPushouts I κ
  AttachCells.ofArrowIso (attachCellsιFunctorObjOfSmall _ _)
    ((Functor.mapArrow ((evaluation _ _).obj f ⋙
      Arrow.leftFunc)).mapIso h.arrowIso.symm)

/-- The class of morphisms in `Arrow C` which on the left side are
pushouts of coproducts of morphisms in `I`, and which are
isomorphisms on the right side. -/
def propArrow : MorphismProperty (Arrow C) := fun _ _ f ↦
  (coproducts.{w} I).pushouts f.left ∧ (isomorphisms C) f.right

#adaptation_note
/--
After https://github.com/leanprover/lean4/pull/14624:

We had to use the `instanceSearchTypes` backward compatibility flag to make an instance search
succeed. Concretely, the following instance cannot be synthesized:
`Category.{max u v, max u v} (Comma (𝟭 C) (𝟭 C) ⥤ Comma (𝟭 C) (𝟭 C))`
It is needed by the `⟨F⟩` pattern in the opening `intro`, which re-elaborates `ofHoms.mk F` against
a goal where the carrier `Arrow C ⥤ Arrow C` is exposed at its `Comma (𝟭 C) (𝟭 C)` spelling.

The failure happens while applying `@Functor.category`: assigning one of its
instance-implicit-argument metavariables is rejected because the metavariable's type and the type
of the assigned value do not match at `.instances` transparency. The metavariable's expected type
is `Category (Comma (𝟭 C) (𝟭 C))`, whereas the assigned value `instCategoryArrow` has type
`Category (Arrow C)`. The comparison bottoms out at `Comma (𝟭 C) (𝟭 C) =?= Arrow C`, where `Arrow`
is a plain semireducible `def` and therefore does not unfold at the `.instances` transparency that
instance search runs at. Lean falls back to synthesize an instance of the correct type, but it
returns `commaCategory`, which is again not defeq to `instCategoryArrow`: that comparison runs at
`.implicit`, and `Arrow` does not unfold there either.

With the metavariable unsolved, the `intro` argument `⟨F⟩` has type `ofHoms ?m.69 (?m.69 F)`,
which fails to unify with `(succStruct I κ).prop f✝`.

Potential fix: mark `Arrow` and `Arrow.Hom` implicit-reducible, then remove
`instanceSearchTypes false`.
-/
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
lemma succStruct_prop_le_propArrow :
    (succStruct I κ).prop ≤ (propArrow.{w} I).functorCategory (Arrow C) := by
  have := locallySmall I κ
  have := isSmall I κ
  have := hasColimitsOfShape_discrete I κ
  have := hasPushouts I κ
  intro _ _ _ ⟨F⟩ f
  constructor
  · nth_rw 1 [← I.ofHoms_homFamily]
    apply pushouts_mk _ (functorObj_isPushout I.homFamily (F.obj f).hom)
    exact coproducts_of_small _ _ (colimitsOfShape_colimMap _ (by rintro ⟨j⟩; constructor))
  · rw [MorphismProperty.isomorphisms.iff]
    dsimp [succStruct]
    infer_instance

/-- The functor `κ.ord.ToType ⥤ Arrow C ⥤ Arrow C` corresponding to the
iterations of the successor structure `succStruct I κ`. -/
noncomputable def iterationFunctor : κ.ord.ToType ⥤ Arrow C ⥤ Arrow C :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).iterationFunctor κ.ord.ToType

/-- The colimit of `iterationFunctor I κ`. -/
noncomputable def iteration : Arrow C ⥤ Arrow C :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).iteration κ.ord.ToType

/-- The natural "inclusion" `𝟭 (Arrow C) ⟶ iteration I κ`. -/
noncomputable def ιIteration : 𝟭 _ ⟶ iteration I κ :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).ιIteration κ.ord.ToType

/-- The morphism `ιIteration I κ` is a transfinite composition of shape
`κ.ord.ToType` of morphisms satisfying `(succStruct I κ).prop`. -/
noncomputable def transfiniteCompositionOfShapeSuccStructPropιIteration :
    (succStruct I κ).prop.TransfiniteCompositionOfShape κ.ord.ToType (ιIteration I κ) :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).transfiniteCompositionOfShapeιIteration κ.ord.ToType

@[simp]
lemma transfiniteCompositionOfShapeSuccStructPropιIteration_F :
    (transfiniteCompositionOfShapeSuccStructPropιIteration I κ).F =
      iterationFunctor I κ :=
  rfl

/-- For any `f : Arrow C`, the map `((ιIteration I κ).app f).right` is
a transfinite composition of isomorphisms. -/
noncomputable def transfiniteCompositionOfShapeιIterationAppRight (f : Arrow C) :
    (isomorphisms C).TransfiniteCompositionOfShape κ.ord.ToType
      ((ιIteration I κ).app f).right :=
  haveI := hasIterationOfShape I κ
  let h := transfiniteCompositionOfShapeSuccStructPropιIteration I κ
  { toTransfiniteCompositionOfShape :=
      h.toTransfiniteCompositionOfShape.map ((evaluation _ _).obj f ⋙ Arrow.rightFunc)
    map_mem j hj := ((succStruct_prop_le_propArrow I κ _ (h.map_mem j hj)) f).2 }

instance (f : Arrow C) : IsIso ((ιIteration I κ).app f).right :=
  (transfiniteCompositionOfShapeιIterationAppRight I κ f).isIso

instance {j₁ j₂ : κ.ord.ToType} (φ : j₁ ⟶ j₂) (f : Arrow C) :
    IsIso (((iterationFunctor I κ).map φ).app f).right :=
  inferInstanceAs (IsIso ((transfiniteCompositionOfShapeιIterationAppRight I κ f).F.map φ))

/-- For any `f : Arrow C`, the object `((iteration I κ).obj f).right`
identifies to `f.right`. -/
@[simps! hom]
noncomputable def iterationObjRightIso (f : Arrow C) :
    f.right ≅ ((iteration I κ).obj f).right :=
  asIso ((ιIteration I κ).app f).right

set_option backward.isDefEq.respectTransparency false in
/-- For any `f : Arrow C` and `j : κ.ord.ToType`, the object
`(((iterationFunctor I κ).obj j).obj f).right` identifies to `f.right`. -/
noncomputable def iterationFunctorObjObjRightIso (f : Arrow C) (j : κ.ord.ToType) :
    (((iterationFunctor I κ).obj j).obj f).right ≅ f.right :=
  asIso ((transfiniteCompositionOfShapeιIterationAppRight I κ f).incl.app j) ≪≫
    (iterationObjRightIso I κ f).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma iterationFunctorObjObjRightIso_ιIteration_app_right (f : Arrow C) (j : κ.ord.ToType) :
    (iterationFunctorObjObjRightIso I κ f j).hom ≫ ((ιIteration I κ).app f).right =
      (transfiniteCompositionOfShapeιIterationAppRight I κ f).incl.app j := by
  simp [iterationFunctorObjObjRightIso, iterationObjRightIso]

lemma prop_iterationFunctor_map_succ (j : κ.ord.ToType) :
    (succStruct I κ).prop ((iterationFunctor I κ).map (homOfLE (Order.le_succ j))) := by
  have := hasIterationOfShape I κ
  have := Cardinal.noMaxOrder (Fact.elim inferInstance : κ.IsRegular).aleph0_le
  exact (succStruct I κ).prop_iterationFunctor_map_succ j (not_isMax j)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For any `f : Arrow C` and `j : κ.ord.ToType`, the morphism
`((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f` identifies
to a morphism given by `SmallObject.ε I.homFamily`. -/
noncomputable def iterationFunctorMapSuccAppArrowIso (f : Arrow C) (j : κ.ord.ToType) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    Arrow.mk (((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f) ≅
      (ε I.homFamily).app (((iterationFunctor I κ).obj j).obj f) :=
  have := hasIterationOfShape I κ
  have := Cardinal.noMaxOrder (Fact.elim inferInstance : κ.IsRegular).aleph0_le
  Arrow.isoMk (Iso.refl _)
    (((evaluation _ _).obj f).mapIso
      ((succStruct I κ).iterationFunctorObjSuccIso j (not_isMax j))) (by
    have := congr($((succStruct I κ).iterationFunctor_map_succ j (not_isMax j)).app f)
    dsimp at this
    dsimp [iterationFunctor]
    rw [id_comp, this, assoc, Iso.inv_hom_id_app, comp_id]
    dsimp [succStruct])

@[simp]
lemma iterationFunctorMapSuccAppArrowIso_hom_left (f : Arrow C) (j : κ.ord.ToType) :
    (iterationFunctorMapSuccAppArrowIso I κ f j).hom.left = 𝟙 _ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in -- Needed below
@[reassoc (attr := simp)]
lemma iterationFunctorMapSuccAppArrowIso_hom_right_right_comp
    (f : Arrow C) (j : κ.ord.ToType) :
    (iterationFunctorMapSuccAppArrowIso I κ f j).hom.right.right ≫
      (((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f).right = 𝟙 _ := by
  have := Arrow.rightFunc.congr_map ((iterationFunctorMapSuccAppArrowIso I κ f j).hom.w)
  dsimp at this ⊢
  rw [← cancel_epi (((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f).right,
    ← reassoc_of% this, comp_id]

section

variable {X Y : C} (f : X ⟶ Y)

/-- The intermediate object in the factorization given by the
small object argument. -/
noncomputable def obj : C := ((iteration I κ).obj (Arrow.mk f)).left

/-- The "inclusion" morphism in the factorization given by
the small object argument. -/
noncomputable def ιObj : X ⟶ obj I κ f := ((ιIteration I κ).app (Arrow.mk f)).left

/-- The "projection" morphism in the factorization given by
the small object argument. -/
noncomputable def πObj : obj I κ f ⟶ Y :=
  ((iteration I κ).obj (Arrow.mk f)).hom ≫ inv ((ιIteration I κ).app f).right

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
lemma πObj_ιIteration_app_right :
    πObj I κ f ≫ ((ιIteration I κ).app f).right =
      ((iteration I κ).obj (Arrow.mk f)).hom := by simp [πObj]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma ιObj_πObj : ιObj I κ f ≫ πObj I κ f = f := by
  simp [ιObj, πObj]

/-- The morphism `ιObj I κ f` is a relative `I`-cell complex. -/
noncomputable def relativeCellComplexιObj :
    RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) ↦ I.homFamily)
      (ιObj I κ f) := by
  have := hasIterationOfShape I κ
  let h := transfiniteCompositionOfShapeSuccStructPropιIteration I κ
  exact
  { toTransfiniteCompositionOfShape :=
      h.toTransfiniteCompositionOfShape.map ((evaluation _ _).obj f ⋙ Arrow.leftFunc)
    attachCells j hj :=
      attachCellsOfSuccStructProp I κ (h.map_mem j hj) f }

lemma transfiniteCompositionsOfShape_ιObj :
    (coproducts.{w} I).pushouts.transfiniteCompositionsOfShape κ.ord.ToType
      (ιObj I κ f) :=
  ⟨((relativeCellComplexιObj I κ f).transfiniteCompositionOfShape).ofLE
    (by simp)⟩

lemma llp_rlp_ιObj : I.rlp.llp (ιObj I κ f) := by
  apply I.transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp κ.ord.ToType
  apply transfiniteCompositionsOfShape_ιObj

/-- When `ιObj I κ f` is considered as a relative `I`-cell complex,
the object at the `j`th step is obtained by applying the construction
`SmallObject.functorObj`. -/
noncomputable def relativeCellComplexιObjFObjSuccIso (j : κ.ord.ToType) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    (relativeCellComplexιObj I κ f).F.obj (Order.succ j) ≅
      functorObj I.homFamily (((iterationFunctor I κ).obj j).obj (Arrow.mk f)).hom :=
  (Arrow.rightFunc ⋙ Arrow.leftFunc).mapIso
    (iterationFunctorMapSuccAppArrowIso I κ f j)

set_option backward.defeqAttrib.useBackward true in
lemma ιFunctorObj_eq (j : κ.ord.ToType) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    ιFunctorObj I.homFamily (((iterationFunctor I κ).obj j).obj (Arrow.mk f)).hom =
      (relativeCellComplexιObj I κ f).F.map (homOfLE (Order.le_succ j)) ≫
        (relativeCellComplexιObjFObjSuccIso I κ f j).hom := by
  simpa using! Arrow.leftFunc.congr_map (iterationFunctorMapSuccAppArrowIso I κ f j).hom.w

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma πFunctorObj_eq (j : κ.ord.ToType) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    πFunctorObj I.homFamily (((iterationFunctor I κ).obj j).obj (Arrow.mk f)).hom =
      (relativeCellComplexιObjFObjSuccIso I κ f j).inv ≫
      (relativeCellComplexιObj I κ f).incl.app (Order.succ j) ≫
      πObj I κ f ≫ (iterationFunctorObjObjRightIso I κ (Arrow.mk f) j).inv := by
  have h₁ := (iterationFunctorMapSuccAppArrowIso I κ f j).hom.right.w
  have h₂ := (transfiniteCompositionOfShapeSuccStructPropιIteration I κ).incl.naturality
    (homOfLE (Order.le_succ j))
  dsimp at h₁ h₂
  rw [comp_id] at h₂
  rw [← cancel_mono (iterationFunctorObjObjRightIso I κ (Arrow.mk f) j).hom,
    ← cancel_mono ((ιIteration I κ).app f).right, assoc, assoc, assoc, assoc, assoc,
    Iso.inv_hom_id_assoc, πObj_ιIteration_app_right,
    iterationFunctorObjObjRightIso_ιIteration_app_right,
    ← cancel_epi (relativeCellComplexιObjFObjSuccIso I κ f j).hom, Iso.hom_inv_id_assoc]
  dsimp [relativeCellComplexιObjFObjSuccIso,
    relativeCellComplexιObj, transfiniteCompositionOfShapeιIterationAppRight]
  simp only [reassoc_of% h₁, comp_id, comp_id, Arrow.w_mk_right, ← h₂,
    NatTrans.comp_app, Arrow.comp_right,
    iterationFunctorMapSuccAppArrowIso_hom_right_right_comp_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma hasRightLiftingProperty_πObj {A B : C} (i : A ⟶ B) (hi : I i) (f : X ⟶ Y)
    (hSmall : PreservesColimit (relativeCellComplexιObj I κ f).F
      (coyoneda.obj (Opposite.op A))) :
    HasLiftingProperty i (πObj I κ f) := ⟨by
  let _ := hSmall
  have := hasColimitsOfShape_discrete I κ
  have := hasPushouts I κ
  intro g b sq
  obtain ⟨j, t, ht⟩ := Types.jointly_surjective _
    (isColimitOfPreserves (coyoneda.obj (Opposite.op A))
      (relativeCellComplexιObj I κ f).isColimit) g
  dsimp at g b sq t ht
  obtain ⟨l, hl₁, hl₂⟩ := ιFunctorObj_extension' I.homFamily
    ((relativeCellComplexιObj I κ f).incl.app j ≫ πObj I κ f)
    ((relativeCellComplexιObj I κ f).F.map (homOfLE (Order.le_succ j)))
    ((relativeCellComplexιObj I κ f).incl.app (Order.succ j) ≫ πObj I κ f) (by simp) (Iso.refl _)
    (iterationFunctorObjObjRightIso I κ (Arrow.mk f) j).symm
    (relativeCellComplexιObjFObjSuccIso I κ f j)
    (by dsimp; rw [ιFunctorObj_eq, id_comp])
    (by dsimp; rw [πFunctorObj_eq, assoc, Iso.hom_inv_id_assoc])
    (i := ⟨i, hi⟩) t b (by rw [reassoc_of% ht, sq.w]; dsimp)
  dsimp at hl₁
  exact ⟨⟨{
    l := l ≫ (relativeCellComplexιObj I κ f).incl.app (Order.succ j)
    fac_left := by simp [reassoc_of% hl₁, ← ht]
    fac_right := by rw [assoc, hl₂]
  }⟩⟩⟩

lemma rlp_πObj
    (hSmall : ∀ {A B : C} (i : A ⟶ B), I i →
      PreservesColimit (relativeCellComplexιObj I κ f).F
        (coyoneda.obj (Opposite.op A))) : I.rlp (πObj I κ f) :=
  fun _ _ i hi ↦ hasRightLiftingProperty_πObj I κ i hi f (hSmall i hi)

end

/-- The functoriality of the intermediate object in the
factorization of the small object argument. -/
noncomputable def objMap {f g : Arrow C} (φ : f ⟶ g) : obj I κ f.hom ⟶ obj I κ g.hom :=
  ((iteration I κ).map φ).left

@[simp]
lemma objMap_id (f : Arrow C) : objMap I κ (𝟙 f) = 𝟙 _ := by
  exact (iteration I κ ⋙ Arrow.leftFunc).map_id f

@[reassoc, simp]
lemma objMap_comp {f g h : Arrow C} (φ : f ⟶ g) (ψ : g ⟶ h) :
    objMap I κ (φ ≫ ψ) = objMap I κ φ ≫ objMap I κ ψ := by
  simp only [objMap, Functor.map_comp]
  rfl

@[reassoc (attr := simp)]
lemma ιObj_naturality {f g : Arrow C} (φ : f ⟶ g) :
    ιObj I κ f.hom ≫ objMap I κ φ = φ.left ≫ ιObj I κ g.hom :=
  Arrow.leftFunc.congr_map ((ιIteration I κ).naturality φ).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma πObj_naturality {f g : Arrow C} (φ : f ⟶ g) :
    objMap I κ φ ≫ πObj I κ g.hom = πObj I κ f.hom ≫ φ.right := by
  let e₁ := asIso ((ιIteration I κ).app (Arrow.mk f.hom)).right
  let e₂ := asIso ((ιIteration I κ).app (Arrow.mk g.hom)).right
  change _ ≫ _ ≫ e₂.inv = (_ ≫ e₁.inv) ≫ _
  have h₁ := ((iteration I κ).map φ).w =≫ e₂.inv
  have h₂ : φ.right ≫ e₂.hom = e₁.hom ≫ ((iteration I κ).map φ).right :=
    ((Functor.whiskerRight (ιIteration I κ) Arrow.rightFunc).naturality φ)
  dsimp at h₁
  rw [assoc] at h₁
  apply h₁.trans
  simp only [← cancel_mono e₂.hom, assoc, e₂.inv_hom_id, h₂, e₁.inv_hom_id_assoc]
  rw [← assoc]
  apply comp_id

set_option backward.defeqAttrib.useBackward true in

/-- Raw functorial geometry: the left map is cellular, while no right-class claim is made. -/
def leftFactorizationData : FunctorialFactorizationData I.rlp.llp ⊤ where
  Z := { obj f := obj I κ f.hom, map φ := objMap I κ φ }
  i := { app f := ιObj I κ f.hom }
  p := { app f := πObj I κ f.hom }
  fac := by ext f; exact ιObj_πObj I κ f.hom
  hi f := llp_rlp_ιObj I κ f.hom
  hp _ := trivial

/-- The actual raw factorization has right lifting on the supplied source class. -/
def restrictedFactorizationData (source : C → Prop)
    (hSmall : ∀ (f : Arrow C), source f.left →
      ∀ {A B : C} (i : A ⟶ B), I i →
        PreservesColimit (relativeCellComplexιObj I κ f.hom).F
          (coyoneda.obj (Opposite.op A))) :
    SourceRestrictedFunctorialFactorizationData I.rlp.llp I.rlp source where
  Z := (leftFactorizationData I κ).Z
  i := (leftFactorizationData I κ).i
  p := (leftFactorizationData I κ).p
  fac := (leftFactorizationData I κ).fac
  hi f _ := llp_rlp_ιObj I κ f.hom
  hp f h := rlp_πObj I κ f.hom (hSmall f h)


/-- The actual canonical one-step left map on every original arrow and square. -/
def oneStepLeftArrowFunctor : Arrow C ⥤ Arrow C := by
  let : HasPushouts C := hasPushouts I κ
  let : ∀ {X Y : C} (p : X ⟶ Y),
      HasColimitsOfShape (Discrete (FunctorObjIndex I.homFamily p)) C :=
    fun {X Y} p => hasColimitsOfShape_discrete I κ X Y p
  exact
    { obj f := Arrow.mk (ιFunctorObj I.homFamily f.hom)
      map φ := Arrow.homMk φ.left (functorMap I.homFamily φ)
        (ιFunctorObj_naturality I.homFamily φ).symm
      map_id f := by
        apply Arrow.hom_ext
        · rfl
        · exact functorMap_id I.homFamily f.left
      map_comp φ ψ := by
        apply Arrow.hom_ext
        · rfl
        · dsimp
          simp only [functorMap, Arrow.comp_left]
          ext ⟨i, t, b, w⟩
          · simp
          · simp [functorMapTgt, assoc]
            congr 2; simp [assoc] }

end HomotopicalAlgebra.SemiModel.RawSmallObject

universe uC vC uD vD

namespace HomotopicalAlgebra.SemiModel

open Opposite

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]

/-- Preservation of the nonempty ordinal colimits used by the original transfer. -/
class PreservesNonemptyOrdinalColimits (U : D ⥤ C) : Prop where
  /-- The same actual nonempty well-ordered diagram keeps its colimit after U. -/
  preserves (J : Type w) [LinearOrder J] [WellFoundedLT J] [Nonempty J] :
    PreservesColimitsOfShape J U

instance (U : D ⥤ C) [PreservesNonemptyOrdinalColimits.{w} U]
    (J : Type w) [LinearOrder J] [WellFoundedLT J] [Nonempty J] :
    PreservesColimitsOfShape J U := PreservesNonemptyOrdinalColimits.preserves J

instance (U : D ⥤ C) [PreservesNonemptyOrdinalColimits.{w} U]
    (J : Type w) [LinearOrder J] [OrderBot J] [WellFoundedLT J] :
    PreservesWellOrderContinuousOfShape J U where
  preservesColimitsOfShape j hj := by
    let : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
    infer_instance

/-- Conditional relative source smallness, with the original source class at every step. -/
def UniformRelativeSourceSmallnessOnSources (P : MorphismProperty D)
    (source : D → Prop) : Prop :=
  ∀ p : P.toSet, ∃ β : Cardinal.{w},
    ∀ (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType], β < κ →
      ∀ (F : κ.ord.ToType ⥤ D) [F.IsWellOrderContinuous],
        (∀ j : κ.ord.ToType, ¬ IsMax j →
          relativeCellMaps.{w} P (F.map (homOfLE (Order.le_succ j)))) →
        (∀ j : κ.ord.ToType, ¬ IsMax j → source (F.obj j)) →
        PreservesColimit F (coyoneda.obj (op p.1.left))

namespace UniformRelativeSourceSmallnessOnSources

variable {P : MorphismProperty D} {source : D → Prop}
  (h : UniformRelativeSourceSmallnessOnSources.{w} P source)

/-- The chosen bound belongs to the actual original source arrow. -/
def sourceBound (p : P.toSet) : Cardinal.{w} := (h p).choose

/-- The bound retains the original same-diagram and permitted-source contract. -/
theorem sourceBound_spec (p : P.toSet)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (hκ : sourceBound h p < κ) (F : κ.ord.ToType ⥤ D) [F.IsWellOrderContinuous]
    (hF : ∀ j : κ.ord.ToType, ¬ IsMax j →
      relativeCellMaps.{w} P (F.map (homOfLE (Order.le_succ j))))
    (hSource : ∀ j : κ.ord.ToType, ¬ IsMax j → source (F.obj j)) :
    PreservesColimit F (coyoneda.obj (op p.1.left)) :=
  (h p).choose_spec κ hκ F hF hSource

/-- Source Hom preserves the original relative complex when every actual stage is eligible. -/
theorem preservesColimit_relativeCellComplex
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    {A B X Y : D} (i : A ⟶ B) (hi : P i)
    (hκ : sourceBound h ⟨Arrow.mk i, hi⟩ < κ) (f : X ⟶ Y)
    (c : RelativeCellComplex.{w} (fun _ : κ.ord.ToType => P.homFamily) f)
    (hSource : ∀ j, source (c.F.obj j)) :
    PreservesColimit c.F (coyoneda.obj (op A)) := by
  let : c.F.IsWellOrderContinuous := c.toTransfiniteCompositionOfShape.isWellOrderContinuous
  exact sourceBound_spec h ⟨Arrow.mk i, hi⟩ κ hκ c.F
    (fun j hj => attachCells_mem_relativeCellMaps P (c.attachCells j hj))
    (fun j _ => hSource j)

end UniformRelativeSourceSmallnessOnSources

/-- The unchanged full-I and source-restricted J ranks have a common regular upper bound. -/
theorem exists_common_source_bound
    (I J : MorphismProperty D) [I.IsSmall.{w}] [J.IsSmall.{w}]
    (source : D → Prop)
    (hI : UniformRelativeSourceSmallness.{w} I)
    (hJ : UniformRelativeSourceSmallnessOnSources.{w} J source) :
    ∃ κ : Cardinal.{w}, κ.IsRegular ∧
      (∀ i : I.toSet, UniformRelativeSourceSmallness.sourceBound hI i < κ) ∧
      (∀ j : J.toSet, UniformRelativeSourceSmallnessOnSources.sourceBound hJ j < κ) := by
  let K := I.toSet ⊕ J.toSet
  let β : K → Cardinal.{w} := fun s =>
    match s with
    | .inl i => UniformRelativeSourceSmallness.sourceBound hI i
    | .inr j => UniformRelativeSourceSmallnessOnSources.sourceBound hJ j
  let ranks : K → Type w := fun s => (β s).ord.ToType
  obtain ⟨κ, hκ, h⟩ := HasCardinalLT.exists_regular_cardinal_forall.{w} ranks
  have hb (s : K) : β s < κ := by
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, ranks, Cardinal.mk_ord_toType] using h s
  exact ⟨κ, hκ, fun i => hb (.inl i), fun j => hb (.inr j)⟩

/-- The actual free images of the original source morphism property. -/
abbrev freeGenerators (F : C ⥤ D) (P : MorphismProperty C) : MorphismProperty D := P.strictMap F

/-- The full original right lifting class is transported through the actual adjunction. -/
theorem freeGenerators_rlp (F : C ⥤ D) (U : D ⥤ C) (adj : F ⊣ U)
    (P : MorphismProperty C) :
    (freeGenerators F P).rlp = P.rlp.inverseImage U :=
  strictMap_rlp_eq_inverseImage_rlp P F U adj

variable [ModelCategory C]

/-- Weak equivalences are the actual underlying class. -/
abbrev weakClass (U : D ⥤ C) : MorphismProperty D := (weakEquivalences C).inverseImage U

/-- Fibrations are the actual underlying class. -/
abbrev fibrationClass (U : D ⥤ C) : MorphismProperty D := (fibrations C).inverseImage U

/-- Trivial fibrations retain the full underlying intersection. -/
abbrev trivialFibrationClass (U : D ⥤ C) : MorphismProperty D :=
  (trivialFibrations C).inverseImage U

/-- Cofibrations are the full left lifting class against underlying trivial fibrations. -/
abbrev cofibrationClass (U : D ⥤ C) : MorphismProperty D := (trivialFibrationClass U).llp

/-- Trivial cofibrations retain the actual cofibration/weak intersection. -/
abbrev trivialCofibrationClass (U : D ⥤ C) : MorphismProperty D :=
  cofibrationClass U ⊓ weakClass U

/-- Intrinsic source eligibility is computed from the same original initial arrow. -/
abbrev cofibrantSource [HasInitial D] (U : D ⥤ C) (X : D) : Prop :=
  IntrinsicCofibrant (cofibrationClass U) X

/-- The original free-cofibration cell objects, with no retract silently included. -/
def FreeCofibrantCellObject [HasInitial D] (F : C ⥤ D) (X : D) : Prop :=
  relativeCellMaps.{w} (freeGenerators F (cofibrations C)) (initial.to X)

/-- The derived one-step free-cell criterion at the original cell sources. -/
structure FreeCellPushoutCriterion [HasInitial D] (F : C ⥤ D) (U : D ⥤ C) : Prop where
  /-- Actual coproduct/free-cofibration attachments preserve underlying cofibrations. -/
  cofibration {X Y : D} (f : X ⟶ Y) :
    FreeCofibrantCellObject.{w} F X →
      (coproducts.{w} (freeGenerators F (cofibrations C))).pushouts f →
        cofibrations C (U.map f)
  /-- The same actual free-cell attachments preserve underlying trivial cofibrations. -/
  trivialCofibration {X Y : D} (f : X ⟶ Y) :
    FreeCofibrantCellObject.{w} F X →
      (coproducts.{w} (freeGenerators F (trivialCofibrations C))).pushouts f →
        trivialCofibrations C (U.map f)

/-- The actual free cofibration family lies in the constructed target cofibration class. -/
theorem freeCofibrations_le (F : C ⥤ D) (U : D ⥤ C) (adj : F ⊣ U) :
    freeGenerators F (cofibrations C) ≤ cofibrationClass U := by
  have h : (freeGenerators F (cofibrations C)).rlp = trivialFibrationClass U := by
    rw [freeGenerators_rlp F U adj, cofibrations_rlp]
  rw [cofibrationClass, ← h]
  exact (freeGenerators F (cofibrations C)).le_llp_rlp

/-- Original I-injectivity computes the full target cofibration class. -/
theorem cofibrationClass_eq_freeI (F : C ⥤ D) (U : D ⥤ C) (adj : F ⊣ U)
    (I : MorphismProperty C) (hI : I.rlp = trivialFibrations C) :
    cofibrationClass U = (freeGenerators F I).rlp.llp := by
  rw [freeGenerators_rlp F U adj, hI]


section CellSources

variable [HasInitial D]

/-- Every actual prefix of an initial cell history is an initial cell object. -/
theorem initialCellStage {P : MorphismProperty D}
    {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {Y : D} (f : (⊥_ D) ⟶ Y)
    (c : (coproducts.{w} P).pushouts.TransfiniteCompositionOfShape J f) (j : J) :
    relativeCellMaps.{w} P (initial.to (c.F.obj j)) := by
  let e : Arrow.mk (initial.to (c.F.obj j)) ≅
      Arrow.mk (c.F.map (homOfLE bot_le : ⊥ ⟶ j)) :=
    Arrow.isoMk c.isoBot.symm (Iso.refl _) (by
      change c.isoBot.inv ≫ c.F.map (homOfLE bot_le : ⊥ ⟶ j) =
        initial.to (c.F.obj j) ≫ 𝟙 (c.F.obj j)
      apply Subsingleton.elim)
  exact transfiniteCompositionsOfShape_le_transfiniteCompositions _ _ _
    ((c.iic j).ofArrowIso e.symm).mem

variable (F : C ⥤ D) (U : D ⥤ C)
  [hU : PreservesNonemptyOrdinalColimits.{w} U]
  (criterion : FreeCellPushoutCriterion.{w} F U)

include hU criterion

/-- The actual initial free-cofibration cell history gives an underlying cofibration. -/
theorem initialCell_underlyingCofibration (X : D)
    (hX : FreeCofibrantCellObject.{w} F X) :
    cofibrations C (U.map (initial.to X)) := by
  unfold FreeCofibrantCellObject relativeCellMaps at hX
  rw [transfiniteCompositions_iff] at hX
  obtain ⟨J, _, _, _, _, ⟨c⟩⟩ := hX
  let : (cofibrations C).IsStableUnderTransfiniteCompositionOfShape J := by
    rw [← trivialFibrations_llp]
    infer_instance
  let out : (cofibrations C).TransfiniteCompositionOfShape J (U.map (initial.to X)) :=
    { toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape.map U
      map_mem j hj := criterion.cofibration _
        (initialCellStage (initial.to X) c j) (c.map_mem j hj) }
  exact (cofibrations C).transfiniteCompositionsOfShape_le J _ out.mem

/-- Nullary initial cofibrancy and the actual cell history give underlying cofibrancy. -/
theorem initialCell_underlyingCofibrant
    (hInitial : IsCofibrant (U.obj (⊥_ D))) (X : D)
    (hX : FreeCofibrantCellObject.{w} F X) : IsCofibrant (U.obj X) := by
  rw [isCofibrant_iff, cofibration_iff] at hInitial ⊢
  rw [Subsingleton.elim (initial.to (U.obj X))
    (initial.to (U.obj (⊥_ D)) ≫ U.map (initial.to X))]
  exact (cofibrations C).comp_mem _ _ hInitial
    (initialCell_underlyingCofibration F U criterion X hX)

end CellSources


section CofibrantSources

variable [HasInitial D]
  (F : C ⥤ D) (U : D ⥤ C) (adj : F ⊣ U)
  (I : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [(freeGenerators F I).IsCardinalForSmallObjectArgument κ]

/-- The replacement keeps the actual I-cell object, both factors and the original cell history. -/
structure CofibrantCellReplacement (X : D) where
  /-- The actual intermediate object of the original free-I factorization. -/
  Z : D
  /-- The original initial free-I cell factor. -/
  i : (⊥_ D) ⟶ Z
  /-- The original underlying trivial-fibration projection. -/
  p : Z ⟶ X
  /-- These same two original factors compose to the initial arrow. -/
  fac : i ≫ p = initial.to X
  /-- The original projection has the full original free-I right lifting class. -/
  p_rlp : (freeGenerators F I).rlp p
  /-- The original cell cofans, history and endpoint cocone are retained. -/
  history : RelativeCellComplex.{w} (fun _ : κ.ord.ToType => (freeGenerators F I).homFamily) i
  /-- The same object is an actual free-cofibration cell object. -/
  isCell : FreeCofibrantCellObject.{w} F Z
  /-- The actual section obtained by the original cofibration lifting square. -/
  s : X ⟶ Z
  /-- The original section and projection make X a retract of this cell object. -/
  section_projection : s ≫ p = 𝟙 X

include adj hI in
/-- The original free-I factorization and its lifting square give an actual cell retract. -/
def cofibrantCellReplacement (X : D) (hX : cofibrantSource U X) :
    CofibrantCellReplacement F I κ X := by
  let Z := CategoryTheory.SmallObject.obj (freeGenerators F I) κ (initial.to X)
  let i : (⊥_ D) ⟶ Z := CategoryTheory.SmallObject.ιObj (freeGenerators F I) κ (initial.to X)
  let p : Z ⟶ X := CategoryTheory.SmallObject.πObj (freeGenerators F I) κ (initial.to X)
  have hp : trivialFibrationClass U p := by
    have hRight : (freeGenerators F I).rlp = trivialFibrationClass U := by
      rw [freeGenerators_rlp F U adj, hI]
    rw [← hRight]
    exact CategoryTheory.SmallObject.rlp_πObj (freeGenerators F I) κ (initial.to X)
  have hICof : I ≤ cofibrations C := by
    have h := I.le_llp_rlp
    rw [hI, trivialFibrations_llp] at h
    exact h
  have hFI : freeGenerators F I ≤ freeGenerators F (cofibrations C) :=
    monotone_strictMap F hICof
  have hCell : FreeCofibrantCellObject.{w} F Z := by
    have h : (coproducts.{w} (freeGenerators F (cofibrations C))).pushouts.transfiniteCompositionsOfShape
        κ.ord.ToType i :=
      transfiniteCompositionsOfShape_monotone κ.ord.ToType
        (pushouts_monotone (coproducts_monotone hFI)) _
        (CategoryTheory.SmallObject.transfiniteCompositionsOfShape_ιObj
          (freeGenerators F I) κ (initial.to X))
    change relativeCellMaps.{w} (freeGenerators F (cofibrations C)) (initial.to Z)
    rw [Subsingleton.elim (initial.to Z) i]
    exact transfiniteCompositionsOfShape_le_transfiniteCompositions _ _ _ h
  change (trivialFibrationClass U).llp (initial.to X) at hX
  have : HasLiftingProperty (initial.to X) p := hX p hp
  let square : CommSq i (initial.to X) p (𝟙 X) :=
    ⟨by dsimp [i, p]; simp⟩
  exact
    { Z := Z
      i := i
      p := p
      fac := CategoryTheory.SmallObject.ιObj_πObj (freeGenerators F I) κ (initial.to X)
      p_rlp := CategoryTheory.SmallObject.rlp_πObj (freeGenerators F I) κ (initial.to X)
      history := CategoryTheory.SmallObject.relativeCellComplexιObj
        (freeGenerators F I) κ (initial.to X)
      isCell := hCell
      s := square.lift
      section_projection := square.fac_right }

variable [hU : PreservesNonemptyOrdinalColimits.{w} U]
  (criterion : FreeCellPushoutCriterion.{w} F U)

include adj hI hU criterion κ in
/-- Intrinsically cofibrant objects have cofibrant underlying objects via the actual I-cell retract. -/
theorem cofibrantSource_underlying
    (hInitial : IsCofibrant (U.obj (⊥_ D))) (X : D) (hX : cofibrantSource U X) :
    IsCofibrant (U.obj X) := by
  let replacement := cofibrantCellReplacement F U adj I hI κ X hX
  have hZ : IsCofibrant (U.obj replacement.Z) :=
    initialCell_underlyingCofibrant F U criterion hInitial replacement.Z replacement.isCell
  rw [isCofibrant_iff, cofibration_iff] at hZ ⊢
  let retract : RetractArrow (initial.to (U.obj X)) (initial.to (U.obj replacement.Z)) :=
    { i := Arrow.homMk (𝟙 (⊥_ C)) (U.map replacement.s) (by
        change 𝟙 (⊥_ C) ≫ initial.to (U.obj replacement.Z) =
          initial.to (U.obj X) ≫ U.map replacement.s
        apply Subsingleton.elim)
      r := Arrow.homMk (𝟙 (⊥_ C)) (U.map replacement.p) (by
        change 𝟙 (⊥_ C) ≫ initial.to (U.obj X) =
          initial.to (U.obj replacement.Z) ≫ U.map replacement.p
        apply Subsingleton.elim)
      retract := by
        ext
        · simp
        · change U.map replacement.s ≫ U.map replacement.p = 𝟙 (U.obj X)
          rw [← U.map_comp, replacement.section_projection, U.map_id] }
  exact (cofibrations C).of_retract retract hZ


include adj hI κ in
omit hU in
/-- The original one-step cell functor transports the actual cofibrant-source retract. -/
theorem oneStep_underlying_of_cofibrantSource
    (P : MorphismProperty D) [RawSmallObject.Geometry P κ]
    (target : MorphismProperty C) [target.IsStableUnderRetracts]
    (hCell : ∀ {A B : D} (g : A ⟶ B), FreeCofibrantCellObject.{w} F A →
      (coproducts.{w} P).pushouts g → target (U.map g))
    {X Y : D} (f : X ⟶ Y) (hX : cofibrantSource U X) :
    target (U.map ((RawSmallObject.oneStepLeftArrowFunctor P κ).obj (Arrow.mk f)).hom) := by
  let replacement := cofibrantCellReplacement F U adj I hI κ X hX
  let f' : replacement.Z ⟶ Y := replacement.p ≫ f
  let retract : Retract (Arrow.mk f) (Arrow.mk f') :=
    { i := Arrow.homMk replacement.s (𝟙 Y) (by
        dsimp [f']
        rw [← assoc, replacement.section_projection, id_comp, comp_id])
      r := Arrow.homMk replacement.p (𝟙 Y) (by dsimp [f']; rw [comp_id])
      retract := by
        apply Arrow.hom_ext
        · exact replacement.section_projection
        · simp }
  let R := retract.map (RawSmallObject.oneStepLeftArrowFunctor P κ)
  let : P.IsSmall.{w} := RawSmallObject.isSmall P κ
  let : LocallySmall.{w} D := RawSmallObject.locallySmall P κ
  let : HasPushouts D := RawSmallObject.hasPushouts P κ
  let : ∀ {A B : D} (g : A ⟶ B),
      HasColimitsOfShape (Discrete (FunctorObjIndex P.homFamily g)) D :=
    fun {A B} g => RawSmallObject.hasColimitsOfShape_discrete P κ A B g
  have hStep : (coproducts.{w} P).pushouts
      ((RawSmallObject.oneStepLeftArrowFunctor P κ).obj (Arrow.mk f')).hom := by
    dsimp [RawSmallObject.oneStepLeftArrowFunctor]
    simpa only [MorphismProperty.ofHoms_homFamily] using
      (attachCellsιFunctorObjOfSmall P.homFamily f').pushouts_coproducts
  exact target.of_retract (R.map U.mapArrow)
    (hCell _ replacement.isCell hStep)

end CofibrantSources


section RawSourceStages

variable [HasInitial D] (U : D ⥤ C)

omit [HasInitial D] in
/-- One-step P-cell maps lie in the same full target left lifting class. -/
theorem cellSteps_le_cofibrationClass (P : MorphismProperty D)
    (hP : P ≤ cofibrationClass U) :
    (coproducts.{w} P).pushouts ≤ cofibrationClass U := by
  have hStep : (coproducts.{w} P).pushouts ≤ P.rlp.llp := by
    simpa only [rlp_coproducts] using (coproducts.{w} P).pushouts_le_llp_rlp
  have hClosed := antitone_llp (antitone_rlp hP)
  simpa only [cofibrationClass, llp_rlp_llp] using hStep.trans hClosed

/-- Every original stage remains intrinsically cofibrant along a genuine cofibration-cell history. -/
theorem cofibrantSource_stages
    (P : MorphismProperty D) (hP : P ≤ cofibrationClass U)
    {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {X Y : D} (f : X ⟶ Y)
    (c : RelativeCellComplex.{w} (fun _ : J => P.homFamily) f)
    (hX : cofibrantSource U X) (j : J) : cofibrantSource U (c.F.obj j) := by
  let Q := cofibrationClass U
  let : Q.IsStableUnderTransfiniteCompositionOfShape (Set.Iic j) := by
    dsimp [Q, cofibrationClass]
    infer_instance
  let cf : Q.TransfiniteCompositionOfShape J f :=
    (c.transfiniteCompositionOfShape P.homFamily).ofLE
      (by simpa only [MorphismProperty.ofHoms_homFamily] using cellSteps_le_cofibrationClass U P hP)
  have hj : Q (c.F.map (homOfLE bot_le : ⊥ ⟶ j)) :=
    Q.transfiniteCompositionsOfShape_le (Set.Iic j) _ (cf.iic j).mem
  have hi : Q c.isoBot.inv := llp_of_isIso _ _
  change Q (initial.to (c.F.obj j))
  rw [Subsingleton.elim (initial.to (c.F.obj j))
    (initial.to X ≫ c.isoBot.inv ≫ c.F.map (homOfLE bot_le : ⊥ ⟶ j))]
  exact Q.comp_mem _ _ hX (Q.comp_mem _ _ hi hj)

variable (P : MorphismProperty D) (κ : Cardinal.{w})
  [Fact κ.IsRegular] [OrderBot κ.ord.ToType] [RawSmallObject.Geometry P κ]
  [hU : PreservesNonemptyOrdinalColimits.{w} U]

include hU in
/-- The actual raw ordinal factor is underlying in a class when each permitted one-step factor is. -/
theorem rawLeft_underlyingClass
    (target : MorphismProperty C) [target.RespectsIso]
    [target.IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType]
    (hP : P ≤ cofibrationClass U)
    (hStep : ∀ {A B : D} (g : A ⟶ B), cofibrantSource U A →
      target (U.map ((RawSmallObject.oneStepLeftArrowFunctor P κ).obj (Arrow.mk g)).hom))
    {X Y : D} (f : X ⟶ Y) (hX : cofibrantSource U X) :
    target (U.map (RawSmallObject.ιObj P κ f)) := by
  let c := RawSmallObject.relativeCellComplexιObj P κ f
  let : HasPushouts D := RawSmallObject.hasPushouts P κ
  let : ∀ {A B : D} (g : A ⟶ B),
      HasColimitsOfShape (Discrete (FunctorObjIndex P.homFamily g)) D :=
    fun {A B} g => RawSmallObject.hasColimitsOfShape_discrete P κ A B g
  have hStage (j : κ.ord.ToType) : cofibrantSource U (c.F.obj j) :=
    cofibrantSource_stages U P hP _ c hX j
  have hMap (j : κ.ord.ToType) (hj : ¬ IsMax j) :
      target (U.map (c.F.map (homOfLE (Order.le_succ j)))) := by
    let g := (((RawSmallObject.iterationFunctor P κ).obj j).obj (Arrow.mk f)).hom
    have h := hStep g (hStage j)
    change target (U.map (ιFunctorObj P.homFamily g)) at h
    let e : Arrow.mk (c.F.map (homOfLE (Order.le_succ j))) ≅
        Arrow.mk (ιFunctorObj P.homFamily g) :=
      Arrow.isoMk (Iso.refl _) (RawSmallObject.relativeCellComplexιObjFObjSuccIso P κ f j) (by
        change 𝟙 _ ≫ ιFunctorObj P.homFamily g = _
        rw [id_comp]
        exact RawSmallObject.ιFunctorObj_eq P κ f j)
    exact (target.arrow_mk_iso_iff (U.mapArrow.mapIso e)).mpr h
  let out : target.TransfiniteCompositionOfShape κ.ord.ToType (U.map (RawSmallObject.ιObj P κ f)) :=
    { toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape.map U
      map_mem j hj := hMap j hj }
  exact target.transfiniteCompositionsOfShape_le _ _ out.mem

end RawSourceStages


section DerivedFactors

variable [HasInitial D]
  (F : C ⥤ D) (U : D ⥤ C) (adj : F ⊣ U)
  (I : MorphismProperty C) (hI : I.rlp = trivialFibrations C)
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [(freeGenerators F I).IsCardinalForSmallObjectArgument κ]
  [hU : PreservesNonemptyOrdinalColimits.{w} U]
  (criterion : FreeCellPushoutCriterion.{w} F U)

include F I κ in
omit [ModelCategory C] [HasInitial D] in
/-- The first full small-object record supplies only structural geometry for another small family. -/
theorem geometryFromFullI (P : MorphismProperty D) (hP : P.IsSmall.{w}) :
    RawSmallObject.Geometry P κ where
  isSmall := hP
  locallySmall := CategoryTheory.SmallObject.locallySmall (freeGenerators F I) κ
  hasPushouts := CategoryTheory.SmallObject.hasPushouts (freeGenerators F I) κ
  hasCoproducts := CategoryTheory.SmallObject.hasCoproducts (freeGenerators F I) κ
  hasIterationOfShape := CategoryTheory.SmallObject.hasIterationOfShape (freeGenerators F I) κ

include adj hI hU criterion κ in
/-- The actual raw free-I factor is underlying cofibrant for an intrinsically cofibrant source. -/
theorem rawI_underlyingCofibration {X Y : D} (f : X ⟶ Y) (hX : cofibrantSource U X) :
    letI : RawSmallObject.Geometry (freeGenerators F I) κ :=
      geometryFromFullI F I κ (freeGenerators F I) (CategoryTheory.SmallObject.isSmall _ κ)
    cofibrations C (U.map (RawSmallObject.ιObj (freeGenerators F I) κ f)) := by
  let : RawSmallObject.Geometry (freeGenerators F I) κ :=
    geometryFromFullI F I κ (freeGenerators F I) (CategoryTheory.SmallObject.isSmall _ κ)
  have hICof : I ≤ cofibrations C := by
    have h := I.le_llp_rlp
    rw [hI, trivialFibrations_llp] at h
    exact h
  have hFree : freeGenerators F I ≤ freeGenerators F (cofibrations C) :=
    monotone_strictMap F hICof
  let : (cofibrations C).IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType := by
    rw [← trivialFibrations_llp]
    infer_instance
  exact rawLeft_underlyingClass U (freeGenerators F I) κ (cofibrations C)
    (hFree.trans (freeCofibrations_le F U adj))
    (fun g hg => oneStep_underlying_of_cofibrantSource F U adj I hI κ
      (freeGenerators F I) (cofibrations C)
      (fun a ha hStep => criterion.cofibration a ha
        (pushouts_monotone (coproducts_monotone hFree) _ hStep)) g hg) f hX

include adj hI hU criterion κ in
/-- The actual raw free-J factor is underlying trivial cofibrant only on the permitted source class. -/
theorem rawJ_underlyingTrivialCofibration
    (J : MorphismProperty C) (hJ : J.rlp = fibrations C)
    (hSmallJ : (freeGenerators F J).IsSmall.{w})
    {X Y : D} (f : X ⟶ Y) (hX : cofibrantSource U X) :
    letI : RawSmallObject.Geometry (freeGenerators F J) κ :=
      geometryFromFullI F I κ (freeGenerators F J) hSmallJ
    trivialCofibrations C (U.map (RawSmallObject.ιObj (freeGenerators F J) κ f)) := by
  let : RawSmallObject.Geometry (freeGenerators F J) κ :=
    geometryFromFullI F I κ (freeGenerators F J) hSmallJ
  have hJTriv : J ≤ trivialCofibrations C := by
    have h := J.le_llp_rlp
    rw [hJ, fibrations_llp] at h
    exact h
  have hFree : freeGenerators F J ≤ freeGenerators F (trivialCofibrations C) :=
    monotone_strictMap F hJTriv
  have hBase : freeGenerators F J ≤ freeGenerators F (cofibrations C) :=
    hFree.trans (monotone_strictMap F inf_le_left)
  let : (trivialCofibrations C).IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType := by
    rw [← fibrations_llp]
    infer_instance
  exact rawLeft_underlyingClass U (freeGenerators F J) κ (trivialCofibrations C)
    (hBase.trans (freeCofibrations_le F U adj))
    (fun g hg => oneStep_underlying_of_cofibrantSource F U adj I hI κ
      (freeGenerators F J) (trivialCofibrations C)
      (fun a ha hStep => criterion.trivialCofibration a ha
        (pushouts_monotone (coproducts_monotone hFree) _ hStep)) g hg) f hX


include adj hI hU criterion κ in
/-- Conditional source smallness proves right lifting for the actual free-J projection. -/
theorem rawJ_projectionFibration
    (J : MorphismProperty C) (hJ : J.rlp = fibrations C)
    (hSmallJ : (freeGenerators F J).IsSmall.{w})
    (hInitial : IsCofibrant (U.obj (⊥_ D)))
    (hSourceJ : UniformRelativeSourceSmallnessOnSources.{w}
      (freeGenerators F J) (fun X => IsCofibrant (U.obj X)))
    (hBoundJ : ∀ p : (freeGenerators F J).toSet,
      UniformRelativeSourceSmallnessOnSources.sourceBound hSourceJ p < κ)
    {X Y : D} (f : X ⟶ Y) (hX : cofibrantSource U X) :
    letI : RawSmallObject.Geometry (freeGenerators F J) κ :=
      geometryFromFullI F I κ (freeGenerators F J) hSmallJ
    fibrationClass U (RawSmallObject.πObj (freeGenerators F J) κ f) := by
  let : RawSmallObject.Geometry (freeGenerators F J) κ :=
    geometryFromFullI F I κ (freeGenerators F J) hSmallJ
  have hJTriv : J ≤ trivialCofibrations C := by
    have h := J.le_llp_rlp
    rw [hJ, fibrations_llp] at h
    exact h
  have hP : freeGenerators F J ≤ cofibrationClass U :=
    (monotone_strictMap F (hJTriv.trans inf_le_left)).trans (freeCofibrations_le F U adj)
  let c := RawSmallObject.relativeCellComplexιObj (freeGenerators F J) κ f
  have hStages (j : κ.ord.ToType) : IsCofibrant (U.obj (c.F.obj j)) :=
    cofibrantSource_underlying F U adj I hI κ criterion hInitial _
      (cofibrantSource_stages U (freeGenerators F J) hP _ c hX j)
  have hRight : (freeGenerators F J).rlp (RawSmallObject.πObj (freeGenerators F J) κ f) :=
    RawSmallObject.rlp_πObj (freeGenerators F J) κ f
      (fun i hi => UniformRelativeSourceSmallnessOnSources.preservesColimit_relativeCellComplex
        hSourceJ κ i hi (hBoundJ ⟨Arrow.mk i, hi⟩) _ c hStages)
  rw [freeGenerators_rlp F U adj J, hJ] at hRight
  exact hRight


include adj hI κ in
omit [HasInitial D] hU in
/-- The raw first projection has the full actual underlying trivial-fibration class. -/
theorem rawI_projectionTrivialFibration {X Y : D} (f : X ⟶ Y) :
    letI : RawSmallObject.Geometry (freeGenerators F I) κ :=
      geometryFromFullI F I κ (freeGenerators F I) (CategoryTheory.SmallObject.isSmall _ κ)
    trivialFibrationClass U (RawSmallObject.πObj (freeGenerators F I) κ f) := by
  let : RawSmallObject.Geometry (freeGenerators F I) κ :=
    geometryFromFullI F I κ (freeGenerators F I) (CategoryTheory.SmallObject.isSmall _ κ)
  have h : (freeGenerators F I).rlp (RawSmallObject.πObj (freeGenerators F I) κ f) :=
    RawSmallObject.rlp_πObj (freeGenerators F I) κ f
      (fun i hi => CategoryTheory.SmallObject.preservesColimit (freeGenerators F I) κ
        i hi _ (RawSmallObject.relativeCellComplexιObj (freeGenerators F I) κ f))
  rw [freeGenerators_rlp F U adj, hI] at h
  exact h

include adj hI hU criterion κ in
/-- A cofibration with intrinsically cofibrant source is underlying a cofibration by its actual cell retract. -/
theorem cofibration_underlying_of_cofibrantSource
    {X Y : D} (f : X ⟶ Y) (hX : cofibrantSource U X) (hf : cofibrationClass U f) :
    cofibrations C (U.map f) := by
  let : RawSmallObject.Geometry (freeGenerators F I) κ :=
    geometryFromFullI F I κ (freeGenerators F I) (CategoryTheory.SmallObject.isSmall _ κ)
  let i := RawSmallObject.ιObj (freeGenerators F I) κ f
  let p := RawSmallObject.πObj (freeGenerators F I) κ f
  have hp : trivialFibrationClass U p := rawI_projectionTrivialFibration F U adj I hI κ f
  have : HasLiftingProperty f p := hf p hp
  let square : CommSq i f p (𝟙 Y) := ⟨by dsimp [i, p]; simp⟩
  let retract : RetractArrow f i :=
    { i := Arrow.homMk (𝟙 X) square.lift (by simp)
      r := Arrow.homMk (𝟙 X) p (by dsimp [i, p]; simp)
      retract := by
        apply Arrow.hom_ext
        · simp
        · exact square.fac_right }
  exact (cofibrations C).of_retract (retract.map U)
    (rawI_underlyingCofibration F U adj I hI κ criterion f hX)

end DerivedFactors


section SemiModelAtCardinal

variable [HasInitial D] [HasLimitsOfSize.{w, w} D] [HasColimitsOfSize.{w, w} D]
  (F : C ⥤ D) (U : D ⥤ C) (adj : F ⊣ U)
  (I J : MorphismProperty C)
  (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [(freeGenerators F I).IsCardinalForSmallObjectArgument κ]
  (hSmallJ : (freeGenerators F J).IsSmall.{w})
  [hU : PreservesNonemptyOrdinalColimits.{w} U]
  (criterion : FreeCellPushoutCriterion.{w} F U)
  (hInitial : IsCofibrant (U.obj (⊥_ D)))
  (hSourceJ : UniformRelativeSourceSmallnessOnSources.{w}
    (freeGenerators F J) (fun X => IsCofibrant (U.obj X)))
  (hBoundJ : ∀ p : (freeGenerators F J).toSet,
    UniformRelativeSourceSmallnessOnSources.sourceBound hSourceJ p < κ)

include adj hI κ in
/-- The original full free-I argument gives the unrestricted first functorial factorization. -/
def cofibrationFactorizationAtCardinal :
    FunctorialFactorizationData (cofibrationClass U) (trivialFibrationClass U) := by
  let d := CategoryTheory.SmallObject.functorialFactorizationData (freeGenerators F I) κ
  have hRight : (freeGenerators F I).rlp = trivialFibrationClass U := by
    rw [freeGenerators_rlp F U adj, hI]
  exact
    { Z := d.Z
      i := d.i
      p := d.p
      fac := d.fac
      hi f := by
        rw [cofibrationClass_eq_freeI F U adj I hI]
        exact d.hi f
      hp f := hRight ▸ d.hp f }

include adj hI hJ hSmallJ hU criterion hInitial hSourceJ hBoundJ κ in
/-- The original free-J geometry gives the other factors only with intrinsic source cofibrancy. -/
def trivialCofibrationFactorizationAtCardinal :
    SourceRestrictedFunctorialFactorizationData (trivialCofibrationClass U)
      (fibrationClass U) (cofibrantSource U) := by
  let : RawSmallObject.Geometry (freeGenerators F J) κ :=
    geometryFromFullI F I κ (freeGenerators F J) hSmallJ
  let d := RawSmallObject.leftFactorizationData (freeGenerators F J) κ
  have hRight : (freeGenerators F J).rlp = fibrationClass U := by
    rw [freeGenerators_rlp F U adj, hJ]
  exact
    { Z := d.Z
      i := d.i
      p := d.p
      fac := d.fac
      hi f hX := by
        constructor
        · have h : (fibrationClass U).llp (d.i.app f) := hRight ▸ d.hi f
          exact (antitone_llp (show trivialFibrationClass U ≤ fibrationClass U from
            fun _ _ _ hp => hp.1)) _ h
        · exact (rawJ_underlyingTrivialCofibration F U adj I hI κ criterion
            J hJ hSmallJ f.hom hX).2
      hp f hX := rawJ_projectionFibration F U adj I hI κ criterion
        J hJ hSmallJ hInitial hSourceJ hBoundJ f.hom hX }

include adj hI hJ hSmallJ hU criterion hInitial hSourceJ hBoundJ κ in
omit [HasLimitsOfSize.{w, w} D] [HasColimitsOfSize.{w, w} D] in
/-- Intrinsically cofibrant-source trivial cofibrations lift against every actual underlying fibration. -/
theorem trivialCofibration_liftingAtCardinal
    {X Y A B : D} (f : X ⟶ Y) (p : A ⟶ B)
    (hX : cofibrantSource U X) (hf : trivialCofibrationClass U f)
    (hp : fibrationClass U p) : HasLiftingProperty f p := by
  let : RawSmallObject.Geometry (freeGenerators F J) κ :=
    geometryFromFullI F I κ (freeGenerators F J) hSmallJ
  let d := trivialCofibrationFactorizationAtCardinal F U adj I J hI hJ κ
    hSmallJ criterion hInitial hSourceJ hBoundJ
  let : (weakClass U).HasTwoOutOfThreeProperty := inferInstance
  have hi := d.hi (Arrow.mk f) hX
  have hqFib := d.hp (Arrow.mk f) hX
  have hqWeak : weakClass U (d.p.app (Arrow.mk f)) :=
    (weakClass U).of_precomp (d.i.app (Arrow.mk f)) (d.p.app (Arrow.mk f)) hi.2
      (by rw [d.fac_app]; exact hf.2)
  have hq : trivialFibrationClass U (d.p.app (Arrow.mk f)) := ⟨hqFib, hqWeak⟩
  have : HasLiftingProperty f (d.p.app (Arrow.mk f)) := hf.1 _ hq
  let square : CommSq (d.i.app (Arrow.mk f)) f (d.p.app (Arrow.mk f)) (𝟙 Y) :=
    ⟨by simp [d.fac_app]⟩
  let retract : RetractArrow f (d.i.app (Arrow.mk f)) :=
    { i := Arrow.homMk (𝟙 X) square.lift (by simp)
      r := Arrow.homMk (𝟙 X) (d.p.app (Arrow.mk f)) (by simp)
      retract := by
        apply Arrow.hom_ext
        · simp
        · exact square.fac_right }
  have hLeft : (fibrationClass U).llp (d.i.app (Arrow.mk f)) := by
    have h := RawSmallObject.llp_rlp_ιObj (freeGenerators F J) κ f
    rw [freeGenerators_rlp F U adj, hJ] at h
    exact h
  let : HasLiftingProperty (d.i.app (Arrow.mk f)) p := hLeft p hp
  exact retract.leftLiftingProperty p

include adj hI hJ hSmallJ hU criterion hInitial hSourceJ hBoundJ κ in
/-- The actual primitive source criterion and two original source-smallness arguments construct the semi-model. -/
def semiModelCategoryAtCardinal : SemiModelCategoryData.{w} D := by
  have hIRight : (freeGenerators F I).rlp = trivialFibrationClass U := by
    rw [freeGenerators_rlp F U adj, hI]
  have hJRight : (freeGenerators F J).rlp = fibrationClass U := by
    rw [freeGenerators_rlp F U adj, hJ]
  exact
    { complete := inferInstance
      cocomplete := inferInstance
      weakEquivalences := weakClass U
      fibrations := fibrationClass U
      cofibrations := cofibrationClass U
      weak_twoOutOfThree := inferInstance
      weak_retracts := inferInstance
      fibration_retracts := inferInstance
      cofibration_eq_llp := rfl
      cofibrationFactorization := cofibrationFactorizationAtCardinal F U adj I hI κ
      trivialCofibration_lifting := fun f p hX hf hp =>
        trivialCofibration_liftingAtCardinal F U adj I J hI hJ κ hSmallJ
          criterion hInitial hSourceJ hBoundJ f p hX hf hp
      trivialCofibrationFactorization := trivialCofibrationFactorizationAtCardinal
        F U adj I J hI hJ κ hSmallJ criterion hInitial hSourceJ hBoundJ
      fibration_pullbacks := by rw [← hJRight]; infer_instance
      trivialFibration_pullbacks := by
        change (trivialFibrationClass U).IsStableUnderBaseChange
        rw [← hIRight]
        infer_instance }

end SemiModelAtCardinal


section UniformTransfer

variable [HasInitial D]

/-- Full cofibrant-generation data for the actual semi-model, retaining both original source contracts. -/
structure CofibrantlyGeneratedSemiModelTransfer (F : C ⥤ D) (U : D ⥤ C)
    (I J : MorphismProperty C)
    (hSourceI : UniformRelativeSourceSmallness.{w} (freeGenerators F I))
    (hSourceJ : UniformRelativeSourceSmallnessOnSources.{w}
      (freeGenerators F J) (fun X => IsCofibrant (U.obj X))) where
  /-- The common regular cardinal derived from the original I/J source bounds. -/
  cardinal : Cardinal.{w}
  /-- The retained regularity dictionary of that same cardinal. -/
  regular : Fact cardinal.IsRegular
  /-- The retained bottom of its actual original ordinal. -/
  orderBot : OrderBot cardinal.ord.ToType
  /-- Every original free-I source bound lies strictly below that cardinal. -/
  sourceI_bounds : ∀ p : (freeGenerators F I).toSet,
    UniformRelativeSourceSmallness.sourceBound hSourceI p < cardinal
  /-- Every original conditional free-J source bound lies below that same cardinal. -/
  sourceJ_bounds : ∀ p : (freeGenerators F J).toSet,
    UniformRelativeSourceSmallnessOnSources.sourceBound hSourceJ p < cardinal
  /-- The unchanged free-I family retains all six full small-object fields. -/
  I_smallObject : letI := regular; letI := orderBot;
    (freeGenerators F I).IsCardinalForSmallObjectArgument cardinal
  /-- The constructed complete semi-model data on the original carrier. -/
  semiModel : SemiModelCategoryData.{w} D
  /-- Its weak equivalences are exactly the original underlying class. -/
  weak_eq : semiModel.weakEquivalences = weakClass U
  /-- Its fibrations are exactly the original underlying class. -/
  fibrations_eq : semiModel.fibrations = fibrationClass U
  /-- Its cofibrations are the full actual left lifting class against underlying trivial fibrations. -/
  cofibrations_eq : semiModel.cofibrations = cofibrationClass U
  /-- The original free-I family detects all trivial fibrations. -/
  I_rlp : (freeGenerators F I).rlp = semiModel.trivialFibrations
  /-- The original free-J family detects all fibrations. -/
  J_rlp : (freeGenerators F J).rlp = semiModel.fibrations
  /-- Intrinsically cofibrant objects have cofibrant underlying objects. -/
  underlyingCofibrant (X : D) : semiModel.IsCofibrant X → IsCofibrant (U.obj X)
  /-- Actual cofibrations with intrinsically cofibrant source are underlying cofibrations. -/
  underlyingCofibration {X Y : D} (f : X ⟶ Y) :
    semiModel.IsCofibrant X → semiModel.cofibrations f → cofibrations C (U.map f)

variable [HasLimitsOfSize.{w, w} D] [HasColimitsOfSize.{w, w} D] [LocallySmall.{w} D]
  (F : C ⥤ D) (U : D ⥤ C) (adj : F ⊣ U)
  (I J : MorphismProperty C) [I.IsSmall.{w}] [J.IsSmall.{w}]
  (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
  [hU : PreservesNonemptyOrdinalColimits.{w} U]
  (criterion : FreeCellPushoutCriterion.{w} F U)
  (hInitial : IsCofibrant (U.obj (⊥_ D)))
  (hSourceI : UniformRelativeSourceSmallness.{w} (freeGenerators F I))
  (hSourceJ : UniformRelativeSourceSmallnessOnSources.{w}
    (freeGenerators F J) (fun X => IsCofibrant (U.obj X)))

include adj hI hJ hU criterion hInitial hSourceI hSourceJ in
/-- Original relative smallness and the derived free-cell criterion construct the complete
cofibrantly generated semi-model. -/
def cofibrantlyGeneratedSemiModelTransfer :
    CofibrantlyGeneratedSemiModelTransfer F U I J hSourceI hSourceJ := by
  apply Classical.choice
  let : (freeGenerators F I).IsSmall.{w} := IsSmall.strictMap (inferInstance : I.IsSmall.{w}) F
  let : (freeGenerators F J).IsSmall.{w} := IsSmall.strictMap (inferInstance : J.IsSmall.{w}) F
  obtain ⟨κ, hκ, hIκ, hJκ⟩ := exists_common_source_bound
    (freeGenerators F I) (freeGenerators F J) (fun X => IsCofibrant (U.obj X)) hSourceI hSourceJ
  let : Fact κ.IsRegular := ⟨hκ⟩
  let : Nonempty κ.ord.ToType := Cardinal.nonempty_ord_toType hκ.ne_zero
  let bottom : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot κ.ord.ToType
  let : OrderBot κ.ord.ToType := bottom
  let : (freeGenerators F I).IsCardinalForSmallObjectArgument κ :=
    isCardinalForSmallObjectArgument_of_uniform_bounds (freeGenerators F I) hSourceI κ hIκ
  let model := semiModelCategoryAtCardinal F U adj I J hI hJ κ
    (inferInstance : (freeGenerators F J).IsSmall.{w}) criterion hInitial hSourceJ hJκ
  exact ⟨
    { cardinal := κ
      regular := inferInstance
      orderBot := bottom
      sourceI_bounds := hIκ
      sourceJ_bounds := hJκ
      I_smallObject := inferInstance
      semiModel := model
      weak_eq := rfl
      fibrations_eq := rfl
      cofibrations_eq := rfl
      I_rlp := by
        change (freeGenerators F I).rlp = trivialFibrationClass U
        rw [freeGenerators_rlp F U adj, hI]
      J_rlp := by
        change (freeGenerators F J).rlp = fibrationClass U
        rw [freeGenerators_rlp F U adj, hJ]
      underlyingCofibrant X hX := cofibrantSource_underlying F U adj I hI κ
        criterion hInitial X hX
      underlyingCofibration f hX hf := cofibration_underlying_of_cofibrantSource
        F U adj I hI κ criterion f hX hf }⟩

end UniformTransfer

end HomotopicalAlgebra.SemiModel
