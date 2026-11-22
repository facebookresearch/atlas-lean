/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CategoricalEquivalences
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CategoricalFibrations
import MathlibExt.AlgebraicTopology.SimplicialSpace.HorizontalReedyModel
import MathlibExt.AlgebraicTopology.SimplicialSpace.RelativeBoundaryMatching

/-!
# Rows and pullback powers of simplicial spaces

This file gives the model-independent row API used in Joyal--Tierney,
Lemmas 4.3--4.4.  It retains the original simplicial-space and simplicial-set
maps:

* `rowFunctor n` is evaluation at inner degree `n`;
* `rowZeroTo n` is induced by the unique map `[n] ⟶ [0]`;
* `rowPowerFunctor K` is the actual inner mapping object out of the
  discrete-inner copy of `K` into the canonical transpose, hence the right
  division `X / K` rather than the left division `K \ X`;
* `rowPullbackHom v f` is the genuine Leibniz pullback-Hom map
  `⟨f / v⟩`.

Categorical constancy and rowwise categorical equivalences are defined
without selecting either the horizontal or Rezk model.  The final
Joyal--Tierney fibration and localization assertions belong in later files.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite MorphismProperty
open scoped Simplicial SimplicialSpace.Inner

namespace SimplicialSpace

/-- Evaluation of a simplicial space at inner degree `n`, retaining the
outer simplicial-set coordinate. -/
abbrev rowFunctor (n : ℕ) : SimplicialSpace.{u} ⥤ SSet.{u} :=
  HorizontalModel.transposeSpaceEquivalence.{u}.functor ⋙ forget.{u} ⋙
    (evaluation SimplexCategoryᵒᵖ SSet.{u}).obj
      (Opposite.op (⦋n⦌ : SimplexCategory))

/-- The row functor retains every original bidegree component. -/
theorem rowFunctor_obj_obj (n : ℕ) (X : SimplicialSpace.{u})
    (m : SimplexCategoryᵒᵖ) :
    ((rowFunctor n).obj X).obj m =
      (X.diagram.obj m).obj (Opposite.op (⦋n⦌ : SimplexCategory)) :=
  rfl

/-- The row functor map is the exact row map used by the horizontal Reedy
model. -/
theorem rowFunctor_map_eq_horizontalRowMap {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    (rowFunctor n).map f =
      HorizontalModel.horizontalRowMap f
        (Opposite.op (⦋n⦌ : SimplexCategory)) :=
  rfl

/-- The unique simplex-category map `[n] ⟶ [0]`. -/
abbrev rowToZero (n : ℕ) :
    (⦋n⦌ : SimplexCategory) ⟶ (⦋0⦌ : SimplexCategory) :=
  SimplexCategory.const (⦋n⦌ : SimplexCategory)
    (⦋0⦌ : SimplexCategory) 0

/-- The canonical map from row zero to row `n`, induced contravariantly by
the unique map `[n] ⟶ [0]`. -/
def rowZeroTo (n : ℕ) : rowFunctor.{u} 0 ⟶ rowFunctor.{u} n where
  app X := (HorizontalModel.transposeSpaceEquivalence.functor.obj X).diagram.map
    (rowToZero n).op
  naturality _ _ f :=
    ((HorizontalModel.transposeSpaceEquivalence.functor.map f).hom.naturality
      (rowToZero n).op).symm

@[simp]
theorem rowZeroTo_zero_app (X : SimplicialSpace.{u}) :
    (rowZeroTo.{u} 0).app X = 𝟙 _ := by
  change (HorizontalModel.transposeSpaceEquivalence.functor.obj X).diagram.map
      (rowToZero 0).op =
    𝟙 ((HorizontalModel.transposeSpaceEquivalence.functor.obj X).diagram.obj
      (Opposite.op (⦋0⦌ : SimplexCategory)))
  have h : (rowToZero 0).op =
      𝟙 (Opposite.op (⦋0⦌ : SimplexCategory)) := Subsingleton.elim _ _
  rw [h,
    (HorizontalModel.transposeSpaceEquivalence.functor.obj X).diagram.map_id]

/-- The canonical row map commutes with every original map of simplicial
spaces. -/
@[reassoc]
theorem rowZeroTo_naturality {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (n : ℕ) :
    (rowFunctor 0).map f ≫ (rowZeroTo n).app Y =
      (rowZeroTo n).app X ≫ (rowFunctor n).map f :=
  (rowZeroTo n).naturality f

/-- A simplicial space is categorically constant when every canonical map
from its zeroth row is a categorical equivalence. -/
def categoricallyConstant (X : SimplicialSpace.{u}) : Prop :=
  ∀ n : ℕ, SSet.categoricalEquivalences ((rowZeroTo n).app X)

/-- Every original row of a simplicial space is a quasicategory.  This is
kept separate from categorical constancy, which alone does not imply
fibrancy of the rows. -/
def rowsAreQuasicategories (X : SimplicialSpace.{u}) : Prop :=
  ∀ n : ℕ, SSet.Quasicategory ((rowFunctor n).obj X)

/-- A map is a rowwise categorical equivalence when it is a categorical
equivalence in every inner degree. -/
def rowwiseCategoricalEquivalences : MorphismProperty SimplicialSpace.{u} :=
  fun _ _ f ↦ ∀ n : ℕ,
    SSet.categoricalEquivalences ((rowFunctor n).map f)

@[simp]
theorem rowwiseCategoricalEquivalences_iff {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) :
    rowwiseCategoricalEquivalences f ↔
      ∀ n : ℕ, SSet.categoricalEquivalences ((rowFunctor n).map f) :=
  Iff.rfl

instance : rowwiseCategoricalEquivalences.ContainsIdentities where
  id_mem X := by
    change ∀ n : ℕ,
      SSet.categoricalEquivalences ((rowFunctor n).map (𝟙 X))
    intro n
    rw [(rowFunctor n).map_id]
    exact SSet.categoricalEquivalences.id_mem ((rowFunctor n).obj X)

instance : rowwiseCategoricalEquivalences.IsStableUnderComposition where
  comp_mem f g hf hg n := by
    rw [Functor.map_comp]
    exact SSet.categoricalEquivalences.comp_mem _ _ (hf n) (hg n)

instance : rowwiseCategoricalEquivalences.HasOfPostcompProperty
    rowwiseCategoricalEquivalences where
  of_postcomp f g hg hfg n := by
    apply SSet.categoricalEquivalences.of_postcomp
      ((rowFunctor n).map f) ((rowFunctor n).map g) (hg n)
    simpa only [Functor.map_comp] using hfg n

instance : rowwiseCategoricalEquivalences.HasOfPrecompProperty
    rowwiseCategoricalEquivalences where
  of_precomp f g hf hfg n := by
    apply SSet.categoricalEquivalences.of_precomp
      ((rowFunctor n).map f) ((rowFunctor n).map g) (hf n)
    simpa only [Functor.map_comp] using hfg n

instance : rowwiseCategoricalEquivalences.HasTwoOutOfThreeProperty where

instance : rowwiseCategoricalEquivalences.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) n ↦ by
      let _ : IsIso ((rowFunctor n).map f) := inferInstance
      exact SSet.categoricalEquivalences.of_isIso _)

/-- On categorically constant source and target, a map is rowwise
categorical exactly when its zeroth row is categorical. -/
theorem rowwiseCategoricalEquivalences_iff_zero_of_categoricallyConstant
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (hX : categoricallyConstant X) (hY : categoricallyConstant Y) :
    rowwiseCategoricalEquivalences f ↔
      SSet.categoricalEquivalences ((rowFunctor 0).map f) := by
  constructor
  · intro hf
    exact hf 0
  · intro hf n
    have hcomp : SSet.categoricalEquivalences
        ((rowZeroTo n).app X ≫ (rowFunctor n).map f) := by
      rw [← rowZeroTo_naturality f n]
      exact SSet.categoricalEquivalences.comp_mem _ _ hf (hY n)
    exact SSet.categoricalEquivalences.of_precomp
      ((rowZeroTo n).app X) ((rowFunctor n).map f) (hX n) hcomp

/-- The discrete-inner copy of a simplicial set, on the designated
simplicial-space carrier. -/
abbrev discreteInner (K : SSet.{u}) : SimplicialSpace.{u} :=
  ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj K)

/-- The discrete-inner copy of an original simplicial-set map. -/
abbrev discreteInnerMap {K L : SSet.{u}} (v : K ⟶ L) :
    discreteInner K ⟶ discreteInner L :=
  ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map v)

/-- The row power `X / K`, as the actual inner enriched mapping object from
the discrete-inner copy of `K` into the canonical transpose of `X`. -/
abbrev rowPowerFunctor (K : SSet.{u}) : SimplicialSpace.{u} ⥤ SSet.{u} :=
  HorizontalModel.transposeSpaceEquivalence.{u}.functor ⋙
    innerHomFunctor.{u}.obj (op (discreteInner K))

/-- Restriction `X / L ⟶ X / K` along an original map `v : K ⟶ L`. -/
abbrev rowRestriction {K L : SSet.{u}} (v : K ⟶ L)
    (X : SimplicialSpace.{u}) :
    (rowPowerFunctor L).obj X ⟶ (rowPowerFunctor K).obj X :=
  (innerHomFunctor.{u}.map (discreteInnerMap v).op).app
    (HorizontalModel.transposeSpaceEquivalence.functor.obj X)

/-- The native pullback square underlying the Joyal--Tierney map
`⟨f / v⟩`.  Its point is
`(X / K) ×_(Y / K) (Y / L)`. -/
abbrev rowPullbackHomSquare {K L : SSet.{u}} (v : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :=
  Functor.PullbackObjObj.ofHasPullback innerHomFunctor.{u}
    (discreteInnerMap v)
      (HorizontalModel.transposeSpaceEquivalence.functor.map f)

/-- The actual row pullback-Hom arrow
`X / L ⟶ (X / K) ×_(Y / K) (Y / L)`. -/
abbrev rowPullbackHom {K L : SSet.{u}} (v : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    (rowPowerFunctor L).obj X ⟶ (rowPullbackHomSquare v f).pt :=
  (rowPullbackHomSquare v f).π

/-- The complete original pullback-Hom arrow, functorial in the input
commutative square. -/
abbrev rowPullbackHomFunctor {K L : SSet.{u}} (v : K ⟶ L) :
    Arrow SimplicialSpace.{u} ⥤ Arrow SSet.{u} :=
  HorizontalModel.transposeSpaceEquivalence.{u}.functor.mapArrow ⋙
    innerHomFunctor.{u}.leibnizPullback.obj
      (op (Arrow.mk (discreteInnerMap v)))

theorem rowPullbackHomFunctor_obj_hom {K L : SSet.{u}} (v : K ⟶ L)
    (p : Arrow SimplicialSpace.{u}) :
    ((rowPullbackHomFunctor v).obj p).hom = rowPullbackHom v p.hom :=
  rfl

/-- The first projection records restriction of the source. -/
@[reassoc]
theorem rowPullbackHom_fst {K L : SSet.{u}} (v : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    rowPullbackHom v f ≫ (rowPullbackHomSquare v f).fst =
      rowRestriction v X :=
  (rowPullbackHomSquare v f).π_fst

/-- The second projection records the map on the `L`-power. -/
@[reassoc]
theorem rowPullbackHom_snd {K L : SSet.{u}} (v : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    rowPullbackHom v f ≫ (rowPullbackHomSquare v f).snd =
      (rowPowerFunctor L).map f :=
  (rowPullbackHomSquare v f).π_snd

/-- For a terminal map, choose the pullback-Hom square whose point is
literally `X / K` and whose comparison is literally restriction. -/
noncomputable abbrev rowPullbackHomTerminalSquare {K L : SSet.{u}}
    (v : K ⟶ L) (X : SimplicialSpace.{u}) :
    innerHomFunctor.{u}.PullbackObjObj (discreteInnerMap v)
      (HorizontalModel.transposeSpaceEquivalence.functor.map
        (terminal.from X)) := by
  let _ : (innerHomFunctor.{u}.obj (op (discreteInner K))).IsRightAdjoint :=
    (innerTensorHomAdjunction₂.adj (discreteInner K)).isRightAdjoint
  let _ : (innerHomFunctor.{u}.obj (op (discreteInner L))).IsRightAdjoint :=
    (innerTensorHomAdjunction₂.adj (discreteInner L)).isRightAdjoint
  let hT : IsTerminal
      (HorizontalModel.transposeSpaceEquivalence.functor.obj
        (⊤_ SimplicialSpace.{u})) :=
    (terminalIsTerminal : IsTerminal (⊤_ SimplicialSpace.{u})).isTerminalObj
      HorizontalModel.transposeSpaceEquivalence.functor _
  let hK := IsTerminal.isTerminalObj
    (innerHomFunctor.{u}.obj (op (discreteInner K))) _ hT
  let hL := IsTerminal.isTerminalObj
    (innerHomFunctor.{u}.obj (op (discreteInner L))) _ hT
  exact
    { pt := (rowPowerFunctor K).obj X
      fst := 𝟙 _
      snd := hL.from _
      isPullback := by
        apply +allowSynthFailures IsPullback.of_horiz_isIso
        · exact isIso_of_isTerminal hL hK _
        · exact ⟨hK.hom_ext _ _⟩
      π := rowRestriction v X
      π_snd := hL.hom_ext _ _ }

/-- The limit comparison from the ordinary pullback point for a terminal
map to the literal restriction target `X / K`. -/
noncomputable def rowPullbackHomTerminalPointIso {K L : SSet.{u}}
    (v : K ⟶ L) (X : SimplicialSpace.{u}) :
    (rowPullbackHomSquare v (terminal.from X)).pt ≅
      (rowPowerFunctor K).obj X :=
  (rowPullbackHomSquare v (terminal.from X)).isPullback.isoIsPullback
    _ _ (rowPullbackHomTerminalSquare v X).isPullback

/-- The terminal-point comparison retains the restriction-side
projection. -/
@[reassoc]
theorem rowPullbackHomTerminalPointIso_hom_fst {K L : SSet.{u}}
    (v : K ⟶ L) (X : SimplicialSpace.{u}) :
    (rowPullbackHomTerminalPointIso v X).hom ≫
        (rowPullbackHomTerminalSquare v X).fst =
      (rowPullbackHomSquare v (terminal.from X)).fst :=
  IsPullback.isoIsPullback_hom_fst _ _
    (rowPullbackHomSquare v (terminal.from X)).isPullback
    (rowPullbackHomTerminalSquare v X).isPullback

/-- The terminal-point comparison retains the terminal-side projection. -/
@[reassoc]
theorem rowPullbackHomTerminalPointIso_hom_snd {K L : SSet.{u}}
    (v : K ⟶ L) (X : SimplicialSpace.{u}) :
    (rowPullbackHomTerminalPointIso v X).hom ≫
        (rowPullbackHomTerminalSquare v X).snd =
      (rowPullbackHomSquare v (terminal.from X)).snd :=
  IsPullback.isoIsPullback_hom_snd _ _
    (rowPullbackHomSquare v (terminal.from X)).isPullback
    (rowPullbackHomTerminalSquare v X).isPullback

/-- The pullback-Hom of a terminal map is isomorphic, as a whole original
arrow, to the direct restriction map. -/
noncomputable def rowPullbackHomTerminalArrowIso {K L : SSet.{u}}
    (v : K ⟶ L) (X : SimplicialSpace.{u}) :
    Arrow.mk (rowPullbackHom v (terminal.from X)) ≅
      Arrow.mk (rowRestriction v X) :=
  Arrow.isoMk (Iso.refl _) (rowPullbackHomTerminalPointIso v X) (by
    change (rowPullbackHomTerminalSquare v X).π =
      (rowPullbackHomSquare v (terminal.from X)).π ≫
        (rowPullbackHomTerminalPointIso v X).hom
    symm
    apply (rowPullbackHomTerminalSquare v X).isPullback.hom_ext
    · rw [Category.assoc,
        rowPullbackHomTerminalPointIso_hom_fst,
        (rowPullbackHomSquare v (terminal.from X)).π_fst,
        (rowPullbackHomTerminalSquare v X).π_fst]
    · rw [Category.assoc,
        rowPullbackHomTerminalPointIso_hom_snd,
        (rowPullbackHomSquare v (terminal.from X)).π_snd,
        (rowPullbackHomTerminalSquare v X).π_snd])

/-- Every pullback-Hom restriction along a monomorphism is a genuine
categorical fibration.  This is the model-independent conclusion shape of
Joyal--Tierney Lemma 4.3. -/
def hasCategoricalRowPullbackHom {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) : Prop :=
  ∀ (K L : SSet.{u}) (v : K ⟶ L), monomorphisms SSet.{u} v →
    SSet.categoricalFibrations (rowPullbackHom v f)

/-- The enriched Yoneda isomorphism from the power by `Δ[n]` to row `n`. -/
abbrev rowRepresentableIso (n : ℕ) (X : SimplicialSpace.{u}) :
    (rowPowerFunctor (Δ[n] : SSet.{u})).obj X ≅
      (rowFunctor n).obj X :=
  SSet.Rezk.pointwiseYonedaIso n
    (HorizontalModel.transposeSpaceEquivalence.functor.obj X).diagram

/-- Restriction along the standard-simplex map induced by `[n] ⟶ [0]`
is the canonical zero-to-`n` row map under enriched Yoneda. -/
@[reassoc]
theorem rowRestriction_const_toZero (n : ℕ) (X : SimplicialSpace.{u}) :
    rowRestriction (SSet.stdSimplex.map (rowToZero n)) X ≫
        (rowRepresentableIso n X).hom =
      (rowRepresentableIso 0 X).hom ≫ (rowZeroTo n).app X :=
  SSet.Rezk.pointwiseYonedaIso_naturality_index (rowToZero n)
    (HorizontalModel.transposeSpaceEquivalence.functor.obj X).diagram

/-- The direct row matching map `X / Δ[n] ⟶ X / ∂Δ[n]`. -/
abbrev rowMatchingMap (n : ℕ) (X : SimplicialSpace.{u}) :
    (rowPowerFunctor (Δ[n] : SSet.{u})).obj X ⟶
      (rowPowerFunctor (SSet.boundary.{u} n : SSet.{u})).obj X :=
  (innerHomFunctor.map
    (ReedyGeneratingFamilies.outerBoundaryMap.{u} n).op).app
      (HorizontalModel.transposeSpaceEquivalence.functor.obj X)

/-- Every direct row matching map is a genuine categorical fibration. -/
def rowMatchingCategoricalFibrations (X : SimplicialSpace.{u}) : Prop :=
  ∀ n : ℕ, SSet.categoricalFibrations (rowMatchingMap n X)

/-- Boundary pullback–Hom is naturally the relative matching arrow of the
transposed horizontal diagram. -/
def rowRelativeMatchingNatIso (n : ℕ) :
    rowPullbackHomFunctor.{u} (SSet.boundary.{u} n).ι ≅
      HorizontalModel.transposeSpaceEquivalence.{u}.functor.mapArrow ⋙
        (forget.{u}.mapArrow ⋙
          SimplicialObject.relativeMatchingMapArrowFunctor n) :=
  Functor.isoWhiskerLeft
    HorizontalModel.transposeSpaceEquivalence.functor.mapArrow
      (relativeBoundaryMatchingArrowIso n)

/-- For every original arrow, its boundary pullback–Hom is isomorphic as a
whole arrow to the genuine horizontal relative matching map. -/
def rowRelativeMatchingArrowIso (n : ℕ) (p : Arrow SimplicialSpace.{u}) :
    Arrow.mk (rowPullbackHom (SSet.boundary.{u} n).ι p.hom) ≅
      Arrow.mk (HorizontalModel.horizontalRelativeMatchingMap p.hom n) :=
  (rowRelativeMatchingNatIso n).app p

/-- The direct row matching map is the original absolute matching map under
the enriched Yoneda and boundary-matching isomorphisms. -/
def rowMatchingArrowIso (n : ℕ) (X : SimplicialSpace.{u}) :
    Arrow.mk (rowMatchingMap n X) ≅
      Arrow.mk (SimplicialObject.matchingMap
        (HorizontalModel.transposeSpaceEquivalence.functor.obj X).diagram n) :=
  Arrow.isoMk (rowRepresentableIso n X)
    ((boundaryMatchingIso n).app
      (HorizontalModel.transposeSpaceEquivalence.functor.obj X))
    (boundaryMatchingIso_boundary n
      (HorizontalModel.transposeSpaceEquivalence.functor.obj X)).symm

@[simp]
theorem rowMatchingArrowIso_hom_left (n : ℕ) (X : SimplicialSpace.{u}) :
    (rowMatchingArrowIso n X).hom.left = (rowRepresentableIso n X).hom :=
  rfl

@[simp]
theorem rowMatchingArrowIso_hom_right (n : ℕ) (X : SimplicialSpace.{u}) :
    (rowMatchingArrowIso n X).hom.right =
      ((boundaryMatchingIso n).app
        (HorizontalModel.transposeSpaceEquivalence.functor.obj X)).hom :=
  rfl

end SimplicialSpace
