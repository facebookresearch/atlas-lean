/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.CellularLocalizationFactorizations
import MathlibExt.AlgebraicTopology.ModelCategory.CellularLocalizingFamilies
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantSpanReplacement
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenFrameHomComplex
import MathlibExt.AlgebraicTopology.ModelCategory.UnderOverProperQuillen
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.OriginalLocalMappingTests
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import MathlibExt.CategoryTheory.MorphismProperty.CoproductClosure

/-!
# Original generic local-equivalence attachment calculus

The right function complex is formed from the original coefficient Hom
functions and the actual original generated right frame. Its source maps
take the caller's original pushout to an actual simplicial pullback.
The genuine frame fibration and cofibrant-source comparison give the
derived local weak test on the source cofibrant replacements.

This receiving module retains the conventional format of the generic
continuous/projective source calculus used for full ordinal comparisons.
-/

set_option autoImplicit false

noncomputable section

universe w wS u v vJ

open CategoryTheory Limits MorphismProperty Opposite
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CellularLocalEquivalenceClosure

open QuillenFrameHomComplex GeneratedFramings CellularLocalizationFactorizations

section OriginalHom

variable {C : Type u} [Category.{v} C]

/-- The same original right coefficient-Hom functor at a fixed actual simplicial object. -/
def rawRightFunctor (B : SimplicialObject C) : Cᵒᵖ ⥤ SSet.{v} :=
  (CosimplicialObject.const C).op ⋙ ResolutionHomComplex.bifunctor ⋙
    (evaluation (SimplicialObject C) SSet.{v}).obj B

/-- Every original source arrow is the same original right-complex precomposition. -/
theorem rawRightFunctor_map {X X' : C} (f : X ⟶ X') (B : SimplicialObject C) :
    (rawRightFunctor B).map f.op = rightPrecomp f B := rfl

/-- Every actual original pushout is sent to its full original coefficient-Hom pullback. -/
theorem rawHom_isPullback {A B X Y : C} {f : A ⟶ B} {i : A ⟶ X}
    {p : B ⟶ Y} {q : X ⟶ Y} (sq : IsPushout f i p q) (Z : SimplicialObject C) :
    IsPullback (rightPrecomp p Z) (rightPrecomp q Z) (rightPrecomp f Z) (rightPrecomp i Z) := by
  apply IsPullback.of_forall_isPullback_app
  intro n
  change IsPullback ((yoneda.obj (Z.obj n)).map p.op) ((yoneda.obj (Z.obj n)).map q.op)
    ((yoneda.obj (Z.obj n)).map f.op) ((yoneda.obj (Z.obj n)).map i.op)
  exact sq.op.flip.map (yoneda.obj (Z.obj n))

/-- Every supplied limiting cone is retained by the exact original right coefficient Hom. -/
def rawImageConeIsLimit {J : Type w} [Category.{vJ} J] {F : J ⥤ Cᵒᵖ}
    (B : SimplicialObject C) (c : Cone F) (hc : IsLimit c) :
    IsLimit ((rawRightFunctor B).mapCone c) := by
  apply evaluationJointlyReflectsLimits
  intro n
  change IsLimit ((yoneda.obj (B.obj n)).mapCone c)
  exact isLimitOfPreserves (yoneda.obj (B.obj n)) hc

/-- The original coefficient Hom preserves limiting cones of every actual source shape. -/
theorem rawPreservesLimitsOfShape (J : Type w) [Category.{vJ} J] (B : SimplicialObject C) :
    PreservesLimitsOfShape J (rawRightFunctor B) where
  preservesLimit {F} := { preserves := fun hc => ⟨rawImageConeIsLimit (F := F) B _ hc⟩ }

/-- Opposite transport retains the same original colimit shape and coefficient Hom maps. -/
theorem rawPreservesColimitsOfShape (J : Type w) [Category.{vJ} J] (B : SimplicialObject C) :
    PreservesColimitsOfShape J (rawRightFunctor B).rightOp := by
  let _ : PreservesLimitsOfShape Jᵒᵖ (rawRightFunctor B) := rawPreservesLimitsOfShape Jᵒᵖ B
  exact preservesColimitsOfShape_rightOp J (rawRightFunctor B)

/-- The caller's actual colimit cocone remains the original opposite right-Hom colimit cocone. -/
def rawImageCoconeIsColimit {J : Type w} [Category.{vJ} J] {F : J ⥤ C}
    (B : SimplicialObject C) (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((rawRightFunctor B).rightOp.mapCocone c) := by
  let _ : PreservesColimitsOfShape J (rawRightFunctor B).rightOp := rawPreservesColimitsOfShape J B
  exact isColimitOfPreserves (rawRightFunctor B).rightOp hc

/-- Proper original well-order colimit cocones are preserved without imposing large global product shapes. -/
theorem rawPreservesWellOrderContinuous (J : Type w) [LinearOrder J] (B : SimplicialObject C) :
    PreservesWellOrderContinuousOfShape J (rawRightFunctor B).rightOp where
  preservesColimitsOfShape j _ := rawPreservesColimitsOfShape (Set.Iio j) B

/-- Actual trivial-fibration transition tests give the original endpoint test on the full supplied chain. -/
theorem rawPrecomp_trivial_of_continuous {J : Type w} [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J] (F : J ⥤ C) [F.IsWellOrderContinuous]
    (B : SimplicialObject C) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j : J, ¬ IsMax j →
      trivialFibrations SSet.{v} (rightPrecomp (F.map (homOfLE (Order.le_succ j))) B)) :
    trivialFibrations SSet.{v} (rightPrecomp (c.ι.app ⊥) B) := by
  let _ : PreservesWellOrderContinuousOfShape J (rawRightFunctor B).rightOp :=
    rawPreservesWellOrderContinuous J B
  let H := F ⋙ (rawRightFunctor B).rightOp
  let _ : H.IsWellOrderContinuous := inferInstance
  let s := (rawRightFunctor B).rightOp.mapCocone c
  have hs : IsColimit s := rawImageCoconeIsColimit B c hc
  let _ : IsStableUnderTransfiniteComposition.{w} (trivialCofibrations SSet.{v}ᵒᵖ) := by
    rw [← fibrations_llp]
    infer_instance
  have ht : trivialCofibrations SSet.{v}ᵒᵖ (s.ι.app ⊥) := by
    apply (trivialCofibrations SSet.{v}ᵒᵖ).transfiniteCompositionsOfShape_le J
    exact ⟨{
      F := H
      isoBot := Iso.refl _
      incl := s.ι
      isColimit := hs
      fac := Category.id_comp _
      map_mem := fun j hj => by
        change trivialCofibrations SSet.{v}ᵒᵖ
          (rightPrecomp (F.map (homOfLE (Order.le_succ j))) B).op
        rw [trivialCofibrations_op]
        exact hF j hj }⟩
  change trivialCofibrations SSet.{v}ᵒᵖ (rightPrecomp (c.ι.app ⊥) B).op at ht
  rw [trivialCofibrations_op] at ht
  exact ht

end OriginalHom

section CofibrantAttachments

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) {K : Type wS} (S : K → Arrow C)

/-- The exact generic right-frame test is an actual trivial fibration at cofibrant sources. -/
theorem rawPrecomp_trivial_of_local {A B : C} [IsCofibrant A] [IsCofibrant B]
    (f : A ⟶ B) (hf : localTrivialCofibrations d S f) (Z : C)
    (hZ : generatedLocalFibrant d S Z) :
    trivialFibrations SSet.{v} (rightPrecomp f ((rightFrame d).obj Z)) := by
  let _ : Cofibration f := (cofibration_iff _).mpr hf.1
  exact (generatedPrecomp_iff_raw_trivialFibration d f Z).mp (hf.2 Z hZ)

/-- The caller's original cobase change is local-weak for cofibrant source objects. -/
theorem pushout_local_of_cofibrant {A B X Y : C} [IsCofibrant A] [IsCofibrant X]
    {f : A ⟶ B} {i : A ⟶ X} {p : B ⟶ Y} {q : X ⟶ Y}
    (sq : IsPushout f i p q) (hf : localTrivialCofibrations d S f) :
    localTrivialCofibrations d S q := by
  let _ : Cofibration f := (cofibration_iff _).mpr hf.1
  let _ : IsCofibrant B := isCofibrant_of_cofibration f
  have hq : cofibrations C q := (cofibrations C).of_isPushout sq.flip hf.1
  let _ : Cofibration q := (cofibration_iff _).mpr hq
  let _ : IsCofibrant Y := isCofibrant_of_cofibration q
  refine ⟨hq, fun Z hZ => ?_⟩
  have hpull : trivialFibrations SSet.{v} (rightPrecomp q ((rightFrame d).obj Z)) :=
    (trivialFibrations SSet.{v}).of_isPullback (rawHom_isPullback sq ((rightFrame d).obj Z))
      (rawPrecomp_trivial_of_local d S f hf Z hZ)
  exact (generatedPrecomp_iff_raw_trivialFibration d q Z).mpr hpull

end CofibrantAttachments

section OriginalPushoutComparison

variable {C : Type u} [Category.{v} C] [ModelCategory C]

private theorem under_mk_cofibrant {A B : C} (f : A ⟶ B) [Cofibration f] :
    IsCofibrant (Under.mk f) := by
  let u : Under.mk (𝟙 A) ⟶ Under.mk f := Under.homMk f (by simp)
  let _ : Cofibration u := (cofibrations_under_iff A u).mpr (by
    change Cofibration f
    infer_instance)
  exact (isCofibrant_iff_of_isInitial u Under.mkIdInitial).mpr inferInstance

/-- The whole original pushout comparison is weak in a left proper base model,
even when its original source and endpoints are not cofibrant objects. -/
theorem pushoutComparison_weak_of_leftProper [IsLeftProper C]
    {A₀ B₀ X₀ A₁ B₁ X₁ : C} (f₀ : A₀ ⟶ B₀) (i₀ : A₀ ⟶ X₀)
    (f₁ : A₁ ⟶ B₁) (i₁ : A₁ ⟶ X₁)
    (a : A₀ ⟶ A₁) (b : B₀ ⟶ B₁) (x : X₀ ⟶ X₁)
    (hf : a ≫ f₁ = f₀ ≫ b) (hi : a ≫ i₁ = i₀ ≫ x)
    [Cofibration f₀] [Cofibration f₁]
    [WeakEquivalence a] [WeakEquivalence b] [WeakEquivalence x] :
    WeakEquivalence (pushout.map f₀ i₀ f₁ i₁ b x a hf.symm hi.symm) := by
  let m₁ : pushout f₀ i₀ ⟶ pushout f₀ (i₀ ≫ x) :=
    pushout.desc (pushout.inl f₀ (i₀ ≫ x)) (x ≫ pushout.inr f₀ (i₀ ≫ x))
      (by simpa only [Category.assoc] using (pushout.condition (f := f₀) (g := i₀ ≫ x)))
  have hm₁l : pushout.inl f₀ i₀ ≫ m₁ = pushout.inl f₀ (i₀ ≫ x) :=
    pushout.inl_desc _ _ _
  have hm₁r : pushout.inr f₀ i₀ ≫ m₁ = x ≫ pushout.inr f₀ (i₀ ≫ x) :=
    pushout.inr_desc _ _ _
  have houter : IsPushout f₀ (i₀ ≫ x)
      (pushout.inl f₀ i₀ ≫ m₁) (pushout.inr f₀ (i₀ ≫ x)) := by
    rw [hm₁l]
    exact IsPushout.of_hasPushout f₀ (i₀ ≫ x)
  have hm₁sq : IsPushout (pushout.inr f₀ i₀) x m₁ (pushout.inr f₀ (i₀ ≫ x)) :=
    houter.of_top hm₁r (IsPushout.of_hasPushout f₀ i₀)
  let _ : Cofibration (pushout.inr f₀ i₀) := (cofibration_iff _).mpr
    ((cofibrations C).of_isPushout (IsPushout.of_hasPushout f₀ i₀).flip (mem_cofibrations f₀))
  let _ : WeakEquivalence m₁ := IsLeftProper.weakEquivalence_of_isPushout hm₁sq
  let k := pushout.inl f₀ a
  let j := pushout.inr f₀ a
  let p : pushout f₀ a ⟶ B₁ := pushout.desc b f₁ hf.symm
  have hkp : k ≫ p = b := pushout.inl_desc _ _ _
  have hjp : j ≫ p = f₁ := pushout.inr_desc _ _ _
  let _ : WeakEquivalence k :=
    IsLeftProper.weakEquivalence_of_isPushout (IsPushout.of_hasPushout f₀ a)
  let _ : WeakEquivalence p := weakEquivalence_of_precomp_of_fac hkp
  let _ : Cofibration j := (cofibration_iff _).mpr
    ((cofibrations C).of_isPushout (IsPushout.of_hasPushout f₀ a).flip (mem_cofibrations f₀))
  let U : Under A₁ := Under.mk j
  let V : Under A₁ := Under.mk f₁
  let z : U ⟶ V := Under.homMk p hjp
  let _ : IsCofibrant U := under_mk_cofibrant j
  let _ : IsCofibrant V := under_mk_cofibrant f₁
  let _ : WeakEquivalence z := (weakEquivalences_under_iff A₁ z).mpr (by
    change WeakEquivalence p
    infer_instance)
  let _ : (Under.mapPushoutAdj i₁).IsQuillenAdjunction :=
    Under.mapPushoutAdj_isQuillenAdjunction i₁
  let u : pushout j i₁ ⟶ pushout f₁ i₁ := ((Under.pushout i₁).map z).right
  let _ : WeakEquivalence u :=
    (weakEquivalences_under_iff X₁ ((Under.pushout i₁).map z)).mp
      (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
        (adj := Under.mapPushoutAdj i₁) z)
  have hul : pushout.inl j i₁ ≫ u = p ≫ pushout.inl f₁ i₁ := by
    change pushout.inl j i₁ ≫
      pushout.desc (p ≫ pushout.inl f₁ i₁) (pushout.inr f₁ i₁) _ = _
    exact pushout.inl_desc _ _ _
  have hur : pushout.inr j i₁ ≫ u = pushout.inr f₁ i₁ := by
    change pushout.inr j i₁ ≫
      pushout.desc (p ≫ pushout.inl f₁ i₁) (pushout.inr f₁ i₁) _ = _
    exact pushout.inr_desc _ _ _
  have h₂ : IsPushout f₀ (i₀ ≫ x)
      (k ≫ pushout.inl j i₁) (pushout.inr j i₁) := by
    rw [← hi]
    exact (IsPushout.of_hasPushout f₀ a).paste_vert (IsPushout.of_hasPushout j i₁)
  let h₁ := IsPushout.of_hasPushout f₀ (i₀ ≫ x)
  let e : pushout f₀ (i₀ ≫ x) ≅ pushout j i₁ := h₁.isoIsPushout _ _ h₂
  have hel : pushout.inl f₀ (i₀ ≫ x) ≫ e.hom = k ≫ pushout.inl j i₁ :=
    h₁.inl_isoIsPushout_hom _ _ h₂
  have her : pushout.inr f₀ (i₀ ≫ x) ≫ e.hom = pushout.inr j i₁ :=
    h₁.inr_isoIsPushout_hom _ _ h₂
  have heq : m₁ ≫ e.hom ≫ u = pushout.map f₀ i₀ f₁ i₁ b x a hf.symm hi.symm := by
    apply pushout.hom_ext
    · calc
        pushout.inl f₀ i₀ ≫ (m₁ ≫ e.hom ≫ u) =
            (pushout.inl f₀ (i₀ ≫ x) ≫ e.hom) ≫ u := by
          simp only [← Category.assoc, hm₁l]
        _ = (k ≫ pushout.inl j i₁) ≫ u := by rw [hel]
        _ = b ≫ pushout.inl f₁ i₁ := by rw [Category.assoc, hul, ← Category.assoc, hkp]
        _ = pushout.inl f₀ i₀ ≫ pushout.map f₀ i₀ f₁ i₁ b x a hf.symm hi.symm :=
          (pushout.inl_desc _ _ _).symm
    · calc
        pushout.inr f₀ i₀ ≫ (m₁ ≫ e.hom ≫ u) =
            (x ≫ pushout.inr f₀ (i₀ ≫ x)) ≫ e.hom ≫ u := by
          simp only [← Category.assoc, hm₁r]
        _ = x ≫ pushout.inr j i₁ ≫ u := by
          simp only [Category.assoc]
          rw [← Category.assoc (pushout.inr f₀ (i₀ ≫ x)) e.hom u, her]
        _ = x ≫ pushout.inr f₁ i₁ := by rw [hur]
        _ = pushout.inr f₀ i₀ ≫ pushout.map f₀ i₀ f₁ i₁ b x a hf.symm hi.symm :=
          (pushout.inr_desc _ _ _).symm
  rw [← heq]
  infer_instance

end OriginalPushoutComparison

section OriginalGeneratedSpans

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open CellularLocalizingFamilies GeneratedFunctorialReplacements

/-- A whole original span is resolved by the same actual Q/I Arrow factories on both legs. -/
def generatedSpan {A B X : C} (f : A ⟶ B) (i : A ⟶ X) :
    CofibrantSpanReplacement (span f i) := by
  let F := (cellApproximation d).obj (Arrow.mk f)
  let I := (cellApproximation d).obj (Arrow.mk i)
  let Q₀ : WalkingSpan ⥤ C := span F.hom I.hom
  let q : Q₀ ⟶ span f i := spanHomMk ((counit d).app A)
    ((toOriginal d).app (Arrow.mk f)).right ((toOriginal d).app (Arrow.mk i)).right
    (toOriginal_square d (Arrow.mk f)).symm (toOriginal_square d (Arrow.mk i)).symm
  refine
    { Q := Q₀
      counit := q
      isCofibrant_zero := Q_isCofibrant d A
      cofibration_fst := ?_
      cofibration_snd := ?_
      counit_app_mem_trivialFibrations := ?_ }
  · change Cofibration F.hom
    exact (cofibration_iff _).mpr (cellApproximation_cofibration d (Arrow.mk f))
  · change Cofibration I.hom
    exact (cofibration_iff _).mpr (cellApproximation_cofibration d (Arrow.mk i))
  · rintro (_ | _ | _)
    · exact counit_trivialFibration d A
    · exact toOriginal_right_trivialFibration d (Arrow.mk f)
    · exact toOriginal_right_trivialFibration d (Arrow.mk i)

variable [IsLeftProper C] {K : Type wS} (S : K → Arrow C)

/-- Every caller's original cobase change preserves actual derived-local trivial cofibrations,
with arbitrary original endpoints and the supplied original pushout cocone. -/
theorem pushout_local {A B X Y : C} {f : A ⟶ B} {i : A ⟶ X}
    {p : B ⟶ Y} {q : X ⟶ Y} (sq : IsPushout f i p q)
    (hf : localTrivialCofibrations d S f) : localTrivialCofibrations d S q := by
  let R := generatedSpan d f i
  let f₀ := R.Q.map WalkingSpan.Hom.fst
  let i₀ := R.Q.map WalkingSpan.Hom.snd
  let a := R.counit.app WalkingSpan.zero
  let b := R.counit.app WalkingSpan.left
  let x := R.counit.app WalkingSpan.right
  let _ : IsCofibrant (R.Q.obj WalkingSpan.zero) := R.isCofibrant_zero
  let _ : Cofibration f₀ := R.cofibration_fst
  let _ : Cofibration i₀ := R.cofibration_snd
  let _ : IsCofibrant (R.Q.obj WalkingSpan.right) := isCofibrant_of_cofibration i₀
  let _ : Cofibration f := (cofibration_iff _).mpr hf.1
  let _ : WeakEquivalence a := (weakEquivalence_iff _).mpr
    (R.counit_app_mem_trivialFibrations WalkingSpan.zero).2
  let _ : WeakEquivalence b := (weakEquivalence_iff _).mpr
    (R.counit_app_mem_trivialFibrations WalkingSpan.left).2
  let _ : WeakEquivalence x := (weakEquivalence_iff _).mpr
    (R.counit_app_mem_trivialFibrations WalkingSpan.right).2
  have hf₀ : localTrivialCofibrations d S f₀ := by
    refine ⟨mem_cofibrations f₀, fun Z hZ => ?_⟩
    change IsIso (GeneratedRightMappingEnrichment.precomp d
      ((cellApproximation d).obj (Arrow.mk f)).hom Z)
    exact (nativePrecomp_iff d (Arrow.mk f) Z).mpr (hf.2 Z hZ)
  have hq₀ : localTrivialCofibrations d S (pushout.inr f₀ i₀) :=
    pushout_local_of_cofibrant d S (IsPushout.of_hasPushout f₀ i₀) hf₀
  have hF : a ≫ f = f₀ ≫ b := (R.counit.naturality WalkingSpan.Hom.fst).symm
  have hI : a ≫ i = i₀ ≫ x := (R.counit.naturality WalkingSpan.Hom.snd).symm
  let t := pushout.map f₀ i₀ f i b x a hF.symm hI.symm
  let _ : WeakEquivalence t := pushoutComparison_weak_of_leftProper f₀ i₀ f i a b x hF hI
  let canonical := IsPushout.of_hasPushout f i
  let e : pushout f i ≅ Y := canonical.isoIsPushout _ _ sq
  let t' : pushout f₀ i₀ ⟶ Y := t ≫ e.hom
  let _ : WeakEquivalence t' := inferInstanceAs (WeakEquivalence (t ≫ e.hom))
  have hq : pushout.inr f₀ i₀ ≫ t' = x ≫ q := by
    change pushout.inr f₀ i₀ ≫ (t ≫ e.hom) = x ≫ q
    rw [← Category.assoc]
    dsimp only [t, pushout.map]
    rw [pushout.inr_desc, Category.assoc, canonical.inr_isoIsPushout_hom]
  let _ : (generatedLocalEquivalences d S).HasTwoOutOfThreeProperty := weak_twoOutOfThree d S
  have hcomp : generatedLocalEquivalences d S (x ≫ q) := by
    rw [← hq]
    exact (generatedLocalEquivalences d S).comp_mem _ _ hq₀.2
      (baseWeak_le d S t' (mem_weakEquivalences t'))
  exact ⟨(cofibrations C).of_isPushout sq.flip hf.1,
    (generatedLocalEquivalences d S).of_precomp x q
      (baseWeak_le d S x (mem_weakEquivalences x)) hcomp⟩

end OriginalGeneratedSpans

section OriginalContinuousLocalChains

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) {K : Type wS} (S : K → Arrow C)
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

private def originalCofibrationChain (F : J ⥤ C) [F.IsWellOrderContinuous]
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j : J, ¬ IsMax j → localTrivialCofibrations d S
      (F.map (homOfLE (Order.le_succ j)))) :
    (cofibrations C).TransfiniteCompositionOfShape J (c.ι.app ⊥) where
  F := F
  isoBot := Iso.refl _
  incl := c.ι
  isColimit := hc
  fac := Category.id_comp _
  map_mem j hj := (hF j hj).1

/-- Full continuous local-cofibration chains are local-weak from their original cofibrant bottom. -/
theorem continuous_local_of_cofibrant (F : J ⥤ C) [F.IsWellOrderContinuous]
    [IsCofibrant (F.obj ⊥)] (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j : J, ¬ IsMax j → localTrivialCofibrations d S
      (F.map (homOfLE (Order.le_succ j)))) :
    localTrivialCofibrations d S (c.ι.app ⊥) := by
  let _ : IsStableUnderTransfiniteComposition.{w} (cofibrations C) := by
    rw [← trivialFibrations_llp]
    infer_instance
  let a := originalCofibrationChain d S F c hc hF
  have hcof : cofibrations C (c.ι.app ⊥) :=
    (cofibrations C).transfiniteCompositionsOfShape_le J _ a.mem
  have hstage (j : J) : IsCofibrant (F.obj j) := by
    let _ : Cofibration (F.map (homOfLE (bot_le : (⊥ : J) ≤ j))) :=
      (cofibration_iff _).mpr (a.mem_map _)
    exact isCofibrant_of_cofibration (F.map (homOfLE (bot_le : (⊥ : J) ≤ j)))
  let _ : Cofibration (c.ι.app ⊥) := (cofibration_iff _).mpr hcof
  let _ : IsCofibrant c.pt := isCofibrant_of_cofibration (c.ι.app ⊥)
  let i₀ : F.obj ⊥ ⟶ c.pt := c.ι.app ⊥
  let _ : Cofibration i₀ := inferInstanceAs (Cofibration (c.ι.app ⊥))
  refine ⟨hcof, fun Z hZ => ?_⟩
  have hraw (j : J) (hj : ¬ IsMax j) :
      trivialFibrations SSet.{v} (rightPrecomp (F.map (homOfLE (Order.le_succ j)))
        ((rightFrame d).obj Z)) := by
    let _ : IsCofibrant (F.obj j) := hstage j
    let _ : IsCofibrant (F.obj (Order.succ j)) := hstage (Order.succ j)
    exact rawPrecomp_trivial_of_local d S _ (hF j hj) Z hZ
  exact (generatedPrecomp_iff_raw_trivialFibration d i₀ Z).mpr
    (rawPrecomp_trivial_of_continuous F ((rightFrame d).obj Z) c hc hraw)

variable [IsLeftProper C]

/-- Every actual original continuous local-cofibration chain preserves its local weak test,
including arbitrary uncofibrant original endpoints and the caller's unchanged cocone. -/
theorem continuous_local (F : J ⥤ C) [F.IsWellOrderContinuous]
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j : J, ¬ IsMax j → localTrivialCofibrations d S
      (F.map (homOfLE (Order.le_succ j)))) :
    localTrivialCofibrations d S (c.ι.app ⊥) := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  let _ : (generatedLocalEquivalences d S).HasTwoOutOfThreeProperty := weak_twoOutOfThree d S
  let QF := OriginalRelativeMapping.continuousSource d F
  let qF := OriginalRelativeMapping.continuousCounit d F
  let _ : QF.IsWellOrderContinuous := OriginalRelativeMapping.continuousSource_continuous d F
  let _ : IsCofibrant (QF.obj ⊥) := OriginalRelativeMapping.continuousSource_cofibrant d F ⊥
  have hcF (j : J) (hj : ¬ IsMax j) : Cofibration (F.map (homOfLE (Order.le_succ j))) :=
    (cofibration_iff _).mpr (hF j hj).1
  have hq (j : J) : generatedLocalEquivalences d S (qF.app j) :=
    baseWeak_le d S _ (OriginalRelativeMapping.continuousCounit_weak d F hcF c hc j)
  have hQF (j : J) (hj : ¬ IsMax j) : localTrivialCofibrations d S
      (QF.map (homOfLE (Order.le_succ j))) := by
    refine ⟨(cofibration_iff _).mp (OriginalRelativeMapping.continuousSource_successor_cofibration d F j hj), ?_⟩
    apply (generatedLocalEquivalences d S).of_postcomp _ (qF.app (Order.succ j)) (hq _)
    rw [qF.naturality]
    exact (generatedLocalEquivalences d S).comp_mem _ _ (hq j) (hF j hj).2
  let cQ := colimit.cocone QF
  have hcQ : IsColimit cQ := colimit.isColimit QF
  let t : cQ.pt ⟶ c.pt := colimit.desc QF (Cocone.mk c.pt (qF ≫ c.ι))
  have ht (j : J) : cQ.ι.app j ≫ t = qF.app j ≫ c.ι.app j := by
    exact colimit.ι_desc _ _
  have htw : WeakEquivalence t :=
    OriginalRelativeMapping.continuousCounit_colimit_weak d F hcF cQ hcQ c hc t ht
  let _ : WeakEquivalence t := htw
  have hQLocal := continuous_local_of_cofibrant d S QF cQ hcQ hQF
  have hcomp : generatedLocalEquivalences d S (qF.app ⊥ ≫ c.ι.app ⊥) := by
    rw [← ht ⊥]
    exact (generatedLocalEquivalences d S).comp_mem _ _ hQLocal.2
      (baseWeak_le d S t (mem_weakEquivalences t))
  let _ : IsStableUnderTransfiniteComposition.{w} (cofibrations C) := by
    rw [← trivialFibrations_llp]
    infer_instance
  let a := originalCofibrationChain d S F c hc hF
  exact ⟨(cofibrations C).transfiniteCompositionsOfShape_le J _ a.mem,
    (generatedLocalEquivalences d S).of_precomp _ _ (hq ⊥) hcomp⟩

/-- Actual derived local trivial cofibrations retain original cobase-change stability. -/
theorem cobaseChange : (localTrivialCofibrations d S).IsStableUnderCobaseChange where
  of_isPushout sq hf := pushout_local d S sq.flip hf

/-- The exact actual class is closed under every original continuous well-order shape. -/
theorem transfiniteComposition : IsStableUnderTransfiniteComposition.{w}
    (localTrivialCofibrations d S) where
  isStableUnderTransfiniteCompositionOfShape O _ _ _ _ :=
    { le := by
        intro X Y f hf
        obtain ⟨t⟩ := hf
        let _ : t.F.IsWellOrderContinuous := t.isWellOrderContinuous
        have hlocal := continuous_local d S t.F (Cocone.mk Y t.incl) t.isColimit t.map_mem
        let _ : IsStableUnderTransfiniteComposition.{w} (cofibrations C) := by
          rw [← trivialFibrations_llp]
          infer_instance
        have hcof : cofibrations C f :=
          (cofibrations C).transfiniteCompositionsOfShape_le O _
            ((t.ofLE (fun _ _ _ h => h.1)).mem)
        let _ : (generatedLocalEquivalences d S).HasTwoOutOfThreeProperty := weak_twoOutOfThree d S
        have hweak : generatedLocalEquivalences d S f := by
          rw [← t.fac]
          exact (generatedLocalEquivalences d S).comp_mem _ _
            (baseWeak_le d S t.isoBot.inv (mem_weakEquivalences t.isoBot.inv)) hlocal.2
        exact ⟨hcof, hweak⟩ }

/-- Arbitrary original coproducts retain the same actual derived local weak class. -/
theorem coproducts : (localTrivialCofibrations d S).IsStableUnderCoproducts.{w} := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  let _ : (localTrivialCofibrations d S).IsStableUnderCobaseChange := cobaseChange d S
  let _ : IsStableUnderTransfiniteComposition.{w} (localTrivialCofibrations d S) :=
    transfiniteComposition d S
  exact (localTrivialCofibrations d S).isStableUnderCoproducts_of_cobase_transfinite

omit [IsLeftProper C] in
/-- Whole original Arrow retracts preserve both original cofibrations and actual local tests. -/
theorem retracts : (localTrivialCofibrations d S).IsStableUnderRetracts := by
  let _ : (generatedLocalEquivalences d S).IsStableUnderRetracts := weak_retracts d S
  change (cofibrations C ⊓ generatedLocalEquivalences d S).IsStableUnderRetracts
  infer_instance

end OriginalContinuousLocalChains

end HomotopicalAlgebra.CellularLocalEquivalenceClosure
