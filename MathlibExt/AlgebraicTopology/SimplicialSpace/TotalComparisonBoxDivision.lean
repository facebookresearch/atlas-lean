/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.TotalComparisonData
import MathlibExt.AlgebraicTopology.SimplicialSpace.BoxProduct
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Original box and division comparisons for the total adjunction

The comparison is natural in the two original simplicial sets and in the
original Joyal target. Its right comparisons are the mates of the same left
comparison, using the actual preserved adjunctions. This is Joyal–Tierney
Lemma 2.11, with the original box/product and division conventions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w

open CategoryTheory Opposite MonoidalCategory

namespace SimplicialSpace.TotalSpace

/-- Applying the actual total left adjoint to the original box bifunctor. -/
abbrev boxTotal : SSet.{u} ⥤ SSet.{u} ⥤ JoyalSSet.{u} :=
  SimplicialSpace.boxProduct.{u} ⋙
    (Functor.whiskeringRight SSet.{u} SimplicialSpace.{u} JoyalSSet.{u}).obj left.{u}

/-- The actual product of the original outer factor with the k-left inner image. -/
abbrev boxTensorTotal : SSet.{u} ⥤ SSet.{u} ⥤ JoyalSSet.{u} :=
  curriedTensor SSet.{u} ⋙
    (Functor.whiskeringLeft SSet.{u} SSet.{u} SSet.{u}).obj
      SSet.FreeGroupoidSimplex.kFunctor.{u} ⋙
    (Functor.whiskeringRight SSet.{u} SSet.{u} JoyalSSet.{u}).obj JoyalSSet.ofSSet.{u}

/-- The actual source-left division of the total right image. -/
abbrev totalLeftDivision : SSet.{u}ᵒᵖ ⥤ JoyalSSet.{u} ⥤ SSet.{u} :=
  SimplicialSpace.boxLeftDivisionFunctor.{u} ⋙
    (Functor.whiskeringLeft JoyalSSet.{u} SimplicialSpace.{u} SSet.{u}).obj right.{u}

/-- The actual k-right image of the ordinary outer function object. -/
abbrev totalLeftFunction : SSet.{u}ᵒᵖ ⥤ JoyalSSet.{u} ⥤ SSet.{u} :=
  MonoidalClosed.internalHom (C := SSet.{u}) ⋙
    (Functor.whiskeringLeft JoyalSSet.{u} SSet.{u} SSet.{u}).obj JoyalSSet.forget.{u} ⋙
    (Functor.whiskeringRight JoyalSSet.{u} SSet.{u} SSet.{u}).obj
      SSet.FreeGroupoidSimplex.kRightFunctor.{u}

/-- The actual source-right division of the total right image. -/
abbrev totalRightDivision : SSet.{u}ᵒᵖ ⥤ JoyalSSet.{u} ⥤ SSet.{u} :=
  SimplicialSpace.rowPowerBifunctor.{u} ⋙
    (Functor.whiskeringLeft JoyalSSet.{u} SimplicialSpace.{u} SSet.{u}).obj right.{u}

/-- The actual ordinary function object from the k-left inner factor. -/
abbrev totalRightFunction : SSet.{u}ᵒᵖ ⥤ JoyalSSet.{u} ⥤ SSet.{u} :=
  SSet.FreeGroupoidSimplex.kFunctor.{u}.op ⋙
    MonoidalClosed.internalHom (C := SSet.{u}) ⋙
    (Functor.whiskeringLeft JoyalSSet.{u} SSet.{u} SSet.{u}).obj JoyalSSet.forget.{u}

/-- The original fixed-outer box adjunction followed by the actual total pair. -/
def boxTotalLeftAdjunction (A : SSet.{u}) :
    boxTotal.obj A ⊣ totalLeftDivision.obj (op A) :=
  (SimplicialSpace.boxProductLeftAdjunction₂.adj A).comp adjunction.{u}

/-- The actual k/product/carrier adjunction for the same fixed outer factor. -/
def boxTensorLeftAdjunction (A : SSet.{u}) :
    boxTensorTotal.obj A ⊣ totalLeftFunction.obj (op A) :=
  ((SSet.FreeGroupoidSimplex.kAdjunction.{u}).comp (ihom.adjunction A)).comp
    JoyalSSet.equivalenceSSet.{u}.symm.toAdjunction

/-- The original fixed-inner box adjunction followed by the actual total pair. -/
def boxTotalRightAdjunction (B : SSet.{u}) :
    boxTotal.flip.obj B ⊣ totalRightDivision.obj (op B) :=
  (SimplicialSpace.boxProductRightAdjunction₂.adj B).comp adjunction.{u}

/-- The original right product order uses the actual native braiding and ihom. -/
def boxTensorRightAdjunction (B : SSet.{u}) :
    boxTensorTotal.flip.obj B ⊣ totalRightFunction.obj (op B) :=
  ((ihom.adjunction (SSet.FreeGroupoidSimplex.kFunctor.obj B)).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight _)).comp
      JoyalSSet.equivalenceSSet.{u}.symm.toAdjunction

/-- The preserved original box representables agree with the total data's literal pairs. -/
def boxRepresentableIso :
    (SSet.stdSimplex.{u}.prod SSet.stdSimplex.{u}) ⋙
      Functor.uncurry.obj SimplicialSpace.boxProduct.{u} ≅ representable.{u} := by
  refine NatIso.ofComponents (fun c => ?_) ?_
  · apply InducedCategory.isoMk
    refine NatIso.ofComponents (fun n => ?_) ?_
    · refine NatIso.ofComponents (fun m => Iso.refl _) ?_
      intro m m' f
      ext x
      change (x.1, (SSet.stdSimplex.obj c.2).map f x.2) =
        ((SSet.stdSimplex.obj c.1).map (𝟙 n) x.1, (SSet.stdSimplex.obj c.2).map f x.2)
      rw [CategoryTheory.Functor.map_id]
      rfl
    · intro n n' f
      ext m x
      change ((SSet.stdSimplex.obj c.1).map f x.1, x.2) =
        ((SSet.stdSimplex.obj c.1).map f x.1, (SSet.stdSimplex.obj c.2).map (𝟙 m) x.2)
      rw [CategoryTheory.Functor.map_id]
      rfl
  · intro c d f
    apply InducedCategory.hom_ext
    ext n m x
    rfl

private theorem isLeftKanExtension_identity {E : Type v} [Category.{w} E]
    (F : SSet.{u} ⥤ E) [Limits.PreservesColimitsOfSize.{0, u} F] :
    F.IsLeftKanExtension (𝟙 (SSet.stdSimplex.{u} ⋙ F)) := by
  let : (SSet.stdSimplex.{u}).IsDense := by
    change (uliftYoneda.{u} (C := SimplexCategory)).IsDense
    infer_instance
  let : F.PreservesLeftKanExtension SSet.stdSimplex.{u} SSet.stdSimplex.{u} := by
    infer_instance
  let : (𝟭 SSet.{u} ⋙ F).IsLeftKanExtension
      (Functor.whiskerRight (Functor.rightUnitor SSet.stdSimplex.{u}).inv F ≫
        (Functor.associator SSet.stdSimplex.{u} (𝟭 SSet.{u}) F).hom) :=
    Functor.PreservesLeftKanExtension.preserves (G := F)
      (F := SSet.stdSimplex.{u}) (L := SSet.stdSimplex.{u})
      (𝟭 SSet.{u}) (Functor.rightUnitor SSet.stdSimplex.{u}).inv
  exact Functor.isLeftKanExtension_of_iso (Functor.leftUnitor F)
    (Functor.whiskerRight (Functor.rightUnitor SSet.stdSimplex.{u}).inv F ≫
      (Functor.associator SSet.stdSimplex.{u} (𝟭 SSet.{u}) F).hom)
    (𝟙 (SSet.stdSimplex.{u} ⋙ F)) (by ext n; simp)

private instance boxTotal_preserves_colimits (A : SSet.{u}) :
    Limits.PreservesColimitsOfSize.{0, u} (boxTotal.obj A) :=
  (boxTotalLeftAdjunction A).leftAdjoint_preservesColimits

private instance boxTensorTotal_preserves_colimits (A : SSet.{u}) :
    Limits.PreservesColimitsOfSize.{0, u} (boxTensorTotal.obj A) :=
  (boxTensorLeftAdjunction A).leftAdjoint_preservesColimits

private instance boxTotal_flip_preserves_colimits (B : SSet.{u}) :
    Limits.PreservesColimitsOfSize.{0, u} (boxTotal.flip.obj B) :=
  (boxTotalRightAdjunction B).leftAdjoint_preservesColimits

private instance boxTensorTotal_flip_preserves_colimits (B : SSet.{u}) :
    Limits.PreservesColimitsOfSize.{0, u} (boxTensorTotal.flip.obj B) :=
  (boxTensorRightAdjunction B).leftAdjoint_preservesColimits

/-- The original comparison is natural in both standard-simplex parameters. -/
def boxStdBothIso :
    (SSet.stdSimplex.{u}.prod SSet.stdSimplex.{u}) ⋙ Functor.uncurry.obj boxTotal.{u} ≅
      (SSet.stdSimplex.{u}.prod SSet.stdSimplex.{u}) ⋙
        Functor.uncurry.obj boxTensorTotal.{u} := by
  let e : Functor.uncurry.obj boxTotal.{u} ≅
      Functor.uncurry.obj SimplicialSpace.boxProduct.{u} ⋙ left.{u} :=
    NatIso.ofComponents (fun x => Iso.refl _) (by
      intro x y f
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      change left.map ((SimplicialSpace.boxProduct.map f.1).app x.2) ≫
        left.map ((SimplicialSpace.boxProduct.obj y.1).map f.2) =
          left.map ((SimplicialSpace.boxProduct.map f.1).app x.2 ≫
            (SimplicialSpace.boxProduct.obj y.1).map f.2)
      exact (left.map_comp _ _).symm)
  exact Functor.isoWhiskerLeft (SSet.stdSimplex.{u}.prod SSet.stdSimplex.{u}) e ≪≫
    Functor.isoWhiskerRight boxRepresentableIso.{u} left.{u} ≪≫
    representableIso.{u} ≪≫
      Functor.isoWhiskerRight
        (NatIso.prod (Iso.refl SSet.stdSimplex.{u})
          SSet.FreeGroupoidSimplex.kRepresentableIso.{u}.symm)
        (tensor SSet.{u} ⋙ JoyalSSet.ofSSet.{u})

/-- Standard outer simplices and arbitrary original inner factors form the first family. -/
abbrev boxStdTotal : SimplexCategory ⥤ SSet.{u} ⥤ JoyalSSet.{u} :=
  SSet.stdSimplex.{u} ⋙ boxTotal.{u}

/-- The product family with the same standard outer simplices and arbitrary inner factors. -/
abbrev boxStdTensor : SimplexCategory ⥤ SSet.{u} ⥤ JoyalSSet.{u} :=
  SSet.stdSimplex.{u} ⋙ boxTensorTotal.{u}

set_option backward.isDefEq.respectTransparency false in
/-- The standard inner restriction retains every original outer operator. -/
def boxStdRestrictionIso :
    SSet.stdSimplex.{u} ⋙ boxStdTotal.{u}.flip ≅
      SSet.stdSimplex.{u} ⋙ boxStdTensor.{u}.flip := by
  refine NatIso.ofComponents (fun m => ?_) ?_
  · refine NatIso.ofComponents (fun n => boxStdBothIso.{u}.app (n, m)) ?_
    intro n n' f
    change (boxTotal.map (SSet.stdSimplex.map f)).app (SSet.stdSimplex.obj m) ≫
        boxStdBothIso.{u}.hom.app (n', m) =
      boxStdBothIso.hom.app (n, m) ≫
        (boxTensorTotal.map (SSet.stdSimplex.map f)).app (SSet.stdSimplex.obj m)
    have h := boxStdBothIso.{u}.hom.naturality
      (show (n, m) ⟶ (n', m) from (f, 𝟙 m))
    simpa only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
      CategoryTheory.Functor.prod_map, CategoryTheory.Functor.prod_obj,
      CategoryTheory.Functor.uncurry_obj_map, CategoryTheory.Functor.map_id,
      NatTrans.id_app, Category.comp_id, Category.id_comp] using h
  · intro m m' f
    ext n
    change (boxTotal.obj (SSet.stdSimplex.obj n)).map (SSet.stdSimplex.map f) ≫
        boxStdBothIso.{u}.hom.app (n, m') =
      boxStdBothIso.hom.app (n, m) ≫
        (boxTensorTotal.obj (SSet.stdSimplex.obj n)).map (SSet.stdSimplex.map f)
    have h := boxStdBothIso.{u}.hom.naturality
      (show (n, m) ⟶ (n, m') from (𝟙 n, f))
    change ((boxTotal.map (SSet.stdSimplex.map (𝟙 n))).app (SSet.stdSimplex.obj m) ≫
        (boxTotal.obj (SSet.stdSimplex.obj n)).map (SSet.stdSimplex.map f)) ≫
        boxStdBothIso.{u}.hom.app (n, m') =
      boxStdBothIso.hom.app (n, m) ≫
        ((boxTensorTotal.map (SSet.stdSimplex.map (𝟙 n))).app (SSet.stdSimplex.obj m) ≫
          (boxTensorTotal.obj (SSet.stdSimplex.obj n)).map (SSet.stdSimplex.map f)) at h
    simp only [CategoryTheory.Functor.map_id, NatTrans.id_app] at h
    exact h

private instance boxStdTotal_flip_preserves_colimits :
    Limits.PreservesColimitsOfSize.{0, u} boxStdTotal.{u}.flip := by
  apply Limits.preservesColimits_of_evaluation
  intro n
  change Limits.PreservesColimitsOfSize.{0, u}
    (boxTotal.obj (SSet.stdSimplex.obj n))
  infer_instance

private instance boxStdTensor_flip_preserves_colimits :
    Limits.PreservesColimitsOfSize.{0, u} boxStdTensor.{u}.flip := by
  apply Limits.preservesColimits_of_evaluation
  intro n
  change Limits.PreservesColimitsOfSize.{0, u}
    (boxTensorTotal.obj (SSet.stdSimplex.obj n))
  infer_instance

/-- The actual inner extension gives arbitrary B while retaining every outer n operator. -/
def boxStdIso : boxStdTotal.{u}.flip ≅ boxStdTensor.{u}.flip := by
  let : boxStdTotal.{u}.flip.IsLeftKanExtension
      (𝟙 (SSet.stdSimplex.{u} ⋙ boxStdTotal.{u}.flip)) :=
    isLeftKanExtension_identity _
  let : boxStdTensor.{u}.flip.IsLeftKanExtension
      (𝟙 (SSet.stdSimplex.{u} ⋙ boxStdTensor.{u}.flip)) :=
    isLeftKanExtension_identity _
  exact Functor.leftKanExtensionUniqueOfIso boxStdTotal.{u}.flip
    (𝟙 (SSet.stdSimplex.{u} ⋙ boxStdTotal.{u}.flip))
    boxStdRestrictionIso.{u} boxStdTensor.{u}.flip
    (𝟙 (SSet.stdSimplex.{u} ⋙ boxStdTensor.{u}.flip))

private instance boxTotal_all_preserves_colimits :
    Limits.PreservesColimitsOfSize.{0, u} boxTotal.{u} := by
  apply Limits.preservesColimits_of_evaluation
  intro B
  change Limits.PreservesColimitsOfSize.{0, u} (boxTotal.flip.obj B)
  infer_instance

private instance boxTensorTotal_all_preserves_colimits :
    Limits.PreservesColimitsOfSize.{0, u} boxTensorTotal.{u} := by
  apply Limits.preservesColimits_of_evaluation
  intro B
  change Limits.PreservesColimitsOfSize.{0, u} (boxTensorTotal.flip.obj B)
  infer_instance

/-- The first extension remains natural in the original standard outer variable. -/
def boxOuterRestrictionIso :
    SSet.stdSimplex.{u} ⋙ boxTotal.{u} ≅ SSet.stdSimplex.{u} ⋙ boxTensorTotal.{u} :=
  (Functor.flipping (C := SSet.{u}) (D := SimplexCategory) (E := JoyalSSet.{u})).functor.mapIso
    boxStdIso.{u}

/-- The full original total-box/product comparison, natural in arbitrary A and B. -/
def boxProductIso : boxTotal.{u} ≅ boxTensorTotal.{u} := by
  let : boxTotal.{u}.IsLeftKanExtension (𝟙 (SSet.stdSimplex.{u} ⋙ boxTotal.{u})) :=
    isLeftKanExtension_identity _
  let : boxTensorTotal.{u}.IsLeftKanExtension
      (𝟙 (SSet.stdSimplex.{u} ⋙ boxTensorTotal.{u})) := isLeftKanExtension_identity _
  exact Functor.leftKanExtensionUniqueOfIso boxTotal.{u}
    (𝟙 (SSet.stdSimplex.{u} ⋙ boxTotal.{u})) boxOuterRestrictionIso.{u}
    boxTensorTotal.{u} (𝟙 (SSet.stdSimplex.{u} ⋙ boxTensorTotal.{u}))

private theorem boxProductIso_std_outer (n : SimplexCategory) :
    boxProductIso.{u}.hom.app (SSet.stdSimplex.obj n) = boxOuterRestrictionIso.hom.app n := by
  let : boxTotal.{u}.IsLeftKanExtension (𝟙 (SSet.stdSimplex.{u} ⋙ boxTotal.{u})) :=
    isLeftKanExtension_identity _
  have h := congr_app (Functor.descOfIsLeftKanExtension_fac boxTotal.{u}
    (𝟙 (SSet.stdSimplex.{u} ⋙ boxTotal.{u})) boxTensorTotal.{u}
    (boxOuterRestrictionIso.hom ≫ 𝟙 _)) n
  simpa only [boxProductIso, Functor.leftKanExtensionUniqueOfIso_hom,
    NatTrans.comp_app, NatTrans.id_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id] using h

/-- On both original representables the comparison is the prescribed total/k generator
comparison. -/
theorem boxProductIso_stdSimplex (n m : SimplexCategory) :
    (boxProductIso.{u}.hom.app (SSet.stdSimplex.obj n)).app (SSet.stdSimplex.obj m) =
      boxStdBothIso.hom.app (n, m) := by
  rw [boxProductIso_std_outer]
  let : boxStdTotal.{u}.flip.IsLeftKanExtension
      (𝟙 (SSet.stdSimplex.{u} ⋙ boxStdTotal.{u}.flip)) := isLeftKanExtension_identity _
  have h := congr_app (Functor.descOfIsLeftKanExtension_fac boxStdTotal.{u}.flip
    (𝟙 (SSet.stdSimplex.{u} ⋙ boxStdTotal.{u}.flip)) boxStdTensor.{u}.flip
    (boxStdRestrictionIso.hom ≫ 𝟙 _)) m
  have h' := congr_app h n
  change (boxStdIso.hom.app (SSet.stdSimplex.obj m)).app n = boxStdBothIso.hom.app (n, m)
  simpa only [boxStdIso, Functor.leftKanExtensionUniqueOfIso_hom, boxStdRestrictionIso,
    NatIso.ofComponents_hom_app, Iso.app_hom, NatTrans.comp_app, NatTrans.id_app,
        Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id] using h'

/-- For fixed outer A the original left division comparison is the exact inverse-left mate. -/
def leftDivisionComponentIso (A : SSet.{u}) :
    totalLeftDivision.obj (op A) ≅ totalLeftFunction.obj (op A) :=
  conjugateIsoEquiv (boxTotalLeftAdjunction A) (boxTensorLeftAdjunction A)
    (boxProductIso.{u}.app A).symm

/-- For fixed inner B the original right division comparison is the same inverse-left mate. -/
def rightDivisionComponentIso (B : SSet.{u}) :
    totalRightDivision.obj (op B) ≅ totalRightFunction.obj (op B) :=
  conjugateIsoEquiv (boxTotalRightAdjunction B) (boxTensorRightAdjunction B)
    (((Functor.flipping (C := SSet.{u}) (D := SSet.{u}) (E := JoyalSSet.{u})).functor.mapIso
      boxProductIso.{u}).app B).symm

/-- The actual total-box/left-division adjunction is natural in the outer parameter. -/
def boxTotalLeftAdjunction₂ : boxTotal.{u} ⊣₂ totalLeftDivision.{u} :=
  ParametrizedAdjunction.mk' boxTotalLeftAdjunction (by
    intro A A' a B Q f
    simp only [boxTotalLeftAdjunction, Adjunction.comp_homEquiv, Equiv.trans_apply]
    change (SimplicialSpace.boxProductLeftAdjunction₂.adj A).homEquiv B (right.obj Q)
        ((adjunction.homEquiv _ Q) (left.map ((SimplicialSpace.boxProduct.map a).app B) ≫ f)) =
      (SimplicialSpace.boxProductLeftAdjunction₂.adj A').homEquiv B (right.obj Q)
        ((adjunction.homEquiv _ Q) f) ≫
          (SimplicialSpace.boxLeftDivisionFunctor.map a.op).app (right.obj Q)
    rw [adjunction.homEquiv_naturality_left]
    exact SimplicialSpace.boxProductLeftAdjunction₂.homEquiv_naturality_one a _)

/-- The actual k/tensor/carrier adjunction is natural in the same outer parameter. -/
def boxTensorLeftAdjunction₂ : boxTensorTotal.{u} ⊣₂ totalLeftFunction.{u} :=
  ParametrizedAdjunction.mk' boxTensorLeftAdjunction (by
    intro A A' a B Q f
    let j : JoyalSSet.ofSSet.{u} ⊣ JoyalSSet.forget.{u} :=
      JoyalSSet.equivalenceSSet.{u}.symm.toAdjunction
    change (SSet.FreeGroupoidSimplex.kAdjunction.homEquiv B _)
        ((ihom.adjunction A).homEquiv _ _
          ((j.homEquiv _ Q) (JoyalSSet.ofSSet.map
              (a ▷ SSet.FreeGroupoidSimplex.kFunctor.obj B) ≫ f))) =
      (SSet.FreeGroupoidSimplex.kAdjunction.homEquiv B _)
        ((ihom.adjunction A').homEquiv _ _ ((j.homEquiv _ Q) f)) ≫
          SSet.FreeGroupoidSimplex.kRightFunctor.map
            ((MonoidalClosed.internalHom.map a.op).app (JoyalSSet.forget.obj Q))
    rw [j.homEquiv_naturality_left]
    have hi := MonoidalClosed.internalHomAdjunction₂.homEquiv_naturality_one a
      ((j.homEquiv (A' ⊗ SSet.FreeGroupoidSimplex.kFunctor.obj B) Q) f)
    have hk := congrArg
      (SSet.FreeGroupoidSimplex.kAdjunction.homEquiv B
        ((ihom A).obj (JoyalSSet.forget.obj Q))) hi
    exact hk.trans (SSet.FreeGroupoidSimplex.kAdjunction.homEquiv_naturality_right _ _))

/-- The actual total-box/right-division adjunction is natural in the inner parameter. -/
def boxTotalRightAdjunction₂ : boxTotal.{u}.flip ⊣₂ totalRightDivision.{u} :=
  ParametrizedAdjunction.mk' boxTotalRightAdjunction (by
    intro B B' b A Q f
    simp only [boxTotalRightAdjunction, Adjunction.comp_homEquiv, Equiv.trans_apply]
    change (SimplicialSpace.boxProductRightAdjunction₂.adj B).homEquiv A (right.obj Q)
        ((adjunction.homEquiv _ Q) (left.map ((SimplicialSpace.boxProduct.obj A).map b) ≫ f)) =
      (SimplicialSpace.boxProductRightAdjunction₂.adj B').homEquiv A (right.obj Q)
        ((adjunction.homEquiv _ Q) f) ≫
          (SimplicialSpace.rowPowerBifunctor.map b.op).app (right.obj Q)
    rw [adjunction.homEquiv_naturality_left]
    exact SimplicialSpace.boxProductRightAdjunction₂.homEquiv_naturality_one b _)

/-- The actual right-product/function adjunction is natural in the original inner factor. -/
def boxTensorRightAdjunction₂ : boxTensorTotal.{u}.flip ⊣₂ totalRightFunction.{u} :=
  ParametrizedAdjunction.mk' boxTensorRightAdjunction (by
    intro B B' b A Q f
    let j : JoyalSSet.ofSSet.{u} ⊣ JoyalSSet.forget.{u} :=
      JoyalSSet.equivalenceSSet.{u}.symm.toAdjunction
    simp only [boxTensorRightAdjunction]
    change (ihom.adjunction (SSet.FreeGroupoidSimplex.kFunctor.obj B)).homEquiv A _
        ((β_ (SSet.FreeGroupoidSimplex.kFunctor.obj B) A).hom ≫
          (j.homEquiv _ Q)
            (JoyalSSet.ofSSet.map (A ◁ SSet.FreeGroupoidSimplex.kFunctor.map b) ≫ f)) =
      (ihom.adjunction (SSet.FreeGroupoidSimplex.kFunctor.obj B')).homEquiv A _
        ((β_ (SSet.FreeGroupoidSimplex.kFunctor.obj B') A).hom ≫ (j.homEquiv _ Q) f) ≫
          (MonoidalClosed.internalHom.map (SSet.FreeGroupoidSimplex.kFunctor.map b).op).app
            (JoyalSSet.forget.obj Q)
    rw [j.homEquiv_naturality_left]
    have hn := BraidedCategory.braiding_naturality_left
      (SSet.FreeGroupoidSimplex.kFunctor.map b) A
    have hh := congrArg
      (fun g => g ≫ (j.homEquiv _ Q) f) hn.symm
    have hi := congrArg
      ((ihom.adjunction (SSet.FreeGroupoidSimplex.kFunctor.obj B)).homEquiv A
        (JoyalSSet.forget.obj Q)) hh
    have hp := MonoidalClosed.internalHomAdjunction₂.homEquiv_naturality_one
      (SSet.FreeGroupoidSimplex.kFunctor.map b)
      ((β_ (SSet.FreeGroupoidSimplex.kFunctor.obj B') A).hom ≫ (j.homEquiv _ Q) f)
    exact hi.trans hp)

private theorem conjugate_parameter_map
    {F : SSet.{u} ⥤ SSet.{u} ⥤ JoyalSSet.{u}}
    {G : SSet.{u}ᵒᵖ ⥤ JoyalSSet.{u} ⥤ SSet.{u}}
    (adj : F ⊣₂ G) {A A' : SSet.{u}} (a : A ⟶ A') :
    conjugateEquiv (adj.adj A') (adj.adj A) (F.map a) = G.map a.op := by
  apply NatTrans.ext
  funext Q
  rw [conjugateEquiv_apply_app, ← (G.obj (op A)).map_comp,
    ← (adj.adj A).homEquiv_unit]
  calc
    _ = (adj.adj A').homEquiv _ Q ((adj.adj A').counit.app Q) ≫
        (G.map a.op).app Q := adj.homEquiv_naturality_one a _
    _ = _ := by
      rw [← (adj.adj A').homEquiv_symm_id Q]
      simp only [Equiv.apply_symm_apply, Category.id_comp]

private def parametrizedConjugateIso
    {F F' : SSet.{u} ⥤ SSet.{u} ⥤ JoyalSSet.{u}}
    {G G' : SSet.{u}ᵒᵖ ⥤ JoyalSSet.{u} ⥤ SSet.{u}}
    (adj : F ⊣₂ G) (adj' : F' ⊣₂ G') (e : F ≅ F') : G ≅ G' := by
  refine NatIso.ofComponents
    (fun A => conjugateIsoEquiv (adj.adj A.unop) (adj'.adj A.unop) (e.app A.unop).symm) ?_
  intro A A' a
  change G.map a.unop.op ≫
      conjugateEquiv (adj.adj A'.unop) (adj'.adj A'.unop) (e.inv.app A'.unop) =
    conjugateEquiv (adj.adj A.unop) (adj'.adj A.unop) (e.inv.app A.unop) ≫
      G'.map a.unop.op
  rw [← conjugate_parameter_map adj a.unop, ← conjugate_parameter_map adj' a.unop,
    conjugateEquiv_comp, conjugateEquiv_comp, e.inv.naturality]

/-- The full original left-division/function comparison, including every outer restriction. -/
def leftDivisionIso : totalLeftDivision.{u} ≅ totalLeftFunction.{u} :=
  parametrizedConjugateIso boxTotalLeftAdjunction₂ boxTensorLeftAdjunction₂ boxProductIso

/-- The full original right-division/function comparison, including every inner restriction. -/
def rightDivisionIso : totalRightDivision.{u} ≅ totalRightFunction.{u} :=
  parametrizedConjugateIso boxTotalRightAdjunction₂ boxTensorRightAdjunction₂
    ((Functor.flipping (C := SSet.{u}) (D := SSet.{u}) (E := JoyalSSet.{u})).functor.mapIso
      boxProductIso)

/-- The full left comparison uses the previously fixed exact inverse-left mate. -/
theorem leftDivisionIso_app (A : SSet.{u}) :
    leftDivisionIso.app (op A) = leftDivisionComponentIso A := rfl

/-- The full right comparison uses the previously fixed exact inverse-left mate. -/
theorem rightDivisionIso_app (B : SSet.{u}) :
    rightDivisionIso.app (op B) = rightDivisionComponentIso B := rfl

/-- The same inverse-left mate preserves the original left-division unit. -/
theorem leftDivisionComponentIso_unit (A B : SSet.{u}) :
    (boxTotalLeftAdjunction A).unit.app B ≫
      (leftDivisionComponentIso A).hom.app ((boxTotal.obj A).obj B) =
    (boxTensorLeftAdjunction A).unit.app B ≫
      (totalLeftFunction.obj (op A)).map ((boxProductIso.app A).inv.app B) :=
  unit_conjugateEquiv (boxTotalLeftAdjunction A) (boxTensorLeftAdjunction A)
    (boxProductIso.app A).inv B

/-- The same inverse-left mate preserves the original left-division counit. -/
theorem leftDivisionComponentIso_counit (A : SSet.{u}) (Q : JoyalSSet.{u}) :
    (boxTensorTotal.obj A).map ((leftDivisionComponentIso A).hom.app Q) ≫
      (boxTensorLeftAdjunction A).counit.app Q =
    (boxProductIso.app A).inv.app ((totalLeftDivision.obj (op A)).obj Q) ≫
      (boxTotalLeftAdjunction A).counit.app Q :=
  conjugateEquiv_counit (boxTotalLeftAdjunction A) (boxTensorLeftAdjunction A)
    (boxProductIso.app A).inv Q

/-- The same inverse-left mate preserves the original right-division unit. -/
theorem rightDivisionComponentIso_unit (B A : SSet.{u}) :
    (boxTotalRightAdjunction B).unit.app A ≫
      (rightDivisionComponentIso B).hom.app (boxTotal.flip.obj B |>.obj A) =
    (boxTensorRightAdjunction B).unit.app A ≫
      (totalRightFunction.obj (op B)).map
        ((((Functor.flipping (C := SSet.{u}) (D := SSet.{u}) (E := JoyalSSet.{u})).functor.mapIso
          boxProductIso).app B).inv.app A) :=
  unit_conjugateEquiv (boxTotalRightAdjunction B) (boxTensorRightAdjunction B) _ A

/-- The same inverse-left mate preserves the original right-division counit. -/
theorem rightDivisionComponentIso_counit (B : SSet.{u}) (Q : JoyalSSet.{u}) :
    (boxTensorTotal.flip.obj B).map ((rightDivisionComponentIso B).hom.app Q) ≫
      (boxTensorRightAdjunction B).counit.app Q =
    (((Functor.flipping (C := SSet.{u}) (D := SSet.{u}) (E := JoyalSSet.{u})).functor.mapIso
      boxProductIso).app B).inv.app ((totalRightDivision.obj (op B)).obj Q) ≫
      (boxTotalRightAdjunction B).counit.app Q :=
  conjugateEquiv_counit (boxTotalRightAdjunction B) (boxTensorRightAdjunction B) _ Q

/-- The inverse left-division comparison preserves the same original unit. -/
theorem leftDivisionComponentIso_inv_unit (A B : SSet.{u}) :
    (boxTensorLeftAdjunction A).unit.app B ≫
      (leftDivisionComponentIso A).inv.app ((boxTensorTotal.obj A).obj B) =
    (boxTotalLeftAdjunction A).unit.app B ≫
      (totalLeftDivision.obj (op A)).map ((boxProductIso.app A).hom.app B) :=
  unit_conjugateEquiv (boxTensorLeftAdjunction A) (boxTotalLeftAdjunction A)
    (boxProductIso.app A).hom B

/-- The inverse left-division comparison preserves the same original counit. -/
theorem leftDivisionComponentIso_inv_counit (A : SSet.{u}) (Q : JoyalSSet.{u}) :
    (boxTotal.obj A).map ((leftDivisionComponentIso A).inv.app Q) ≫
      (boxTotalLeftAdjunction A).counit.app Q =
    (boxProductIso.app A).hom.app ((totalLeftFunction.obj (op A)).obj Q) ≫
      (boxTensorLeftAdjunction A).counit.app Q :=
  conjugateEquiv_counit (boxTensorLeftAdjunction A) (boxTotalLeftAdjunction A)
    (boxProductIso.app A).hom Q

/-- The inverse right-division comparison preserves the same original unit. -/
theorem rightDivisionComponentIso_inv_unit (B A : SSet.{u}) :
    (boxTensorRightAdjunction B).unit.app A ≫
      (rightDivisionComponentIso B).inv.app ((boxTensorTotal.flip.obj B).obj A) =
    (boxTotalRightAdjunction B).unit.app A ≫
      (totalRightDivision.obj (op B)).map
        ((((Functor.flipping (C := SSet.{u}) (D := SSet.{u}) (E := JoyalSSet.{u})).functor.mapIso
          boxProductIso).app B).hom.app A) :=
  unit_conjugateEquiv (boxTensorRightAdjunction B) (boxTotalRightAdjunction B) _ A

/-- The inverse right-division comparison preserves the same original counit. -/
theorem rightDivisionComponentIso_inv_counit (B : SSet.{u}) (Q : JoyalSSet.{u}) :
    (boxTotal.flip.obj B).map ((rightDivisionComponentIso B).inv.app Q) ≫
      (boxTotalRightAdjunction B).counit.app Q =
    (((Functor.flipping (C := SSet.{u}) (D := SSet.{u}) (E := JoyalSSet.{u})).functor.mapIso
      boxProductIso).app B).hom.app ((totalRightFunction.obj (op B)).obj Q) ≫
      (boxTensorRightAdjunction B).counit.app Q :=
  conjugateEquiv_counit (boxTensorRightAdjunction B) (boxTotalRightAdjunction B) _ Q

private def pullbackTransportIso
    {G G' : SSet.{u}ᵒᵖ ⥤ JoyalSSet.{u} ⥤ SSet.{u}} (e : G ≅ G')
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : G.PullbackObjObj a q) (sq' : G'.PullbackObjObj a q) : sq.pt ≅ sq'.pt :=
  (sq.isPullback.of_iso
    (fst' := sq.fst ≫ (e.hom.app (op A)).app Q)
    (snd' := sq.snd ≫ (e.hom.app (op A')).app Q')
    (f' := (G'.obj (op A)).map q) (g' := (G'.map a.op).app Q')
    (Iso.refl sq.pt) ((e.app (op A)).app Q)
    ((e.app (op A')).app Q') ((e.app (op A)).app Q')
    (by simp) (by simp)
    ((e.hom.app (op A)).naturality q)
    (congr_app (e.hom.naturality a.op) Q')).isoIsPullback _ _ sq'.isPullback

private theorem pullbackTransportIso_hom_fst
    {G G' : SSet.{u}ᵒᵖ ⥤ JoyalSSet.{u} ⥤ SSet.{u}} (e : G ≅ G')
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : G.PullbackObjObj a q) (sq' : G'.PullbackObjObj a q) :
    (pullbackTransportIso e sq sq').hom ≫ sq'.fst = sq.fst ≫ (e.hom.app (op A)).app Q :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

private theorem pullbackTransportIso_hom_snd
    {G G' : SSet.{u}ᵒᵖ ⥤ JoyalSSet.{u} ⥤ SSet.{u}} (e : G ≅ G')
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : G.PullbackObjObj a q) (sq' : G'.PullbackObjObj a q) :
    (pullbackTransportIso e sq sq').hom ≫ sq'.snd = sq.snd ≫ (e.hom.app (op A')).app Q' :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

private theorem pullbackTransportIso_π
    {G G' : SSet.{u}ᵒᵖ ⥤ JoyalSSet.{u} ⥤ SSet.{u}} (e : G ≅ G')
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : G.PullbackObjObj a q) (sq' : G'.PullbackObjObj a q) :
    sq.π ≫ (pullbackTransportIso e sq sq').hom =
      (e.hom.app (op A')).app Q ≫ sq'.π := by
  apply sq'.hom_ext
  · rw [Category.assoc, pullbackTransportIso_hom_fst, ← Category.assoc, sq.π_fst,
      Category.assoc, sq'.π_fst]
    exact congr_app (e.hom.naturality a.op) Q
  · rw [Category.assoc, pullbackTransportIso_hom_snd, ← Category.assoc, sq.π_snd,
      Category.assoc, sq'.π_snd]
    exact (e.hom.app (op A')).naturality q

private theorem pullbackTransportIso_inv_fst
    {G G' : SSet.{u}ᵒᵖ ⥤ JoyalSSet.{u} ⥤ SSet.{u}} (e : G ≅ G')
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : G.PullbackObjObj a q) (sq' : G'.PullbackObjObj a q) :
    (pullbackTransportIso e sq sq').inv ≫ sq.fst =
      sq'.fst ≫ (e.inv.app (op A)).app Q := by
  rw [Iso.inv_comp_eq, ← Category.assoc, pullbackTransportIso_hom_fst, Category.assoc]
  simp

private theorem pullbackTransportIso_inv_snd
    {G G' : SSet.{u}ᵒᵖ ⥤ JoyalSSet.{u} ⥤ SSet.{u}} (e : G ≅ G')
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : G.PullbackObjObj a q) (sq' : G'.PullbackObjObj a q) :
    (pullbackTransportIso e sq sq').inv ≫ sq.snd =
      sq'.snd ≫ (e.inv.app (op A')).app Q' := by
  rw [Iso.inv_comp_eq, ← Category.assoc, pullbackTransportIso_hom_snd, Category.assoc]
  simp

private theorem pullbackTransportIso_π_inv
    {G G' : SSet.{u}ᵒᵖ ⥤ JoyalSSet.{u} ⥤ SSet.{u}} (e : G ≅ G')
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : G.PullbackObjObj a q) (sq' : G'.PullbackObjObj a q) :
    sq'.π ≫ (pullbackTransportIso e sq sq').inv =
      (e.inv.app (op A')).app Q ≫ sq.π := by
  rw [Iso.comp_inv_eq, Category.assoc, pullbackTransportIso_π]
  simp

private instance kRight_preserves_limits :
    Limits.PreservesLimitsOfSize.{0, 0} SSet.FreeGroupoidSimplex.kRightFunctor.{u} :=
  SSet.FreeGroupoidSimplex.kAdjunction.rightAdjoint_preservesLimits

private def totalLeftSquare
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.boxLeftDivisionFunctor.PullbackObjObj a (right.map q)) :
    totalLeftDivision.PullbackObjObj a q where
  pt := sq.pt
  fst := sq.fst
  snd := sq.snd
  isPullback := sq.isPullback
  π := sq.π
  π_fst := sq.π_fst
  π_snd := sq.π_snd

private def kRightSquare
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj a
      (JoyalSSet.forget.map q)) : totalLeftFunction.PullbackObjObj a q where
  pt := SSet.FreeGroupoidSimplex.kRightFunctor.obj sq.pt
  fst := SSet.FreeGroupoidSimplex.kRightFunctor.map sq.fst
  snd := SSet.FreeGroupoidSimplex.kRightFunctor.map sq.snd
  isPullback := sq.isPullback.map SSet.FreeGroupoidSimplex.kRightFunctor
  π := SSet.FreeGroupoidSimplex.kRightFunctor.map sq.π
  π_fst := by rw [← CategoryTheory.Functor.map_comp, sq.π_fst]; rfl
  π_snd := by rw [← CategoryTheory.Functor.map_comp, sq.π_snd]; rfl

/-- The supplied left-division pullback point maps to k-right of the supplied function point. -/
def leftDivisionPullbackIso
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.boxLeftDivisionFunctor.PullbackObjObj a (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj a
      (JoyalSSet.forget.map q)) : sq.pt ≅ SSet.FreeGroupoidSimplex.kRightFunctor.obj sq'.pt :=
  pullbackTransportIso leftDivisionIso (totalLeftSquare sq) (kRightSquare sq')

/-- The left point comparison preserves the first original projection. -/
theorem leftDivisionPullbackIso_hom_fst
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.boxLeftDivisionFunctor.PullbackObjObj a (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj a
      (JoyalSSet.forget.map q)) :
    (leftDivisionPullbackIso sq sq').hom ≫ SSet.FreeGroupoidSimplex.kRightFunctor.map sq'.fst =
      sq.fst ≫ (leftDivisionIso.hom.app (op A)).app Q :=
  pullbackTransportIso_hom_fst _ _ _

/-- The left point comparison preserves the second original projection. -/
theorem leftDivisionPullbackIso_hom_snd
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.boxLeftDivisionFunctor.PullbackObjObj a (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj a
      (JoyalSSet.forget.map q)) :
    (leftDivisionPullbackIso sq sq').hom ≫ SSet.FreeGroupoidSimplex.kRightFunctor.map sq'.snd =
      sq.snd ≫ (leftDivisionIso.hom.app (op A')).app Q' :=
  pullbackTransportIso_hom_snd _ _ _

/-- The left comparison preserves the entire original pullback-Hom map. -/
theorem leftDivisionPullbackIso_π
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.boxLeftDivisionFunctor.PullbackObjObj a (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj a
      (JoyalSSet.forget.map q)) :
    sq.π ≫ (leftDivisionPullbackIso sq sq').hom =
      (leftDivisionIso.hom.app (op A')).app Q ≫ SSet.FreeGroupoidSimplex.kRightFunctor.map sq'.π :=
  pullbackTransportIso_π _ _ _

/-- The inverse left point comparison preserves the first original projection. -/
theorem leftDivisionPullbackIso_inv_fst
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.boxLeftDivisionFunctor.PullbackObjObj a (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj a
      (JoyalSSet.forget.map q)) :
    (leftDivisionPullbackIso sq sq').inv ≫ sq.fst =
      SSet.FreeGroupoidSimplex.kRightFunctor.map sq'.fst ≫ (leftDivisionIso.inv.app (op A)).app Q :=
  pullbackTransportIso_inv_fst _ _ _

/-- The inverse left point comparison preserves the second original projection. -/
theorem leftDivisionPullbackIso_inv_snd
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.boxLeftDivisionFunctor.PullbackObjObj a (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj a
      (JoyalSSet.forget.map q)) :
    (leftDivisionPullbackIso sq sq').inv ≫ sq.snd =
      SSet.FreeGroupoidSimplex.kRightFunctor.map sq'.snd ≫
          (leftDivisionIso.inv.app (op A')).app Q' :=
  pullbackTransportIso_inv_snd _ _ _

/-- The inverse left comparison preserves the entire original pullback-Hom map. -/
theorem leftDivisionPullbackIso_π_inv
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.boxLeftDivisionFunctor.PullbackObjObj a (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj a
      (JoyalSSet.forget.map q)) :
    SSet.FreeGroupoidSimplex.kRightFunctor.map sq'.π ≫ (leftDivisionPullbackIso sq sq').inv =
      (leftDivisionIso.inv.app (op A')).app Q ≫ sq.π :=
  pullbackTransportIso_π_inv _ _ _

private def totalRightSquare
    {B B' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {b : B ⟶ B'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.rowPowerBifunctor.PullbackObjObj b (right.map q)) :
    totalRightDivision.PullbackObjObj b q where
  pt := sq.pt
  fst := sq.fst
  snd := sq.snd
  isPullback := sq.isPullback
  π := sq.π
  π_fst := sq.π_fst
  π_snd := sq.π_snd

private def rightFunctionSquare
    {B B' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {b : B ⟶ B'} {q : Q ⟶ Q'}
    (sq : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj
      (SSet.FreeGroupoidSimplex.kFunctor.map b) (JoyalSSet.forget.map q)) :
    totalRightFunction.PullbackObjObj b q where
  pt := sq.pt
  fst := sq.fst
  snd := sq.snd
  isPullback := sq.isPullback
  π := sq.π
  π_fst := sq.π_fst
  π_snd := sq.π_snd

/-- The supplied right-division point compares with the supplied k-left function point. -/
def rightDivisionPullbackIso
    {B B' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {b : B ⟶ B'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.rowPowerBifunctor.PullbackObjObj b (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj
      (SSet.FreeGroupoidSimplex.kFunctor.map b) (JoyalSSet.forget.map q)) : sq.pt ≅ sq'.pt :=
  pullbackTransportIso rightDivisionIso (totalRightSquare sq) (rightFunctionSquare sq')

/-- The right comparison preserves the first supplied projection. -/
theorem rightDivisionPullbackIso_hom_fst
    {B B' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {b : B ⟶ B'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.rowPowerBifunctor.PullbackObjObj b (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj
      (SSet.FreeGroupoidSimplex.kFunctor.map b) (JoyalSSet.forget.map q)) :
    (rightDivisionPullbackIso sq sq').hom ≫ sq'.fst =
      sq.fst ≫ (rightDivisionIso.hom.app (op B)).app Q :=
  pullbackTransportIso_hom_fst _ _ _

/-- The right comparison preserves the second supplied projection. -/
theorem rightDivisionPullbackIso_hom_snd
    {B B' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {b : B ⟶ B'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.rowPowerBifunctor.PullbackObjObj b (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj
      (SSet.FreeGroupoidSimplex.kFunctor.map b) (JoyalSSet.forget.map q)) :
    (rightDivisionPullbackIso sq sq').hom ≫ sq'.snd =
      sq.snd ≫ (rightDivisionIso.hom.app (op B')).app Q' :=
  pullbackTransportIso_hom_snd _ _ _

/-- The right comparison preserves the complete supplied pullback-Hom map. -/
theorem rightDivisionPullbackIso_π
    {B B' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {b : B ⟶ B'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.rowPowerBifunctor.PullbackObjObj b (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj
      (SSet.FreeGroupoidSimplex.kFunctor.map b) (JoyalSSet.forget.map q)) :
    sq.π ≫ (rightDivisionPullbackIso sq sq').hom =
      (rightDivisionIso.hom.app (op B')).app Q ≫ sq'.π :=
  pullbackTransportIso_π _ _ _

/-- The inverse right comparison preserves the first supplied projection. -/
theorem rightDivisionPullbackIso_inv_fst
    {B B' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {b : B ⟶ B'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.rowPowerBifunctor.PullbackObjObj b (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj
      (SSet.FreeGroupoidSimplex.kFunctor.map b) (JoyalSSet.forget.map q)) :
    (rightDivisionPullbackIso sq sq').inv ≫ sq.fst =
      sq'.fst ≫ (rightDivisionIso.inv.app (op B)).app Q :=
  pullbackTransportIso_inv_fst _ _ _

/-- The inverse right comparison preserves the second supplied projection. -/
theorem rightDivisionPullbackIso_inv_snd
    {B B' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {b : B ⟶ B'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.rowPowerBifunctor.PullbackObjObj b (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj
      (SSet.FreeGroupoidSimplex.kFunctor.map b) (JoyalSSet.forget.map q)) :
    (rightDivisionPullbackIso sq sq').inv ≫ sq.snd =
      sq'.snd ≫ (rightDivisionIso.inv.app (op B')).app Q' :=
  pullbackTransportIso_inv_snd _ _ _

/-- The inverse right comparison preserves the complete supplied pullback-Hom map. -/
theorem rightDivisionPullbackIso_π_inv
    {B B' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {b : B ⟶ B'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.rowPowerBifunctor.PullbackObjObj b (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj
      (SSet.FreeGroupoidSimplex.kFunctor.map b) (JoyalSSet.forget.map q)) :
    sq'.π ≫ (rightDivisionPullbackIso sq sq').inv =
      (rightDivisionIso.inv.app (op B')).app Q ≫ sq.π :=
  pullbackTransportIso_π_inv _ _ _

private def pushoutTransportIso
    {F F' : SSet.{u} ⥤ SSet.{u} ⥤ JoyalSSet.{u}} (e : F ≅ F')
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : F.PushoutObjObj a b) (sq' : F'.PushoutObjObj a b) : sq.pt ≅ sq'.pt :=
  (sq.ofNatIso e).isPushout.isoIsPushout _ _ sq'.isPushout

private theorem pushoutTransportIso_inl_hom
    {F F' : SSet.{u} ⥤ SSet.{u} ⥤ JoyalSSet.{u}} (e : F ≅ F')
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : F.PushoutObjObj a b) (sq' : F'.PushoutObjObj a b) :
    sq.inl ≫ (pushoutTransportIso e sq sq').hom = (e.hom.app A').app B ≫ sq'.inl := by
  have h := IsPushout.inl_isoIsPushout_hom _ _ (sq.ofNatIso e).isPushout sq'.isPushout
  change ((e.app A').app B).inv ≫ (sq.inl ≫ (pushoutTransportIso e sq sq').hom) = sq'.inl at h
  exact (Iso.inv_comp_eq _).1 h

private theorem pushoutTransportIso_inr_hom
    {F F' : SSet.{u} ⥤ SSet.{u} ⥤ JoyalSSet.{u}} (e : F ≅ F')
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : F.PushoutObjObj a b) (sq' : F'.PushoutObjObj a b) :
    sq.inr ≫ (pushoutTransportIso e sq sq').hom = (e.hom.app A).app B' ≫ sq'.inr := by
  have h := IsPushout.inr_isoIsPushout_hom _ _ (sq.ofNatIso e).isPushout sq'.isPushout
  change ((e.app A).app B').inv ≫ (sq.inr ≫ (pushoutTransportIso e sq sq').hom) = sq'.inr at h
  exact (Iso.inv_comp_eq _).1 h

private theorem pushoutTransportIso_ι
    {F F' : SSet.{u} ⥤ SSet.{u} ⥤ JoyalSSet.{u}} (e : F ≅ F')
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : F.PushoutObjObj a b) (sq' : F'.PushoutObjObj a b) :
    sq.ι ≫ (e.hom.app A').app B' = (pushoutTransportIso e sq sq').hom ≫ sq'.ι := by
  apply sq.hom_ext
  · rw [← Category.assoc, sq.inl_ι, ← Category.assoc, pushoutTransportIso_inl_hom,
      Category.assoc, sq'.inl_ι]
    exact (e.hom.app A').naturality b
  · rw [← Category.assoc, sq.inr_ι, ← Category.assoc, pushoutTransportIso_inr_hom,
      Category.assoc, sq'.inr_ι]
    exact congr_app (e.hom.naturality a) B'

private theorem pushoutTransportIso_inl_inv
    {F F' : SSet.{u} ⥤ SSet.{u} ⥤ JoyalSSet.{u}} (e : F ≅ F')
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : F.PushoutObjObj a b) (sq' : F'.PushoutObjObj a b) :
    sq'.inl ≫ (pushoutTransportIso e sq sq').inv = (e.inv.app A').app B ≫ sq.inl := by
  rw [Iso.comp_inv_eq, Category.assoc, pushoutTransportIso_inl_hom]
  simp

private theorem pushoutTransportIso_inr_inv
    {F F' : SSet.{u} ⥤ SSet.{u} ⥤ JoyalSSet.{u}} (e : F ≅ F')
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : F.PushoutObjObj a b) (sq' : F'.PushoutObjObj a b) :
    sq'.inr ≫ (pushoutTransportIso e sq sq').inv = (e.inv.app A).app B' ≫ sq.inr := by
  rw [Iso.comp_inv_eq, Category.assoc, pushoutTransportIso_inr_hom]
  simp

private theorem pushoutTransportIso_ι_inv
    {F F' : SSet.{u} ⥤ SSet.{u} ⥤ JoyalSSet.{u}} (e : F ≅ F')
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : F.PushoutObjObj a b) (sq' : F'.PushoutObjObj a b) :
    sq'.ι ≫ (e.inv.app A').app B' = (pushoutTransportIso e sq sq').inv ≫ sq.ι := by
  rw [eq_comm, Iso.inv_comp_eq, ← Category.assoc, ← pushoutTransportIso_ι, Category.assoc]
  simp

private instance total_preserves_colimits : Limits.PreservesColimitsOfSize.{0, 0} left.{u} :=
  adjunction.leftAdjoint_preservesColimits

private instance carrier_preserves_colimits :
    Limits.PreservesColimitsOfSize.{0, 0} JoyalSSet.ofSSet.{u} :=
  JoyalSSet.equivalenceSSet.symm.toAdjunction.leftAdjoint_preservesColimits

private def totalPushoutSquare
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : SimplicialSpace.boxProduct.PushoutObjObj a b) : boxTotal.PushoutObjObj a b where
  pt := left.obj sq.pt
  inl := left.map sq.inl
  inr := left.map sq.inr
  isPushout := sq.isPushout.map left
  ι := left.map sq.ι
  inl_ι := by rw [← CategoryTheory.Functor.map_comp, sq.inl_ι]; rfl
  inr_ι := by rw [← CategoryTheory.Functor.map_comp, sq.inr_ι]; rfl

private def productPushoutSquare
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : (curriedTensor SSet.{u}).PushoutObjObj a (SSet.FreeGroupoidSimplex.kFunctor.map b)) :
    boxTensorTotal.PushoutObjObj a b where
  pt := JoyalSSet.ofSSet.obj sq.pt
  inl := JoyalSSet.ofSSet.map sq.inl
  inr := JoyalSSet.ofSSet.map sq.inr
  isPushout := sq.isPushout.map JoyalSSet.ofSSet
  ι := JoyalSSet.ofSSet.map sq.ι
  inl_ι := by rw [← CategoryTheory.Functor.map_comp, sq.inl_ι]; rfl
  inr_ι := by rw [← CategoryTheory.Functor.map_comp, sq.inr_ι]; rfl

/-- The total image of the supplied box point compares with the supplied product point. -/
def boxPushoutIso
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : SimplicialSpace.boxProduct.PushoutObjObj a b)
    (sq' : (curriedTensor SSet.{u}).PushoutObjObj a (SSet.FreeGroupoidSimplex.kFunctor.map b)) :
    left.obj sq.pt ≅ JoyalSSet.ofSSet.obj sq'.pt :=
  pushoutTransportIso boxProductIso (totalPushoutSquare sq) (productPushoutSquare sq')

/-- The box point comparison preserves the first supplied injection. -/
theorem boxPushoutIso_inl_hom
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : SimplicialSpace.boxProduct.PushoutObjObj a b)
    (sq' : (curriedTensor SSet.{u}).PushoutObjObj a (SSet.FreeGroupoidSimplex.kFunctor.map b)) :
    left.map sq.inl ≫ (boxPushoutIso sq sq').hom =
      (boxProductIso.hom.app A').app B ≫ JoyalSSet.ofSSet.map sq'.inl :=
  pushoutTransportIso_inl_hom _ _ _

/-- The box point comparison preserves the second supplied injection. -/
theorem boxPushoutIso_inr_hom
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : SimplicialSpace.boxProduct.PushoutObjObj a b)
    (sq' : (curriedTensor SSet.{u}).PushoutObjObj a (SSet.FreeGroupoidSimplex.kFunctor.map b)) :
    left.map sq.inr ≫ (boxPushoutIso sq sq').hom =
      (boxProductIso.hom.app A).app B' ≫ JoyalSSet.ofSSet.map sq'.inr :=
  pushoutTransportIso_inr_hom _ _ _

/-- The box comparison preserves the entire original pushout-product map. -/
theorem boxPushoutIso_ι
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : SimplicialSpace.boxProduct.PushoutObjObj a b)
    (sq' : (curriedTensor SSet.{u}).PushoutObjObj a (SSet.FreeGroupoidSimplex.kFunctor.map b)) :
    left.map sq.ι ≫ (boxProductIso.hom.app A').app B' =
      (boxPushoutIso sq sq').hom ≫ JoyalSSet.ofSSet.map sq'.ι :=
  pushoutTransportIso_ι boxProductIso (totalPushoutSquare sq) (productPushoutSquare sq')

/-- The inverse box comparison preserves the first supplied injection. -/
theorem boxPushoutIso_inl_inv
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : SimplicialSpace.boxProduct.PushoutObjObj a b)
    (sq' : (curriedTensor SSet.{u}).PushoutObjObj a (SSet.FreeGroupoidSimplex.kFunctor.map b)) :
    JoyalSSet.ofSSet.map sq'.inl ≫ (boxPushoutIso sq sq').inv =
      (boxProductIso.inv.app A').app B ≫ left.map sq.inl :=
  pushoutTransportIso_inl_inv _ _ _

/-- The inverse box comparison preserves the second supplied injection. -/
theorem boxPushoutIso_inr_inv
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : SimplicialSpace.boxProduct.PushoutObjObj a b)
    (sq' : (curriedTensor SSet.{u}).PushoutObjObj a (SSet.FreeGroupoidSimplex.kFunctor.map b)) :
    JoyalSSet.ofSSet.map sq'.inr ≫ (boxPushoutIso sq sq').inv =
      (boxProductIso.inv.app A).app B' ≫ left.map sq.inr :=
  pushoutTransportIso_inr_inv _ _ _

/-- The inverse box comparison preserves the complete supplied pushout-product map. -/
theorem boxPushoutIso_ι_inv
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : SimplicialSpace.boxProduct.PushoutObjObj a b)
    (sq' : (curriedTensor SSet.{u}).PushoutObjObj a (SSet.FreeGroupoidSimplex.kFunctor.map b)) :
    JoyalSSet.ofSSet.map sq'.ι ≫ (boxProductIso.inv.app A').app B' =
      (boxPushoutIso sq sq').inv ≫ left.map sq.ι :=
  pushoutTransportIso_ι_inv boxProductIso (totalPushoutSquare sq) (productPushoutSquare sq')

/-- The comparison identifies the entire original supplied total/product pushout arrows. -/
def boxPushoutArrowIso
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : SimplicialSpace.boxProduct.PushoutObjObj a b)
    (sq' : (curriedTensor SSet.{u}).PushoutObjObj a (SSet.FreeGroupoidSimplex.kFunctor.map b)) :
    Arrow.mk (left.map sq.ι) ≅ Arrow.mk (JoyalSSet.ofSSet.map sq'.ι) :=
  Arrow.isoMk (boxPushoutIso sq sq') ((boxProductIso.app A').app B')
    (boxPushoutIso_ι sq sq').symm

/-- The comparison identifies the entire supplied left division/k-right pullback arrows. -/
def leftDivisionPullbackArrowIso
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.boxLeftDivisionFunctor.PullbackObjObj a (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj a
      (JoyalSSet.forget.map q)) :
    Arrow.mk sq.π ≅ Arrow.mk (SSet.FreeGroupoidSimplex.kRightFunctor.map sq'.π) :=
  Arrow.isoMk ((leftDivisionIso.app (op A')).app Q) (leftDivisionPullbackIso sq sq')
    (leftDivisionPullbackIso_π sq sq').symm

/-- The comparison identifies the entire supplied right division/function pullback arrows. -/
def rightDivisionPullbackArrowIso
    {B B' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {b : B ⟶ B'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.rowPowerBifunctor.PullbackObjObj b (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj
      (SSet.FreeGroupoidSimplex.kFunctor.map b) (JoyalSSet.forget.map q)) :
    Arrow.mk sq.π ≅ Arrow.mk sq'.π :=
  Arrow.isoMk ((rightDivisionIso.app (op B')).app Q) (rightDivisionPullbackIso sq sq')
    (rightDivisionPullbackIso_π sq sq').symm

/-- The original named row pullback-Hom is the source of the same whole-arrow comparison. -/
def rightRowPullbackArrowIso
    {B B' : SSet.{u}} {Q Q' : JoyalSSet.{u}} (b : B ⟶ B') (q : Q ⟶ Q')
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj
      (SSet.FreeGroupoidSimplex.kFunctor.map b) (JoyalSSet.forget.map q)) :
    Arrow.mk (SimplicialSpace.rowPullbackHom b (right.map q)) ≅ Arrow.mk sq'.π :=
  rightDivisionPullbackArrowIso
    (Functor.PullbackObjObj.ofHasPullback SimplicialSpace.rowPowerBifunctor b (right.map q)) sq'

private def liftLeftIsoEquiv {C : Type v} [Category.{w} C]
    {f g p : Arrow C} (e : f ≅ g) (φ : f ⟶ p) :
    Arrow.LiftStruct φ ≃ Arrow.LiftStruct (e.inv ≫ φ) where
  toFun l :=
    { l := e.inv.right ≫ l.l
      fac_left := by
        change g.hom ≫ (e.inv.right ≫ l.l) = e.inv.left ≫ φ.left
        rw [← Category.assoc, ← e.inv.w, Category.assoc, l.fac_left]
      fac_right := by
        change (e.inv.right ≫ l.l) ≫ p.hom = e.inv.right ≫ φ.right
        rw [Category.assoc, l.fac_right] }
  invFun l :=
    { l := e.hom.right ≫ l.l
      fac_left := by
        rw [← Category.assoc, ← e.hom.w, Category.assoc, l.fac_left]
        simp
      fac_right := by
        rw [Category.assoc, l.fac_right]
        simp }
  left_inv l := by
    apply CommSq.LiftStruct.ext
    simp
  right_inv l := by
    apply CommSq.LiftStruct.ext
    simp

private def liftRightIsoEquiv {C : Type v} [Category.{w} C]
    {i p p' : Arrow C} (e : p ≅ p') (φ : i ⟶ p) :
    Arrow.LiftStruct φ ≃ Arrow.LiftStruct (φ ≫ e.hom) where
  toFun l :=
    { l := l.l ≫ e.hom.left
      fac_left := by
        change i.hom ≫ (l.l ≫ e.hom.left) = φ.left ≫ e.hom.left
        rw [← Category.assoc, l.fac_left]
      fac_right := by
        change (l.l ≫ e.hom.left) ≫ p'.hom = φ.right ≫ e.hom.right
        rw [Category.assoc, e.hom.w, ← Category.assoc, l.fac_right] }
  invFun l :=
    { l := l.l ≫ e.inv.left
      fac_left := by
        rw [← Category.assoc, l.fac_left]
        simp
      fac_right := by
        rw [Category.assoc, e.inv.w, ← Category.assoc, l.fac_right]
        simp }
  left_inv l := by
    apply CommSq.LiftStruct.ext
    simp [Category.assoc]
  right_inv l := by
    apply CommSq.LiftStruct.ext
    simp [Category.assoc]

/-- Fillers of an original total pushout square correspond to fillers of the same product square. -/
def boxPushoutLiftEquiv
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : SimplicialSpace.boxProduct.PushoutObjObj a b)
    (sq' : (curriedTensor SSet.{u}).PushoutObjObj a (SSet.FreeGroupoidSimplex.kFunctor.map b))
    {p : Arrow JoyalSSet.{u}} (φ : Arrow.mk (left.map sq.ι) ⟶ p) :
    Arrow.LiftStruct φ ≃ Arrow.LiftStruct ((boxPushoutArrowIso sq sq').inv ≫ φ) :=
  liftLeftIsoEquiv (boxPushoutArrowIso sq sq') φ

/-- The transported product filler is the original filler preceded by the original inverse
boundary. -/
theorem boxPushoutLiftEquiv_l
    {A A' B B' : SSet.{u}} {a : A ⟶ A'} {b : B ⟶ B'}
    (sq : SimplicialSpace.boxProduct.PushoutObjObj a b)
    (sq' : (curriedTensor SSet.{u}).PushoutObjObj a (SSet.FreeGroupoidSimplex.kFunctor.map b))
    {p : Arrow JoyalSSet.{u}} (φ : Arrow.mk (left.map sq.ι) ⟶ p) (l : Arrow.LiftStruct φ) :
    (boxPushoutLiftEquiv sq sq' φ l).l = (boxProductIso.inv.app A').app B' ≫ l.l := rfl

/-- Original left-division fillers transport to the k-right image of the same function corner. -/
def leftDivisionPullbackLiftEquiv
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.boxLeftDivisionFunctor.PullbackObjObj a (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj a
      (JoyalSSet.forget.map q)) {i : Arrow SSet.{u}} (φ : i ⟶ Arrow.mk sq.π) :
    Arrow.LiftStruct φ ≃ Arrow.LiftStruct (φ ≫ (leftDivisionPullbackArrowIso sq sq').hom) :=
  liftRightIsoEquiv (leftDivisionPullbackArrowIso sq sq') φ

/-- The transported left-division filler uses the original division component. -/
theorem leftDivisionPullbackLiftEquiv_l
    {A A' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {a : A ⟶ A'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.boxLeftDivisionFunctor.PullbackObjObj a (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj a
      (JoyalSSet.forget.map q)) {i : Arrow SSet.{u}} (φ : i ⟶ Arrow.mk sq.π)
    (l : Arrow.LiftStruct φ) :
    (leftDivisionPullbackLiftEquiv sq sq' φ l).l =
      l.l ≫ (leftDivisionIso.hom.app (op A')).app Q := rfl

/-- Original right-division fillers transport to the same k-left function corner. -/
def rightDivisionPullbackLiftEquiv
    {B B' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {b : B ⟶ B'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.rowPowerBifunctor.PullbackObjObj b (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj
      (SSet.FreeGroupoidSimplex.kFunctor.map b) (JoyalSSet.forget.map q))
    {i : Arrow SSet.{u}} (φ : i ⟶ Arrow.mk sq.π) :
    Arrow.LiftStruct φ ≃ Arrow.LiftStruct (φ ≫ (rightDivisionPullbackArrowIso sq sq').hom) :=
  liftRightIsoEquiv (rightDivisionPullbackArrowIso sq sq') φ

/-- The transported right-division filler uses the original division component. -/
theorem rightDivisionPullbackLiftEquiv_l
    {B B' : SSet.{u}} {Q Q' : JoyalSSet.{u}} {b : B ⟶ B'} {q : Q ⟶ Q'}
    (sq : SimplicialSpace.rowPowerBifunctor.PullbackObjObj b (right.map q))
    (sq' : (MonoidalClosed.internalHom (C := SSet.{u})).PullbackObjObj
      (SSet.FreeGroupoidSimplex.kFunctor.map b) (JoyalSSet.forget.map q))
    {i : Arrow SSet.{u}} (φ : i ⟶ Arrow.mk sq.π) (l : Arrow.LiftStruct φ) :
    (rightDivisionPullbackLiftEquiv sq sq' φ l).l =
      l.l ≫ (rightDivisionIso.hom.app (op B')).app Q := rfl

end SimplicialSpace.TotalSpace
