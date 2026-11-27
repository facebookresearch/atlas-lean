/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Functor.NamedBifibrantComparison
import MathlibExt.CategoryTheory.Localization.OriginalCompositeLaws
import MathlibExt.CategoryTheory.Localization.OriginalComparisonLaws
import MathlibExt.CategoryTheory.Localization.OriginalCompositionLaws

set_option autoImplicit false
noncomputable section
universe u v u' v'
open CategoryTheory

namespace CategoryTheory.Localization
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- The original single replacement comparison uses the actual two constructed Ho projections. -/
def originalLocalizedComparison (W : MorphismProperty C) (W' : MorphismProperty D)
    (Q : C ⥤ C) (Q' : D ⥤ D) (F : C ⥤ D)
    (q : W.IsInvertedBy (Q ⋙ W.Q)) (q' : W'.IsInvertedBy (Q' ⋙ W'.Q))
    (hF : W.IsInvertedBy (F ⋙ W'.Q)) (cQ : Q ⋙ F ≅ F ⋙ Q') :=
  originalComparisonIso W W'.Q cQ
    (Construction.lift (Q ⋙ W.Q) q ⋙ Construction.lift (F ⋙ W'.Q) hF)
    (Construction.lift (F ⋙ W'.Q) hF ⋙ Construction.lift (Q' ⋙ W'.Q) q')
    (by
      calc
        W.Q ⋙ (Construction.lift (Q ⋙ W.Q) q ⋙ Construction.lift (F ⋙ W'.Q) hF) =
            (W.Q ⋙ Construction.lift (Q ⋙ W.Q) q) ⋙ Construction.lift (F ⋙ W'.Q) hF := rfl
        _ = (Q ⋙ W.Q) ⋙ Construction.lift (F ⋙ W'.Q) hF := by rw [Construction.fac]
        _ = Q ⋙ (W.Q ⋙ Construction.lift (F ⋙ W'.Q) hF) := rfl
        _ = Q ⋙ (F ⋙ W'.Q) := by rw [Construction.fac]
        _ = _ := rfl)
    (by
      calc
        W.Q ⋙ (Construction.lift (F ⋙ W'.Q) hF ⋙ Construction.lift (Q' ⋙ W'.Q) q') =
            (W.Q ⋙ Construction.lift (F ⋙ W'.Q) hF) ⋙ Construction.lift (Q' ⋙ W'.Q) q' := rfl
        _ = (F ⋙ W'.Q) ⋙ Construction.lift (Q' ⋙ W'.Q) q' := by rw [Construction.fac]
        _ = F ⋙ (W'.Q ⋙ Construction.lift (Q' ⋙ W'.Q) q') := rfl
        _ = F ⋙ (Q' ⋙ W'.Q) := by rw [Construction.fac]
        _ = _ := rfl)

/-- The original single forward component remains the exact projected raw comparison map. -/
theorem originalLocalizedComparison_hom_projected
    (W : MorphismProperty C) (W' : MorphismProperty D)
    (Q : C ⥤ C) (Q' : D ⥤ D) (F : C ⥤ D)
    (q : W.IsInvertedBy (Q ⋙ W.Q)) (q' : W'.IsInvertedBy (Q' ⋙ W'.Q))
    (hF : W.IsInvertedBy (F ⋙ W'.Q)) (cQ : Q ⋙ F ≅ F ⋙ Q') (X : C) :
    (originalLocalizedComparison W W' Q Q' F q q' hF cQ).hom.app (W.Q.obj X) =
      W'.Q.map (cQ.hom.app X) := by
  rw [originalLocalizedComparison, originalComparisonIso_hom_projected]
  change 𝟙 _ ≫ (W'.Q.map (cQ.hom.app X) ≫ 𝟙 _) = _
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The original single inverse component remains the same projected raw inverse map. -/
theorem originalLocalizedComparison_inv_projected
    (W : MorphismProperty C) (W' : MorphismProperty D)
    (Q : C ⥤ C) (Q' : D ⥤ D) (F : C ⥤ D)
    (q : W.IsInvertedBy (Q ⋙ W.Q)) (q' : W'.IsInvertedBy (Q' ⋙ W'.Q))
    (hF : W.IsInvertedBy (F ⋙ W'.Q)) (cQ : Q ⋙ F ≅ F ⋙ Q') (X : C) :
    (originalLocalizedComparison W W' Q Q' F q q' hF cQ).inv.app (W.Q.obj X) =
      W'.Q.map (cQ.inv.app X) := by
  rw [originalLocalizedComparison, originalComparisonIso_inv_projected]
  change 𝟙 _ ≫ (W'.Q.map (cQ.inv.app X) ≫ 𝟙 _) = _
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The actual constructed named bifibrant Ho comparison retains all original projected factors. -/
def originalLocalizedNamedComparison (W : MorphismProperty C) (W' : MorphismProperty D)
    (Q R : C ⥤ C) (Q' R' : D ⥤ D) (F : C ⥤ D)
    (q : W.IsInvertedBy (Q ⋙ W.Q)) (r : W.IsInvertedBy (R ⋙ W.Q))
    (qr : W.IsInvertedBy ((Q ⋙ R) ⋙ W.Q))
    (q' : W'.IsInvertedBy (Q' ⋙ W'.Q)) (r' : W'.IsInvertedBy (R' ⋙ W'.Q))
    (qr' : W'.IsInvertedBy ((Q' ⋙ R') ⋙ W'.Q))
    (hF : W.IsInvertedBy (F ⋙ W'.Q)) (cQ : Q ⋙ F ≅ F ⋙ Q')
    (cR : R ⋙ F ≅ F ⋙ R') :
    Construction.lift ((Q ⋙ R) ⋙ W.Q) qr ⋙ Construction.lift (F ⋙ W'.Q) hF ≅
      Construction.lift (F ⋙ W'.Q) hF ⋙ Construction.lift ((Q' ⋙ R') ⋙ W'.Q) qr' := by
  exact CategoryTheory.originalNamedBifibrantComparison
    (Construction.lift (Q ⋙ W.Q) q) (Construction.lift (R ⋙ W.Q) r)
    (Construction.lift ((Q ⋙ R) ⋙ W.Q) qr)
    (Construction.lift (Q' ⋙ W'.Q) q') (Construction.lift (R' ⋙ W'.Q) r')
    (Construction.lift ((Q' ⋙ R') ⋙ W'.Q) qr') (Construction.lift (F ⋙ W'.Q) hF)
    (originalLocalizedComparison W W' Q Q' F q q' hF cQ)
    (originalLocalizedComparison W W' R R' F r r' hF cR)
    (originalCompositeIso W Q R q r qr) (originalCompositeIso W' Q' R' q' r' qr')

/-- The actual named localized forward comparison is the full original raw bifibrant map. -/
theorem originalLocalizedNamedComparison_hom_projected
    (W : MorphismProperty C) (W' : MorphismProperty D)
    (Q R : C ⥤ C) (Q' R' : D ⥤ D) (F : C ⥤ D)
    (q : W.IsInvertedBy (Q ⋙ W.Q)) (r : W.IsInvertedBy (R ⋙ W.Q))
    (qr : W.IsInvertedBy ((Q ⋙ R) ⋙ W.Q))
    (q' : W'.IsInvertedBy (Q' ⋙ W'.Q)) (r' : W'.IsInvertedBy (R' ⋙ W'.Q))
    (qr' : W'.IsInvertedBy ((Q' ⋙ R') ⋙ W'.Q))
    (hF : W.IsInvertedBy (F ⋙ W'.Q)) (cQ : Q ⋙ F ≅ F ⋙ Q')
    (cR : R ⋙ F ≅ F ⋙ R') (X : C) :
    (originalLocalizedNamedComparison W W' Q R Q' R' F q r qr q' r' qr' hF cQ cR).hom.app
        (W.Q.obj X) =
      W'.Q.map ((CategoryTheory.originalBifibrantComparison Q R Q' R' F cQ cR).hom.app X) := by
  unfold originalLocalizedNamedComparison
  rw [CategoryTheory.originalNamedBifibrantComparison_hom_app]
  have ha := congrArg (Construction.lift (F ⋙ W'.Q) hF).map
    (originalCompositeIso_hom_projected W Q R q r qr X)
  have haId := ha.trans ((Construction.lift (F ⋙ W'.Q) hF).map_id (W.Q.obj (R.obj (Q.obj X))))
  have hd := originalCompositeIso_inv_projected W' Q' R' q' r' qr' (F.obj X)
  have hb := originalLocalizedComparison_hom_projected W W' R R' F r r' hF cR (Q.obj X)
  have hc := originalLocalizedComparison_hom_projected W W' Q Q' F q q' hF cQ X
  have hbMap := hb
  have hcMap := hc
  have hMap := Functor.congr_hom (Construction.fac (R' ⋙ W'.Q) r') (cQ.hom.app X)
  change (Construction.lift (R' ⋙ W'.Q) r').map (W'.Q.map (cQ.hom.app X)) =
    W'.Q.map (R'.map (cQ.hom.app X)) at hMap
  have hcImage := (congrArg (Construction.lift (R' ⋙ W'.Q) r').map hcMap).trans hMap
  have hFactors := congrArg₂ (fun a d => a ≫
      ((originalLocalizedComparison W W' R R' F r r' hF cR).hom.app (W.Q.obj (Q.obj X)) ≫
        (Construction.lift (R' ⋙ W'.Q) r').map
          ((originalLocalizedComparison W W' Q Q' F q q' hF cQ).hom.app (W.Q.obj X))) ≫ d) haId hd
  refine hFactors.trans ?_
  have hMiddle := congrArg₂ (fun b c => 𝟙 _ ≫ (b ≫ c) ≫ 𝟙 _) hbMap hcImage
  refine hMiddle.trans ?_
  exact ((Category.id_comp _).trans (Category.comp_id _)).trans (W'.Q.map_comp _ _).symm

/-- The actual named localized inverse comparison retains the full original raw inverse map. -/
theorem originalLocalizedNamedComparison_inv_projected
    (W : MorphismProperty C) (W' : MorphismProperty D)
    (Q R : C ⥤ C) (Q' R' : D ⥤ D) (F : C ⥤ D)
    (q : W.IsInvertedBy (Q ⋙ W.Q)) (r : W.IsInvertedBy (R ⋙ W.Q))
    (qr : W.IsInvertedBy ((Q ⋙ R) ⋙ W.Q))
    (q' : W'.IsInvertedBy (Q' ⋙ W'.Q)) (r' : W'.IsInvertedBy (R' ⋙ W'.Q))
    (qr' : W'.IsInvertedBy ((Q' ⋙ R') ⋙ W'.Q))
    (hF : W.IsInvertedBy (F ⋙ W'.Q)) (cQ : Q ⋙ F ≅ F ⋙ Q')
    (cR : R ⋙ F ≅ F ⋙ R') (X : C) :
    (originalLocalizedNamedComparison W W' Q R Q' R' F q r qr q' r' qr' hF cQ cR).inv.app
        (W.Q.obj X) =
      W'.Q.map ((CategoryTheory.originalBifibrantComparison Q R Q' R' F cQ cR).inv.app X) := by
  unfold originalLocalizedNamedComparison
  rw [CategoryTheory.originalNamedBifibrantComparison_inv_app]
  have ha := originalCompositeIso_hom_projected W' Q' R' q' r' qr' (F.obj X)
  have hd := congrArg (Construction.lift (F ⋙ W'.Q) hF).map
    (originalCompositeIso_inv_projected W Q R q r qr X)
  have hdId := hd.trans ((Construction.lift (F ⋙ W'.Q) hF).map_id (W.Q.obj (R.obj (Q.obj X))))
  have hb := originalLocalizedComparison_inv_projected W W' Q Q' F q q' hF cQ X
  have hc := originalLocalizedComparison_inv_projected W W' R R' F r r' hF cR (Q.obj X)
  have hMap := Functor.congr_hom (Construction.fac (R' ⋙ W'.Q) r') (cQ.inv.app X)
  change (Construction.lift (R' ⋙ W'.Q) r').map (W'.Q.map (cQ.inv.app X)) =
    W'.Q.map (R'.map (cQ.inv.app X)) at hMap
  have hbImage := (congrArg (Construction.lift (R' ⋙ W'.Q) r').map hb).trans hMap
  have hFactors := congrArg₂ (fun a d => (a ≫
      ((Construction.lift (R' ⋙ W'.Q) r').map
        ((originalLocalizedComparison W W' Q Q' F q q' hF cQ).inv.app (W.Q.obj X)) ≫
          (originalLocalizedComparison W W' R R' F r r' hF cR).inv.app (W.Q.obj (Q.obj X)))) ≫ d)
    ha hdId
  refine hFactors.trans ?_
  have hMiddle := congrArg₂ (fun b c => (𝟙 _ ≫ (b ≫ c)) ≫ 𝟙 _) hbImage hc
  refine hMiddle.trans ?_
  change (𝟙 (W'.Q.obj (R'.obj (Q'.obj (F.obj X)))) ≫
      (W'.Q.map (R'.map (cQ.inv.app X)) ≫ W'.Q.map (cR.inv.app (Q.obj X)))) ≫
        𝟙 (W'.Q.obj (F.obj (R.obj (Q.obj X)))) = _
  exact (congrArg (fun f => f ≫ 𝟙 (W'.Q.obj (F.obj (R.obj (Q.obj X)))))
    (Category.id_comp _)).trans ((Category.comp_id _).trans (W'.Q.map_comp _ _).symm)

end CategoryTheory.Localization
