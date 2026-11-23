/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowStableComparison
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingHomologyColimit
public import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.RealizationSingular

/-!
# Homology calibration of the actual stable opposite-row comparison

The established realization/singular homology isomorphisms put the actual
stable continuous comparison into the original nerve homology coordinates.
Every finite-stage restriction is the literal finite opposite-row map.
Composing with the ORIGINAL finite-BGL homology colimit preserves every
original cofan injection in every degree.

This owner constructs and calibrates the actual map. Its invertibility
still requires the intrinsic zero-grade fraction and eventual stabilization
argument; no such property is an input here.
-/

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The homology map of the actual stable continuous comparison, expressed
through the existing realization/singular isomorphisms for the SAME nerves. -/
public def finiteFreeRowStableHomologyComparison (A : AddCommGrpCat.{u}) (q : ℕ) :
    (nerve (ClassifyingCategory R)).homology (C := AddCommGrpCat.{u}) A q ⟶
      (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))).homology
        (C := AddCommGrpCat.{u}) A q :=
  (SSet.realizationSingularHomologyIso A (nerve (ClassifyingCategory R)) q).hom ≫
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{u} q).obj A).map
      (finiteFreeRowStableZeroComparison R) ≫
    (SSet.realizationSingularHomologyIso A
      (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))) q).inv

/-- The original finite-to-stable injection followed by the actual stable
comparison is the SAME original row-stage homology map, in every degree. -/
public theorem finiteFreeRowStableHomologyComparison_stage
    (A : AddCommGrpCat.{u}) (q n : ℕ) :
    SSet.homologyMap (C := AddCommGrpCat.{u})
      (nerveMap (finiteToStableCategoryMap R n).toFunctor) A q ≫
        finiteFreeRowStableHomologyComparison R A q =
      SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageZeroNerveMap R n) A q := by
  let X := nerve (ClassifyingCategory R)
  let Y := nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))
  let U := nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
  let i : U ⟶ X := nerveMap (finiteToStableCategoryMap R n).toFunctor
  let g : U ⟶ Y := finiteFreeRowStageZeroNerveMap R n
  let f := finiteFreeRowStableZeroComparison R
  let H := (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{u} q).obj A
  let eX := SSet.realizationSingularHomologyIso A X q
  let eY := SSet.realizationSingularHomologyIso A Y q
  let eU := SSet.realizationSingularHomologyIso A U q
  have hi : SSet.homologyMap (C := AddCommGrpCat.{u}) i A q ≫ eX.hom =
      eU.hom ≫ H.map (SSet.toTop.map i) :=
    SSet.realizationSingularHomologyIso_hom_naturality A i q
  have hg : SSet.homologyMap (C := AddCommGrpCat.{u}) g A q ≫ eY.hom =
      eU.hom ≫ H.map (SSet.toTop.map g) :=
    SSet.realizationSingularHomologyIso_hom_naturality A g q
  have hk : H.map (SSet.toTop.map g) = H.map (SSet.toTop.map i) ≫ H.map f :=
    finiteFreeRowStableZeroComparison_homology_stage R A q n
  change SSet.homologyMap (C := AddCommGrpCat.{u}) i A q ≫ (eX.hom ≫ H.map f ≫ eY.inv) =
    SSet.homologyMap (C := AddCommGrpCat.{u}) g A q
  calc
    SSet.homologyMap (C := AddCommGrpCat.{u}) i A q ≫ (eX.hom ≫ H.map f ≫ eY.inv) =
        (SSet.homologyMap (C := AddCommGrpCat.{u}) i A q ≫ eX.hom) ≫ H.map f ≫ eY.inv :=
      (Category.assoc _ _ _).symm
    _ = (eU.hom ≫ H.map (SSet.toTop.map i)) ≫ H.map f ≫ eY.inv :=
      congrArg (fun z => z ≫ H.map f ≫ eY.inv) hi
    _ = eU.hom ≫ (H.map (SSet.toTop.map i) ≫ H.map f) ≫ eY.inv := by
      simp only [Category.assoc]
    _ = eU.hom ≫ H.map (SSet.toTop.map g) ≫ eY.inv :=
      congrArg (fun z => eU.hom ≫ z ≫ eY.inv) hk.symm
    _ = (SSet.homologyMap (C := AddCommGrpCat.{u}) g A q ≫ eY.hom) ≫ eY.inv := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ eY.inv) hg.symm
    _ = SSet.homologyMap (C := AddCommGrpCat.{u}) g A q := by
      rw [Category.assoc, eY.hom_inv_id, Category.comp_id]

/-- The ORIGINAL finite-stage homology colimit mapped into the zero
component by the actual stable continuous comparison, in every degree. -/
public def finiteFreeRowHomologyColimitComparison (A : AddCommGrpCat.{u}) (q : ℕ) :
    colimit (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q) ⟶
      (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))).homology
        (C := AddCommGrpCat.{u}) A q :=
  (finiteBGLHomologyColimitIso R A q).hom ≫
    finiteFreeRowStableHomologyComparison R A q

/-- Every colimit injection is the ORIGINAL opposite-row finite-stage map;
this is the whole source calibration needed by the zero-grade fraction proof. -/
public theorem finiteFreeRowHomologyColimitComparison_ι
    (A : AddCommGrpCat.{u}) (q n : ℕ) :
    colimit.ι (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q) n ≫
        finiteFreeRowHomologyColimitComparison R A q =
      SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageZeroNerveMap R n) A q := by
  have hι := finiteBGLHomologyColimitIso_ι R A q n
  have hassoc := Category.assoc
    (colimit.ι
      (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q) n)
    (finiteBGLHomologyColimitIso R A q).hom
    (finiteFreeRowStableHomologyComparison R A q)
  unfold finiteFreeRowHomologyColimitComparison
  simp only [finiteBGLNerveDiagram, Functor.comp_obj,
    finiteClassifyingCategoryDiagram_obj, Cat.of_α] at hι hassoc ⊢
  have hpost := congrArg
    (fun z :
      (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).homology
          (C := AddCommGrpCat.{u}) A q ⟶
        (nerve (ClassifyingCategory R)).homology (C := AddCommGrpCat.{u}) A q =>
      z ≫ finiteFreeRowStableHomologyComparison R A q)
    hι
  exact hassoc.symm.trans
    (hpost.trans (finiteFreeRowStableHomologyComparison_stage R A q n))

/-- The actual stable continuous map is retained by the complete
realization/singular coordinate square, in every degree. -/
public theorem finiteFreeRowStableHomologyComparison_singular_square
    (A : AddCommGrpCat.{u}) (q : ℕ) :
    (SSet.realizationSingularHomologyIso A (nerve (ClassifyingCategory R)) q).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{u} q).obj A).map
          (finiteFreeRowStableZeroComparison R) =
      finiteFreeRowStableHomologyComparison R A q ≫
        (SSet.realizationSingularHomologyIso A
          (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))) q).hom := by
  let e := SSet.realizationSingularHomologyIso A
    (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))) q
  unfold finiteFreeRowStableHomologyComparison
  rw [Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id]

end AlgebraicKTheory.StableGL
