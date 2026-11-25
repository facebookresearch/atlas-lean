/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.OriginalCompactSuccessorAttachments

set_option autoImplicit false
noncomputable section

universe w uD vD uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
open CategoryTheory.SmallObject.CompactRootBaseChange
open HomotopicalAlgebra HomotopicalAlgebra.FunctorInjective

attribute [local instance] constructionIndexWellFounded constructionIndexSuccOrder

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {kappa : Cardinal.{w}} [Fact kappa.IsRegular]
  [OrderBot kappa.ord.ToType] (d : CofibrantGenerationData C kappa)
  (kappaLP : Cardinal.{w}) [Fact kappaLP.IsRegular]
  [IsCardinalLocallyPresentable C kappaLP] (s : Functor.EssentialIndexData.{w} D C)
  (b : BoundedConstruction d kappaLP s.equivalence) {F G : D ⥤ C}
  (f : F ⟶ G) (hf : ∀ a : D, cofibrations C (f.app a))

-- Every original native successor is reached, including the empty initial transition.
example (gamma : ConstructionIndex (originalSliceHistoryIndex d kappaLP s b f hf))
    (hgamma : ¬IsMax gamma) :
    ∃ (F0 G0 : D ⥤ C)
      (u : F0 ⟶ (originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.obj gamma)
      (v : G0 ⟶ (originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.obj
        (Order.succ gamma)) (f0 : F0 ⟶ G0),
      compactCofibrationArrows D C b.cardinal (Arrow.mk f0) ∧
      IsPushout u f0
        ((originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.map
          (homOfLE (Order.le_succ gamma))) v :=
  originalCompactEverySuccessorAttachment d kappaLP s b f hf gamma hgamma

-- Both actual compact root/endpoints are derived for the same selected original increment.
example (p : originalSliceHistoryIndex d kappaLP s b f hf) (a : s.index) :
    IsCardinalPresentable (originalCompactScalarRoot d kappaLP s b f hf p a).root b.cardinal :=
  (originalCompactScalarRoot d kappaLP s b f hf p a).root_presentable

example (p : originalSliceHistoryIndex d kappaLP s b f hf) (a : s.index) :
    IsCardinalPresentable
      (originalCompactScalarRoot d kappaLP s b f hf p a).tree.endpointObj.right b.cardinal :=
  (originalCompactScalarRoot d kappaLP s b f hf p a).endpoint_presentable

-- Consume the full original scalar charts, both native source/target maps and both factor laws.
example (p : originalSliceHistoryIndex d kappaLP s b f hf) :
    letI := originalSliceComponentOrders d kappaLP s b f hf
    ∃ (F0 G0 : D ⥤ C)
      (u : F0 ⟶ (originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.obj
        (constructionLabel p))
      (v : G0 ⟶ (originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.obj
        (Order.succ (constructionLabel p))) (f0 : F0 ⟶ G0)
      (a0 : ∀ a : D, (originalCompactScalarRoot d kappaLP s b f hf p
        (s.equivalence.functor.obj a)).root ⟶ F0.obj a)
      (b0 : ∀ a : D, (originalCompactScalarRoot d kappaLP s b f hf p
        (s.equivalence.functor.obj a)).tree.endpointObj.right ⟶ G0.obj a),
      compactCofibrationArrows D C b.cardinal (Arrow.mk f0) ∧
      IsPushout u f0
        ((originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.map
          (homOfLE (Order.le_succ (constructionLabel p)))) v ∧
      ∀ a : D, IsPushout (a0 a)
          (originalCompactScalarRoot d kappaLP s b f hf p (s.equivalence.functor.obj a)).tree.hom
          (f0.app a) (b0 a) ∧
        a0 a ≫ u.app a =
          (originalCompactScalarRoot d kappaLP s b f hf p (s.equivalence.functor.obj a)).rootMap ≫
            (originalSliceBirth d kappaLP s b f hf p).intoBefore.toNatTrans.app
              (s.equivalence.functor.obj a) ≫
                (originalTransfiniteFiltrationBirthIso d kappaLP s b f hf p).inv.left.app a ∧
        b0 a ≫ v.app a =
          originalCompactScalarTargetMap d kappaLP s b f hf p (s.equivalence.functor.obj a) ≫
            (originalSliceBirth d kappaLP s b f hf p).patchInclusion.toNatTrans.app
              (s.equivalence.functor.obj a) ≫
                (originalTransfiniteFiltrationBirthIso d kappaLP s b f hf p).inv.right.app a :=
  originalCompactSuccessorAttachment d kappaLP s b f hf p
