/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOriginalFiberComparisonBoundary
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.Stable.FiberHomComparison

/-!
# The original symmetric fiber boundary comparison on all Omega Hom tests

The actual suspended-fiber comparison, original I replacement, Q-cofiber
boundary, caller-chosen enriched fibers and full symmetric Omega family are
retained. Its boundary equation acts on every original integer Hom test.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
namespace OriginalFiberBoundary

open PointedCGWH.Spectra.Symmetric.Stable

attribute [local instance] Native.modelCategory Native.allObjectsFibrant

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev SymC := Actual.SymmetricCarrier.{u, v}
private abbrev J := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev H := toHomotopyCategory SymC.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := J.{u, v})
private abbrev S := OriginalISuspension.suspension (B := B) (I := J.{u, v})
private abbrev CQ := CofiberNullity.cofiberQ (B := B) (I := J.{u, v})
private abbrev R := cotensor (I := J.{u, v}) PointedCGWH.sphereOne.{u, v}
private abbrev T := tensorLeft (A := J.{u, v}) PointedCGWH.sphereOne.{u, v}
private abbrev scalarAdj := ScalarLeibniz.adjunction (A := J.{u, v}) PointedCGWH.sphereOne.{u, v}

private instance symmetricSphereQuillen : scalarAdj.{u, v}.IsQuillenAdjunction := by
  let _ : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
    PointedCGWH.modelCategory.sphereOne_isCofibrant
  exact ScalarCompatibility.scalar_isQuillen PointedCGWH.sphereOne

attribute [local instance] Replacement.isCofibrant_cofibrantReplacement

/-- The same original boundary and suspended-fiber map recover the caller's first projection. -/
theorem symmetricCofiberToFiberHom_connecting
    (a : ∀ F : Arrow SymC.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F)) (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : SymC.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : PointedCGWH.Spectra.Symmetric.Stable.ShiftedHom.test (B := B)
      (q + 1) F.obj.left E) :
    PointedCGWH.Spectra.Symmetric.Stable.FiberHomComparison.cofiberToFiberHom
        (B := B) a ha q F E hE
        (PointedCGWH.Spectra.Symmetric.Stable.ShiftedPuppeTests.connecting
          (B := B) q F.obj E hE g) = H.map (a F.obj).fst ≫ g := by
  let ψ : H.obj (S.obj (Q.obj (a F.obj).pt)) ⟶ H.obj (CQ.obj F.obj) :=
    (OriginalFiberComparison.originalComparison (B := B) a ha Actual.symmetricFamily).app F
  let δ : H.obj (CQ.obj F.obj) ⟶ H.obj (S.obj (Q.obj F.obj.left)) :=
    PointedCGWH.Spectra.Symmetric.Stable.ShiftedPuppeTests.boundaryHo (B := B) F.obj
  let eF := PointedCGWH.Spectra.Symmetric.Stable.ShiftedHom.suspensionHomEquiv
    (B := B) q (a F.obj).pt E hE
  let eX := PointedCGWH.Spectra.Symmetric.Stable.ShiftedHom.suspensionHomEquiv
    (B := B) q F.obj.left E hE
  have hBoundary : ψ ≫ δ = H.map (S.map (Q.map (a F.obj).fst)) :=
    OriginalFiberComparison.originalComparison_boundary (B := B) a ha Actual.symmetricFamily F
  calc
    _ = eF (ψ ≫ (δ ≫ eX.symm g)) := rfl
    _ = eF ((ψ ≫ δ) ≫ eX.symm g) :=
      congrArg eF (Category.assoc ψ δ (eX.symm g)).symm
    _ = eF (H.map (S.map (Q.map (a F.obj).fst)) ≫ eX.symm g) :=
      congrArg (fun k => eF (k ≫ eX.symm g)) hBoundary
    _ = H.map (a F.obj).fst ≫ eX (eX.symm g) :=
      PointedCGWH.Spectra.Symmetric.Stable.ShiftedHom.suspensionHomEquiv_source
        (B := B) q (a F.obj).fst E hE (eX.symm g)
    _ = H.map (a F.obj).fst ≫ g :=
      congrArg (fun k => H.map (a F.obj).fst ≫ k) (eX.apply_symm_apply g)

/-- Every caller-chosen Q-cofiber retains the same original boundary and fiber projection. -/
theorem symmetricChosenCofiberToFiberHom_connecting
    (a : ∀ F : Arrow SymC.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    (d : ∀ F : Arrow SymC.{u, v}, PushoutCocone
      ((OriginalICone.inclusion (B := B) (I := J)).app F.left) F.hom)
    (hd : ∀ F, IsColimit (d F)) (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : SymC.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : PointedCGWH.Spectra.Symmetric.Stable.ShiftedHom.test (B := B)
      (q + 1) F.obj.left E) :
    PointedCGWH.Spectra.Symmetric.Stable.FiberHomComparison.chosenCofiberToFiberHom
        (B := B) a ha d hd q F E hE
        (PointedCGWH.Spectra.Symmetric.Stable.ChosenCofiberTests.connecting
          (B := B) d hd q F.obj E hE g) = H.map (a F.obj).fst ≫ g := by
  let r := PointedCGWH.Spectra.Symmetric.Stable.FiberHomComparison.cofiberToFiberHom
    (B := B) a ha q F E hE
  exact (congrArg r
    (PointedCGWH.Spectra.Symmetric.Stable.ChosenCofiberTests.testHomEquiv_connecting
      (B := B) d hd q F.obj E hE g)).trans
        (symmetricCofiberToFiberHom_connecting a ha q F E hE g)

/-- The caller's fiber-inclusion image is the image of the original cofiber restriction kernel. -/
theorem symmetricFiberRestriction_image_iff
    (a : ∀ F : Arrow SymC.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F)) (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : SymC.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) (q + 1) (a F.obj).pt E) :
    (∃ h : ShiftedHom.test (B := B) (q + 1) F.obj.left E,
      H.map (a F.obj).fst ≫ h = g) ↔
    (∃ k : ShiftedHom.test (B := B) q (CQ.obj F.obj) E,
      FiberHomComparison.cofiberToFiberHom (B := B) a ha q F E hE k = g ∧
      ShiftedPuppeTests.targetRestriction (B := B) q F.obj E k =
        OrdinaryHoCofiberKernel.nullHom F.obj.right ((ShiftedTargets.target q).obj E)) := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨ShiftedPuppeTests.connecting (B := B) q F.obj E hE h,
      (symmetricCofiberToFiberHom_connecting a ha q F E hE h).trans hh, ?_⟩
    exact (ShiftedPuppeTests.exact_at_cofiber (B := B) q F.obj E hE _).mp ⟨h, rfl⟩
  · rintro ⟨k, hk, hNull⟩
    obtain ⟨h, hh⟩ := (ShiftedPuppeTests.exact_at_cofiber (B := B) q F.obj E hE k).mpr hNull
    refine ⟨h, ?_⟩
    calc
      H.map (a F.obj).fst ≫ h =
          FiberHomComparison.cofiberToFiberHom (B := B) a ha q F E hE
            (ShiftedPuppeTests.connecting (B := B) q F.obj E hE h) :=
        (symmetricCofiberToFiberHom_connecting a ha q F E hE h).symm
      _ = FiberHomComparison.cofiberToFiberHom (B := B) a ha q F E hE k :=
        congrArg (FiberHomComparison.cofiberToFiberHom (B := B) a ha q F E hE) hh
      _ = g := hk

/-- The actual scalar adjunct carries the original Q-fiber boundary to the same Q projection. -/
theorem symmetricSourceLoopComparisonQ_boundary
    (a : ∀ F : Arrow SymC.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory) :
    OriginalFiberComparison.sourceLoopComparisonQApp (B := B) a ha Actual.symmetricFamily F ≫
        H.map (R.map (OriginalFiberComparison.originalQCofiberBoundary (B := B) F.obj)) =
      H.map (Q.map (a F.obj).fst) ≫
        QuillenOrdinaryHoHom.homEquiv scalarAdj (Q.obj F.obj.left) (S.obj (Q.obj F.obj.left))
          ((ScalarSphereSuspension.originalISuspensionQIsoSphereQ
            (B := B) (I := J)).inv.app F.obj.left) := by
  let ψ : H.obj (S.obj (Q.obj (a F.obj).pt)) ⟶ H.obj (CQ.obj F.obj) :=
    (OriginalFiberComparison.originalComparison (B := B) a ha Actual.symmetricFamily).app F
  let eF : H.obj (T.obj (Q.obj (a F.obj).pt)) ⟶ H.obj (S.obj (Q.obj (a F.obj).pt)) :=
    (ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B) (I := J)).inv.app (a F.obj).pt
  let eX : H.obj (T.obj (Q.obj F.obj.left)) ⟶ H.obj (S.obj (Q.obj F.obj.left)) :=
    (ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B) (I := J)).inv.app F.obj.left
  let d : CQ.obj F.obj ⟶ S.obj (Q.obj F.obj.left) :=
    OriginalFiberComparison.originalQCofiberBoundary (B := B) F.obj
  let M := QuillenOrdinaryHoHom.homEquiv scalarAdj
    (Q.obj (a F.obj).pt) (S.obj (Q.obj F.obj.left))
  have hBoundary : ψ ≫ H.map d = H.map (S.map (Q.map (a F.obj).fst)) :=
    OriginalFiberComparison.originalComparison_boundary (B := B) a ha Actual.symmetricFamily F
  have hSource : eF ≫ H.map (S.map (Q.map (a F.obj).fst)) =
      H.map (T.map (Q.map (a F.obj).fst)) ≫ eX :=
    (ScalarSphereSuspension.originalISuspensionQIsoSphereQ_inv_naturality
      (B := B) (a F.obj).fst).symm
  calc
    _ = M ((eF ≫ ψ) ≫ H.map d) :=
      (QuillenOrdinaryHoHom.homEquiv_naturality_right scalarAdj
        (Q.obj (a F.obj).pt) (eF ≫ ψ) d).symm
    _ = M (eF ≫ (ψ ≫ H.map d)) := congrArg M (Category.assoc eF ψ (H.map d))
    _ = M (eF ≫ H.map (S.map (Q.map (a F.obj).fst))) :=
      congrArg M (congrArg (fun k => eF ≫ k) hBoundary)
    _ = M (H.map (T.map (Q.map (a F.obj).fst)) ≫ eX) := congrArg M hSource
    _ = H.map (Q.map (a F.obj).fst) ≫
        QuillenOrdinaryHoHom.homEquiv scalarAdj (Q.obj F.obj.left) (S.obj (Q.obj F.obj.left)) eX :=
      QuillenOrdinaryHoHom.homEquiv_naturality_left scalarAdj
        (S.obj (Q.obj F.obj.left)) (Q.map (a F.obj).fst) eX

/-- The original Q counit retains the entire caller-fiber boundary and scalar unit word. -/
theorem symmetricSourceLoopComparison_boundary
    (a : ∀ F : Arrow SymC.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory) :
    (OriginalFiberComparison.sourceLoopComparison (B := B) a ha Actual.symmetricFamily).app F ≫
        H.map (R.map (OriginalFiberComparison.originalQCofiberBoundary (B := B) F.obj)) =
      H.map (a F.obj).fst ≫
        (Replacement.cofibrantReplacementProjectionIso (B := B) (A := J)).inv.app F.obj.left ≫
        QuillenOrdinaryHoHom.homEquiv scalarAdj (Q.obj F.obj.left) (S.obj (Q.obj F.obj.left))
          ((ScalarSphereSuspension.originalISuspensionQIsoSphereQ
            (B := B) (I := J)).inv.app F.obj.left) := by
  let eF : H.obj (Q.obj (a F.obj).pt) ≅ H.obj (a F.obj).pt :=
    (OriginalFiberComparison.originalQFiberCounitHoIso
      (B := B) a ha Actual.symmetricFamily).app F
  let eX : H.obj (Q.obj F.obj.left) ≅ H.obj F.obj.left :=
    (Replacement.cofibrantReplacementProjectionIso (B := B) (A := J)).app F.obj.left
  let δ : H.obj (R.obj (CQ.obj F.obj)) ⟶ H.obj (R.obj (S.obj (Q.obj F.obj.left))) :=
    H.map (R.map (OriginalFiberComparison.originalQCofiberBoundary (B := B) F.obj))
  let uX : H.obj (Q.obj F.obj.left) ⟶ H.obj (R.obj (S.obj (Q.obj F.obj.left))) :=
    QuillenOrdinaryHoHom.homEquiv scalarAdj (Q.obj F.obj.left)
    (S.obj (Q.obj F.obj.left))
    ((ScalarSphereSuspension.originalISuspensionQIsoSphereQ
      (B := B) (I := J)).inv.app F.obj.left)
  let L : H.obj (a F.obj).pt ⟶ H.obj (R.obj (CQ.obj F.obj)) :=
    (OriginalFiberComparison.sourceLoopComparison (B := B) a ha Actual.symmetricFamily).app F
  let LQ : H.obj (Q.obj (a F.obj).pt) ⟶ H.obj (R.obj (CQ.obj F.obj)) :=
    OriginalFiberComparison.sourceLoopComparisonQApp (B := B) a ha Actual.symmetricFamily F
  have hCounit : eF.hom ≫ L = LQ :=
    OriginalFiberComparison.sourceLoopComparison_counit (B := B) a ha Actual.symmetricFamily F
  have hSource : eF.hom ≫ H.map (a F.obj).fst = H.map (Q.map (a F.obj).fst) ≫ eX.hom :=
    ((Replacement.cofibrantReplacementProjectionIso (B := B) (A := J)).hom.naturality
      (a F.obj).fst).symm
  have hUnit : H.map (Q.map (a F.obj).fst) ≫ uX =
      (H.map (Q.map (a F.obj).fst) ≫ eX.hom) ≫ (eX.inv ≫ uX) := by
    apply Eq.symm
    calc
      (H.map (Q.map (a F.obj).fst) ≫ eX.hom) ≫ (eX.inv ≫ uX) =
          H.map (Q.map (a F.obj).fst) ≫ (eX.hom ≫ (eX.inv ≫ uX)) := Category.assoc _ _ _
      _ = H.map (Q.map (a F.obj).fst) ≫ uX :=
        congrArg (fun k => H.map (Q.map (a F.obj).fst) ≫ k) (eX.hom_inv_id_assoc uX)
  change L ≫ δ = H.map (a F.obj).fst ≫ (eX.inv ≫ uX)
  apply (cancel_epi eF.hom).mp
  calc
    eF.hom ≫ (L ≫ δ) = (eF.hom ≫ L) ≫ δ := (Category.assoc _ _ _).symm
    _ = LQ ≫ δ := congrArg (fun k => k ≫ δ) hCounit
    _ = H.map (Q.map (a F.obj).fst) ≫ uX := symmetricSourceLoopComparisonQ_boundary a ha F
    _ = (H.map (Q.map (a F.obj).fst) ≫ eX.hom) ≫ (eX.inv ≫ uX) := hUnit
    _ = (eF.hom ≫ H.map (a F.obj).fst) ≫ (eX.inv ≫ uX) :=
      congrArg (fun k => k ≫ (eX.inv ≫ uX)) hSource.symm
    _ = eF.hom ≫ (H.map (a F.obj).fst ≫ (eX.inv ≫ uX)) := Category.assoc _ _ _

/-- Every whole original K-right Arrow square retains the complete source-loop boundary word. -/
theorem symmetricSourceLoopComparison_boundary_naturality
    (a : ∀ F : Arrow SymC.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    {F G : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory}
    (φ : F ⟶ G) :
    H.map (Diagrams.FiberGeometry.chosenFiberMap φ.hom
      (a F.obj) (a G.obj) (ha G.obj)) ≫
        ((OriginalFiberComparison.sourceLoopComparison (B := B) a ha Actual.symmetricFamily).app G ≫
          H.map (R.map (OriginalFiberComparison.originalQCofiberBoundary (B := B) G.obj))) =
      ((OriginalFiberComparison.sourceLoopComparison (B := B) a ha Actual.symmetricFamily).app F ≫
        H.map (R.map (OriginalFiberComparison.originalQCofiberBoundary (B := B) F.obj))) ≫
          H.map (R.map (S.map (Q.map φ.hom.left))) := by
  let α : H.obj (a F.obj).pt ⟶ H.obj (a G.obj).pt :=
    H.map (Diagrams.FiberGeometry.chosenFiberMap φ.hom (a F.obj) (a G.obj) (ha G.obj))
  let LF : H.obj (a F.obj).pt ⟶ H.obj (R.obj (CQ.obj F.obj)) :=
    (OriginalFiberComparison.sourceLoopComparison (B := B) a ha Actual.symmetricFamily).app F
  let LG : H.obj (a G.obj).pt ⟶ H.obj (R.obj (CQ.obj G.obj)) :=
    (OriginalFiberComparison.sourceLoopComparison (B := B) a ha Actual.symmetricFamily).app G
  let β : H.obj (R.obj (CQ.obj F.obj)) ⟶ H.obj (R.obj (CQ.obj G.obj)) :=
    H.map (R.map (CQ.map φ.hom))
  let dF : H.obj (R.obj (CQ.obj F.obj)) ⟶ H.obj (R.obj (S.obj (Q.obj F.obj.left))) :=
    H.map (R.map (OriginalFiberComparison.originalQCofiberBoundary (B := B) F.obj))
  let dG : H.obj (R.obj (CQ.obj G.obj)) ⟶ H.obj (R.obj (S.obj (Q.obj G.obj.left))) :=
    H.map (R.map (OriginalFiberComparison.originalQCofiberBoundary (B := B) G.obj))
  let γ : H.obj (R.obj (S.obj (Q.obj F.obj.left))) ⟶ H.obj (R.obj (S.obj (Q.obj G.obj.left))) :=
    H.map (R.map (S.map (Q.map φ.hom.left)))
  have hLoop : α ≫ LG = LF ≫ β :=
    OriginalFiberComparison.sourceLoopComparison_naturality (B := B) a ha Actual.symmetricFamily φ
  have hBoundary : β ≫ dG = dF ≫ γ := by
    let bF := OriginalFiberComparison.originalQCofiberBoundary (B := B) F.obj
    let bG := OriginalFiberComparison.originalQCofiberBoundary (B := B) G.obj
    let t := S.map (Q.map φ.hom.left)
    have hBase : CQ.map φ.hom ≫ bG = bF ≫ t :=
      OriginalFiberComparison.originalQCofiberBoundary_naturality (B := B) φ.hom
    have hR : R.map (CQ.map φ.hom) ≫ R.map bG = R.map bF ≫ R.map t :=
      (R.map_comp (CQ.map φ.hom) bG).symm.trans
        ((R.congr_map hBase).trans (R.map_comp bF t))
    exact (H.map_comp (R.map (CQ.map φ.hom)) (R.map bG)).symm.trans
      ((H.congr_map hR).trans (H.map_comp (R.map bF) (R.map t)))
  calc
    _ = (α ≫ LG) ≫ dG := (Category.assoc α LG dG).symm
    _ = (LF ≫ β) ≫ dG := congrArg (fun k => k ≫ dG) hLoop
    _ = LF ≫ (β ≫ dG) := Category.assoc LF β dG
    _ = LF ≫ (dF ≫ γ) := congrArg (fun k => LF ≫ k) hBoundary
    _ = (LF ≫ dF) ≫ γ := (Category.assoc LF dF γ).symm

/-- Both arbitrary caller-fiber families retain the same entire source-loop boundary. -/
theorem symmetricSourceLoopComparison_boundary_choice
    (a : ∀ F : Arrow SymC.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    (b : ∀ F : Arrow SymC.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (hb : ∀ F, IsLimit (b F))
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory) :
    H.map (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
      Diagrams.zeroDiagram_isZero a ha b hb F.obj).hom ≫
        ((OriginalFiberComparison.sourceLoopComparison (B := B) b hb Actual.symmetricFamily).app F ≫
          H.map (R.map (OriginalFiberComparison.originalQCofiberBoundary (B := B) F.obj))) =
      (OriginalFiberComparison.sourceLoopComparison (B := B) a ha Actual.symmetricFamily).app F ≫
        H.map (R.map (OriginalFiberComparison.originalQCofiberBoundary (B := B) F.obj)) := by
  let δ : H.obj (R.obj (CQ.obj F.obj)) ⟶ H.obj (R.obj (S.obj (Q.obj F.obj.left))) :=
    H.map (R.map (OriginalFiberComparison.originalQCofiberBoundary (B := B) F.obj))
  let γ : H.obj (a F.obj).pt ⟶ H.obj (b F.obj).pt :=
    H.map (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
      Diagrams.zeroDiagram_isZero a ha b hb F.obj).hom
  let LA : H.obj (a F.obj).pt ⟶ H.obj (R.obj (CQ.obj F.obj)) :=
    (OriginalFiberComparison.sourceLoopComparison (B := B) a ha Actual.symmetricFamily).app F
  let LB : H.obj (b F.obj).pt ⟶ H.obj (R.obj (CQ.obj F.obj)) :=
    (OriginalFiberComparison.sourceLoopComparison (B := B) b hb Actual.symmetricFamily).app F
  have hChoice : γ ≫ LB = LA :=
    OriginalFiberComparison.sourceLoopComparison_choice (B := B) a ha b hb Actual.symmetricFamily F
  exact (Category.assoc γ LB δ).symm.trans (congrArg (fun k => k ≫ δ) hChoice)

/-- The whole inverse original limit comparison retains that same source-loop boundary. -/
theorem symmetricSourceLoopComparison_boundary_choice_inv
    (a : ∀ F : Arrow SymC.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    (b : ∀ F : Arrow SymC.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (hb : ∀ F, IsLimit (b F))
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory) :
    H.map (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
      Diagrams.zeroDiagram_isZero a ha b hb F.obj).inv ≫
        ((OriginalFiberComparison.sourceLoopComparison (B := B) a ha Actual.symmetricFamily).app F ≫
          H.map (R.map (OriginalFiberComparison.originalQCofiberBoundary (B := B) F.obj))) =
      (OriginalFiberComparison.sourceLoopComparison (B := B) b hb Actual.symmetricFamily).app F ≫
        H.map (R.map (OriginalFiberComparison.originalQCofiberBoundary (B := B) F.obj)) := by
  let e : H.obj (a F.obj).pt ≅ H.obj (b F.obj).pt :=
    H.mapIso (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
      Diagrams.zeroDiagram_isZero a ha b hb F.obj)
  let δ : H.obj (R.obj (CQ.obj F.obj)) ⟶ H.obj (R.obj (S.obj (Q.obj F.obj.left))) :=
    H.map (R.map (OriginalFiberComparison.originalQCofiberBoundary (B := B) F.obj))
  let LA : H.obj (a F.obj).pt ⟶ H.obj (R.obj (CQ.obj F.obj)) :=
    (OriginalFiberComparison.sourceLoopComparison (B := B) a ha Actual.symmetricFamily).app F
  let LB : H.obj (b F.obj).pt ⟶ H.obj (R.obj (CQ.obj F.obj)) :=
    (OriginalFiberComparison.sourceLoopComparison (B := B) b hb Actual.symmetricFamily).app F
  have hChoice : e.hom ≫ (LB ≫ δ) = LA ≫ δ :=
    symmetricSourceLoopComparison_boundary_choice a ha b hb F
  exact (congrArg (fun k => e.inv ≫ k) hChoice).symm.trans (e.inv_hom_id_assoc (LB ≫ δ))

end OriginalFiberBoundary
end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
