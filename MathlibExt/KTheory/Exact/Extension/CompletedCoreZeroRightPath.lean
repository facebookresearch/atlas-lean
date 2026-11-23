/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedCoreZeroRightCylinder
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaQuillenBComparison
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedNullhomotopy
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyMapPrecomp
public import MathlibExt.Topology.Category.TopCat.ProdMapPointwise

/-!
# EVERY-point carried-path constancy in the original restricted right fiber

Realize the WHOLE original right-comma cylinder restriction. Its exact
compact-open path field is constant at every original source point and
interval time. Source precomposition retains the same original homotopy
and clocks; no point or fiber map is inferred from a vertex or projection.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory Opposite
open CategoryTheory.CoreLocalizationComparison
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory Simplicial

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uC vC uNative

namespace AlgebraicKTheory.OriginalQZeroComparison

private theorem actualRealizedConstantCylinderPoint
    {X Y : SSet.{uNative}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (y : Y _⦋0⦌) (h : H.h = SSet.const y)
    (z : ↑(TopCat.I.{uNative} ⨯ SSet.toTop.obj X)) :
    SSet.realizeHomotopyMap X Y f g H z = SSet.realizedVertex y := by
  have hFirst : f = SSet.const y :=
    (SSet.Homotopy.h₀ H).symm.trans
      ((congrArg
        (fun a : X ⊗ (Δ[1] : SSet.{uNative}) ⟶ Y =>
          SSet.ι₀ (X := X) ≫ a) h).trans
            (SSet.comp_const (SSet.ι₀ (X := X)) y))
  have hFactor : H.h =
      CartesianMonoidalCategory.fst X (Δ[1] : SSet.{uNative}) ≫ f :=
    h.trans
      ((SSet.comp_const
        (CartesianMonoidalCategory.fst X (Δ[1] : SSet.{uNative})) y).symm.trans
          (congrArg (fun a : X ⟶ Y =>
            CartesianMonoidalCategory.fst X (Δ[1] : SSet.{uNative}) ≫ a) hFirst.symm))
  let x : SSet.toTop.obj X :=
    (Limits.prod.snd :
      TopCat.I.{uNative} ⨯ SSet.toTop.obj X ⟶ SSet.toTop.obj X) z
  have hMap : (SSet.toTop.map f).hom x = SSet.realizedVertex y :=
    (congrArg (fun a : X ⟶ Y => (SSet.toTop.map a).hom x) hFirst).trans
      ((congrArg
        (fun a : ContinuousMap (SSet.toTop.obj X) (SSet.toTop.obj Y) => a x)
        (SSet.toTop_map_const_hom (A := X) y)).trans rfl)
  exact (ConcreteCategory.congr_hom
    (SSet.realizeHomotopyMap_of_h_eq_fst H hFactor) z).trans
      ((TopCat.comp_app
        (Limits.prod.snd :
          TopCat.I.{uNative} ⨯ SSet.toTop.obj X ⟶ SSet.toTop.obj X)
        (SSet.toTop.map f) z).trans hMap)

private theorem actualRealizedHomotopySourcePoint
    {W X Y : SSet.{uNative}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (k : W ⟶ X) (t : unitInterval)
    (x : SSet.toTop.obj W) :
    SSet.realizeHomotopy X Y f g H (t, SSet.toTop.map k x) =
      SSet.realizeHomotopy W Y (k ≫ f) (k ≫ g) (H.precomp k) (t, x) := by
  let z := (TopCat.prodIsoProd TopCat.I (SSet.toTop.obj W)).inv
    (TopCat.I.homeomorph.symm t, x)
  have hProd : (Limits.prod.map (𝟙 TopCat.I.{uNative}) (SSet.toTop.map k)) z =
      (TopCat.prodIsoProd TopCat.I (SSet.toTop.obj X)).inv
        (TopCat.I.homeomorph.symm t, SSet.toTop.map k x) :=
    TopCat.prodMap_prodIso_inv_apply (SSet.toTop.map k) (TopCat.I.homeomorph.symm t) x
  have hReal := ConcreteCategory.congr_hom (SSet.realizeHomotopyMap_precomp H k) z
  change SSet.realizeHomotopyMap X Y f g H
      ((TopCat.prodIsoProd TopCat.I (SSet.toTop.obj X)).inv
        (TopCat.I.homeomorph.symm t, SSet.toTop.map k x)) =
    SSet.realizeHomotopyMap W Y (k ≫ f) (k ≫ g) (H.precomp k) z
  exact (congrArg (SSet.realizeHomotopyMap X Y f g H) hProd).symm.trans
    ((TopCat.comp_app _ _ z).symm.trans hReal)

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

private theorem actualOriginalRightCarriedPathPoint
    (x : SSet.toTop.obj (nerve ((SInverse (Core C) (Core C))ᵒᵖ)))
    (t : TopCat.I.{max uC vC}) :
    TopCat.homotopyFiberPath
        (SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0}
          (ExtensionCategory.localizedTarget (C := C)).op))
        (SSet.realizedVertex (ComposableArrows.mk₀ (op (⟨(0 : C)⟩ : QuillenQ C))))
        (SSet.rightCommaHomotopyFiberComparison.{uC, 0, max uC vC}
          (ExtensionCategory.localizedTarget (C := C)).op (op (⟨(0 : C)⟩ : QuillenQ C))
          (SSet.toTop.map (nerveMapCommonHomUp.{uC, max uC vC, 0}
            (completedCoreOriginalRightCommaFunctor (C := C))) x)) t =
      SSet.realizedVertex (ComposableArrows.mk₀ (op (⟨(0 : C)⟩ : QuillenQ C))) := by
  let p := (ExtensionCategory.localizedTarget (C := C)).op
  let q := op (⟨(0 : C)⟩ : QuillenQ C)
  let X : SSet.{max uC vC} := nerve (CostructuredArrow p q)
  let Y : SSet.{max uC vC} := nerve ((QuillenQ C)ᵒᵖ)
  let W : SSet.{max uC vC} := nerve ((SInverse (Core C) (Core C))ᵒᵖ)
  let J := completedCoreOriginalRightCommaFunctor (C := C)
  let k : W ⟶ X := nerveMapCommonHomUp.{uC, max uC vC, 0} J
  let f : X ⟶ Y := nerveMapCommonHom.{uC, max uC vC, 0} (CostructuredArrow.proj p q ⋙ p)
  let g : X ⟶ Y := nerveMapCommonHom.{uC, max uC vC, 0}
    ((Functor.const (CostructuredArrow p q)).obj q)
  let H : SSet.Homotopy f g := SSet.rightCommaArrowNerveHomotopy.{uC, 0, max uC vC} p q
  let b : Y _⦋0⦌ := ComposableArrows.mk₀ q
  have hCylinder : (H.precomp k).h = SSet.const b :=
    (SSet.Homotopy.precomp_h H k).trans
      (completedCoreOriginalRightCommaH_restrict_eq_const (C := C))
  have hPath : TopCat.homotopyFiberPath
      (SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0} p))
      (SSet.realizedVertex b)
      (SSet.rightCommaHomotopyFiberComparison.{uC, 0, max uC vC} p q (SSet.toTop.map k x)) t =
      SSet.realizeHomotopy X Y f g H (TopCat.I.homeomorph t, SSet.toTop.map k x) :=
    congrArg (fun gamma : TopCat.pathObject (SSet.toTop.obj Y) => gamma t)
      (ConcreteCategory.congr_hom
        (SSet.rightCommaHomotopyFiberComparison_path.{uC, 0, max uC vC} p q)
        (SSet.toTop.map k x))
  have hPrecomp := actualRealizedHomotopySourcePoint H k (TopCat.I.homeomorph t) x
  have hConst : SSet.realizeHomotopy W Y (k ≫ f) (k ≫ g) (H.precomp k)
      (TopCat.I.homeomorph t, x) = SSet.realizedVertex b :=
    actualRealizedConstantCylinderPoint (H.precomp k) b hCylinder
      ((TopCat.prodIsoProd TopCat.I (SSet.toTop.obj W)).inv
        (TopCat.I.homeomorph.symm (TopCat.I.homeomorph t), x))
  exact hPath.trans (hPrecomp.trans hConst)

/-- The ORIGINAL full right-fiber carried path is constant on EVERY original source point and time.
-/
public theorem completedCoreOriginalRightFiber_path_const
    (x : SSet.toTop.obj (nerve ((SInverse (Core C) (Core C))ᵒᵖ)))
    (t : TopCat.I.{max uC vC}) :
    TopCat.homotopyFiberPath
        (SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0}
          (ExtensionCategory.localizedTarget (C := C)).op))
        (SSet.realizedVertex (ComposableArrows.mk₀ (op (⟨(0 : C)⟩ : QuillenQ C))))
        (SSet.rightCommaHomotopyFiberComparison.{uC, 0, max uC vC}
          (ExtensionCategory.localizedTarget (C := C)).op (op (⟨(0 : C)⟩ : QuillenQ C))
          (SSet.toTop.map (nerveMapCommonHomUp.{uC, max uC vC, 0}
            (completedCoreOriginalRightCommaFunctor (C := C))) x)) t =
      SSet.realizedVertex (ComposableArrows.mk₀ (op (⟨(0 : C)⟩ : QuillenQ C))) :=
  actualOriginalRightCarriedPathPoint x t

end AlgebraicKTheory.OriginalQZeroComparison

end
