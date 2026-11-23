/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellFundamentalGroupQuotient
public import MathlibExt.AlgebraicTopology.LocalCoefficient.RegularRelativeComparison
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Topology.Category.TopCat.EpiMono

/-!
# Regular coefficients for the original subgroup attachment

The coefficient stalk at the image of the original chosen point identifies
as an integral module with the literal group ring of the original quotient fundamental group.
Its coordinate is computed from the actual van Kampen quotient equivalence.
The regular path convention sends a positive loop to right multiplication
by the inverse quotient label.

These project-derived coordinate formulas describe the project's quotient
covering model for the cell construction requested in Weibel, The K-book,
Exercise IV.1.4 (printed p. 273). Both the quotient group and coefficient
paths come from the original attachment.

This stalk coordinate is not a relative cell-basis or acyclicity assertion.
-/

noncomputable section

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicTopology.LoopCellAttachment

/-- The actual regular coefficient stalk identifies as an integral module with the original quotient
group ring. -/
noncomputable def regularQuotientGroupRingIso
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    (CategoryTheory.regularPathModuleCoefficientFunctor
        (_root_.FundamentalGroupoid.mk (inclusion X x P x))).obj
          (_root_.FundamentalGroupoid.mk (inclusion X x P x)) ≅
      ModuleCat.of ℤ (MonoidAlgebra ℤ (FundamentalGroup X x ⧸ P)) := by
  let Y : TopCat.{u} := space X x P
  let y : Y := inclusion X x P x
  let e : FundamentalGroup X x ⧸ P ≃* FundamentalGroup Y y :=
    fundamentalGroupQuotientMulEquiv X x P
  exact TopCat.regularBasedGroupRingIso Y y ≪≫
    (MonoidAlgebra.domCongr ℤ ℤ e.symm).toLinearEquiv.toModuleIso

/-- Every original coefficient path retains its inverse quotient label and every integer. -/
theorem regularQuotientGroupRingIso_hom_zsmul
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (γ : _root_.FundamentalGroupoid.mk (inclusion X x P x) ⟶
      _root_.FundamentalGroupoid.mk (inclusion X x P x)) (z : ℤ) :
    (regularQuotientGroupRingIso X x P).hom (z • FreeAbelianGroup.of γ) =
      MonoidAlgebra.single
        (((fundamentalGroupQuotientMulEquiv X x P).symm
          (FundamentalGroup.fromArrow γ))⁻¹) z := by
  let Y : TopCat.{u} := space X x P
  let y : Y := inclusion X x P x
  let e := fundamentalGroupQuotientMulEquiv X x P
  let d := MonoidAlgebra.domCongr ℤ ℤ e.symm
  let A : ModuleCat.{u} ℤ := (CategoryTheory.regularPathModuleCoefficientFunctor
    (_root_.FundamentalGroupoid.mk y)).obj (_root_.FundamentalGroupoid.mk y)
  let R : Type u := MonoidAlgebra ℤ (FundamentalGroup X x ⧸ P)
  have hRegular : (TopCat.regularBasedGroupRingIso Y y).hom
      (z • (FreeAbelianGroup.of γ : A)) =
        MonoidAlgebra.single (FundamentalGroup.fromArrow γ)⁻¹ z :=
    TopCat.regularBasedGroupRingIso_hom_zsmul Y y γ z
  have hMap : d (MonoidAlgebra.single (FundamentalGroup.fromArrow γ)⁻¹ z) =
      MonoidAlgebra.single (e.symm ((FundamentalGroup.fromArrow γ)⁻¹)) z :=
    MonoidAlgebra.domCongr_single (R := ℤ) (A := ℤ) e.symm _ z
  have hInverse : e.symm ((FundamentalGroup.fromArrow γ)⁻¹) =
      (e.symm (FundamentalGroup.fromArrow γ))⁻¹ :=
    e.symm.toMonoidHom.map_inv (FundamentalGroup.fromArrow γ)
  have hValue : (regularQuotientGroupRingIso X x P).hom
      (z • (FreeAbelianGroup.of γ : A)) =
        d ((TopCat.regularBasedGroupRingIso Y y).hom (z • (FreeAbelianGroup.of γ : A))) := rfl
  exact hValue.trans ((congrArg (fun a => (d a : R)) hRegular).trans
    (hMap.trans (congrArg (fun q => MonoidAlgebra.single q z) hInverse)))

/-- An original quotient-ring basis element returns its actual inverse loop coefficient path. -/
theorem regularQuotientGroupRingIso_inv_single
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (q : FundamentalGroup X x ⧸ P) (z : ℤ) :
    (regularQuotientGroupRingIso X x P).inv (MonoidAlgebra.single q z) =
      z • FreeAbelianGroup.of (FundamentalGroup.toArrow
        ((fundamentalGroupQuotientMulEquiv X x P q)⁻¹)) := by
  let Y : TopCat.{u} := space X x P
  let y : Y := inclusion X x P x
  let e : FundamentalGroup X x ⧸ P ≃* FundamentalGroup Y y :=
    fundamentalGroupQuotientMulEquiv X x P
  let d := MonoidAlgebra.domCongr ℤ ℤ e.symm
  let A : ModuleCat.{u} ℤ := (CategoryTheory.regularPathModuleCoefficientFunctor
    (_root_.FundamentalGroupoid.mk y)).obj (_root_.FundamentalGroupoid.mk y)
  let B : ModuleCat.{u} ℤ := ModuleCat.of ℤ (MonoidAlgebra ℤ (FundamentalGroup Y y))
  let C : ModuleCat.{u} ℤ := ModuleCat.of ℤ (MonoidAlgebra ℤ (FundamentalGroup X x ⧸ P))
  let g : A ≅ B := TopCat.regularBasedGroupRingIso Y y
  have hDom : d.symm (MonoidAlgebra.single q z) = MonoidAlgebra.single (e q) z := by
    simpa only [d, MonoidAlgebra.domCongr_symm, MulEquiv.symm_symm] using
      (MonoidAlgebra.domCongr_single (R := ℤ) (A := ℤ) e q z)
  have hValue : (regularQuotientGroupRingIso X x P).inv (MonoidAlgebra.single q z) =
      g.inv (d.symm (MonoidAlgebra.single q z)) := by
    rfl
  have hRegular : g.inv (MonoidAlgebra.single (e q) z) =
      z • (FreeAbelianGroup.of (FundamentalGroup.toArrow ((e q)⁻¹)) : A) :=
    TopCat.regularBasedGroupRingIso_inv_single Y y (e q) z
  exact hValue.trans ((congrArg (fun a : B => g.inv a) hDom).trans hRegular)

/-- Positive loop transport keeps the actual inverse quotient convention in the group ring. -/
theorem regularQuotientGroupRingIso_postcomp_positive
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (a : FundamentalGroup (space X x P) (inclusion X x P x))
    (t : (CategoryTheory.regularPathModuleCoefficientFunctor
      (_root_.FundamentalGroupoid.mk (inclusion X x P x))).obj
        (_root_.FundamentalGroupoid.mk (inclusion X x P x))) :
    (regularQuotientGroupRingIso X x P).hom
        ((CategoryTheory.regularPathModuleCoefficientFunctor
          (_root_.FundamentalGroupoid.mk (inclusion X x P x))).map
            (FundamentalGroup.toArrow a) t) =
      (regularQuotientGroupRingIso X x P).hom t *
        MonoidAlgebra.single (((fundamentalGroupQuotientMulEquiv X x P).symm a)⁻¹) (1 : ℤ) := by
  let Y : TopCat.{u} := space X x P
  let y : Y := inclusion X x P x
  let e := fundamentalGroupQuotientMulEquiv X x P
  let d := MonoidAlgebra.domCongr ℤ ℤ e.symm
  let E := TopCat.regularBasedGroupRingIso Y y
  let A : ModuleCat.{u} ℤ := (CategoryTheory.regularPathModuleCoefficientFunctor
    (_root_.FundamentalGroupoid.mk y)).obj (_root_.FundamentalGroupoid.mk y)
  let T : A ⟶ A := (CategoryTheory.regularPathModuleCoefficientFunctor
    (_root_.FundamentalGroupoid.mk y)).map (FundamentalGroup.toArrow a)
  have hValue : (regularQuotientGroupRingIso X x P).hom (T t) = d (E.hom (T t)) := rfl
  have hRegular : E.hom (T t) = E.hom t * MonoidAlgebra.single a⁻¹ (1 : ℤ) :=
    TopCat.regularBasedGroupRingIso_postcomp_positive Y y a t
  have hLabel : d (MonoidAlgebra.single a⁻¹ (1 : ℤ)) =
      MonoidAlgebra.single (e.symm a)⁻¹ (1 : ℤ) :=
    (MonoidAlgebra.domCongr_single (R := ℤ) (A := ℤ) e.symm a⁻¹ (1 : ℤ)).trans
      (congrArg (fun q => MonoidAlgebra.single q (1 : ℤ)) (e.symm.toMonoidHom.map_inv a))
  exact hValue.trans ((congrArg d hRegular).trans
    ((map_mul d (E.hom t) (MonoidAlgebra.single a⁻¹ (1 : ℤ))).trans
      (congrArg (fun q => d (E.hom t) * q) hLabel)))

end AlgebraicTopology.LoopCellAttachment

end
