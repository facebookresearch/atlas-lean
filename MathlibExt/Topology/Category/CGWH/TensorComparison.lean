/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.CartesianMonoidal
public import Mathlib.Topology.Category.TopCat.Monoidal

/-!
# Locally compact tensor comparisons for CGWH

When the right factor is locally compact Hausdorff, inclusion of the chosen
CGWH cartesian tensor into `TopCat` agrees with the chosen TopCat tensor up to
a canonical isomorphism.  This file exposes that comparison, its projections,
and its naturality laws.

No claim is made that an arbitrary chosen CGWH product has the raw product
topology.  Every declaration here retains the explicit locally compact and
Hausdorff hypotheses on the right factor.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Topology

namespace CGWH

/-- Inclusion of a chosen CGWH tensor into `TopCat` preserves that tensor
when the right factor is locally compact Hausdorff. -/
noncomputable def tensorToTopIsoOfLocallyCompactRight
    (A B : CGWH.{u, v}) [LocallyCompactSpace B] [T2Space B] :
    cgwhToTop.obj (A ⊗ B) ≅ cgwhToTop.obj A ⊗ cgwhToTop.obj B := by
  let _ : IsIso (prodComparisonToTop A B) :=
    (TopCat.isIso_iff_isHomeomorph _).mpr
      (prodComparisonToTop_isHomeomorph_of_locallyCompact_right A B)
  let _ : IsIso (Limits.prodComparison cgwhToTop A B ≫
      (TopCat.prodIsoProd (cgwhToTop.obj A) (cgwhToTop.obj B)).hom) := by
    change IsIso (prodComparisonToTop A B)
    infer_instance
  let _ : IsIso (Limits.prodComparison cgwhToTop A B) :=
    IsIso.of_isIso_comp_right (Limits.prodComparison cgwhToTop A B)
      (TopCat.prodIsoProd (cgwhToTop.obj A) (cgwhToTop.obj B)).hom
  let _ : PreservesLimit (Limits.pair A B) cgwhToTop :=
    PreservesLimitPair.of_iso_prod_comparison cgwhToTop A B
  exact CartesianMonoidalCategory.prodComparisonIso cgwhToTop A B

/-- The locally compact tensor comparison preserves first projection. -/
@[reassoc]
theorem tensorToTopIsoOfLocallyCompactRight_hom_fst
    (A B : CGWH.{u, v}) [LocallyCompactSpace B] [T2Space B] :
    (tensorToTopIsoOfLocallyCompactRight A B).hom ≫
        CartesianMonoidalCategory.fst (cgwhToTop.obj A) (cgwhToTop.obj B) =
      cgwhToTop.map (CartesianMonoidalCategory.fst A B) :=
  CartesianMonoidalCategory.prodComparison_fst cgwhToTop A B

/-- The locally compact tensor comparison preserves second projection. -/
@[reassoc]
theorem tensorToTopIsoOfLocallyCompactRight_hom_snd
    (A B : CGWH.{u, v}) [LocallyCompactSpace B] [T2Space B] :
    (tensorToTopIsoOfLocallyCompactRight A B).hom ≫
        CartesianMonoidalCategory.snd (cgwhToTop.obj A) (cgwhToTop.obj B) =
      cgwhToTop.map (CartesianMonoidalCategory.snd A B) :=
  CartesianMonoidalCategory.prodComparison_snd cgwhToTop A B

/-- Naturality of the locally compact tensor comparison. -/
theorem tensorToTopIsoOfLocallyCompactRight_naturality
    {A A' B B' : CGWH.{u, v}}
    [LocallyCompactSpace B] [T2Space B]
    [LocallyCompactSpace B'] [T2Space B']
    (f : A ⟶ A') (g : B ⟶ B') :
    cgwhToTop.map (f ⊗ₘ g) ≫
        (tensorToTopIsoOfLocallyCompactRight A' B').hom =
      (tensorToTopIsoOfLocallyCompactRight A B).hom ≫
        (cgwhToTop.map f ⊗ₘ cgwhToTop.map g) :=
  CartesianMonoidalCategory.prodComparison_natural cgwhToTop f g

/-- Inverse naturality of the locally compact tensor comparison. -/
theorem tensorToTopIsoOfLocallyCompactRight_inv_naturality
    {A A' B B' : CGWH.{u, v}}
    [LocallyCompactSpace B] [T2Space B]
    [LocallyCompactSpace B'] [T2Space B']
    (f : A ⟶ A') (g : B ⟶ B') :
    (cgwhToTop.map f ⊗ₘ cgwhToTop.map g) ≫
        (tensorToTopIsoOfLocallyCompactRight A' B').inv =
      (tensorToTopIsoOfLocallyCompactRight A B).inv ≫
        cgwhToTop.map (f ⊗ₘ g) := by
  apply (cancel_mono (tensorToTopIsoOfLocallyCompactRight A' B').hom).1
  have hNat := tensorToTopIsoOfLocallyCompactRight_naturality f g
  have hLeft :
      ((cgwhToTop.map f ⊗ₘ cgwhToTop.map g) ≫
          (tensorToTopIsoOfLocallyCompactRight A' B').inv) ≫
          (tensorToTopIsoOfLocallyCompactRight A' B').hom =
        cgwhToTop.map f ⊗ₘ cgwhToTop.map g := by
    simp
  have hRight :
      ((tensorToTopIsoOfLocallyCompactRight A B).inv ≫
          cgwhToTop.map (f ⊗ₘ g)) ≫
          (tensorToTopIsoOfLocallyCompactRight A' B').hom =
        cgwhToTop.map f ⊗ₘ cgwhToTop.map g := by
    rw [Category.assoc, hNat]
    simp
  exact hLeft.trans hRight.symm

end CGWH

end
