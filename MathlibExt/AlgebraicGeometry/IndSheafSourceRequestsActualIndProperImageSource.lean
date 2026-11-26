/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Indization.Category
import Mathlib.CategoryTheory.Limits.Indization.IndObject

/-!
# Actual ind proper-image source

This module proves `actual_ind_proper_image_source`: the compact-generator
functor has a left Kan extension along the compact Yoneda embedding. The proof
goes through a private helper giving pointwise left Kan extensions along any
`Ind.yoneda` into an ind-category, from small filtered presentations and
filtered cocompleteness of the target.

Source: D'Agnolo--Kashiwara1311.2374v2, Sections2.2/3.2/3.3;
Kashiwara--Schapira, Ind-sheaves.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.IndSheafSourceRequests

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
open MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels

universe uC uD vCD

private theorem hasPointwiseLeftKanExtension_ind_yoneda {C : Type uC} [Category.{vCD} C]
    {D : Type uD} [Category.{vCD} D] (G : C ⥤ Ind D) :
    Functor.HasPointwiseLeftKanExtension (Ind.yoneda (C := C)) G := by
  intro Z
  let P := Ind.presentation Z
  have hcol : Limits.HasColimit (P.F ⋙ G) := inferInstance
  have h1 : Limits.HasColimit (P.toCostructuredArrow ⋙
      CostructuredArrow.proj yoneda ((Ind.inclusion C).obj Z) ⋙ G) := hcol
  have h2 : Limits.HasColimit (CostructuredArrow.proj yoneda ((Ind.inclusion C).obj Z) ⋙ G) :=
    Functor.Final.hasColimit_of_comp P.toCostructuredArrow
  have h3 : Limits.HasColimit (CostructuredArrow.proj (Ind.yoneda ⋙ Ind.inclusion C)
      ((Ind.inclusion C).obj Z) ⋙ G) :=
    (Functor.Final.hasColimit_comp_iff
      (CostructuredArrow.mapNatIso (Ind.yonedaCompInclusion (C := C))).functor).mpr h2
  exact (Functor.Final.hasColimit_comp_iff
    (CostructuredArrow.post (Ind.yoneda (C := C)) (Ind.inclusion C) Z)).mpr h3

/-- Extend the same actual compact generator functor by the native left Kan construction. -/
public theorem actual_ind_proper_image_source (k : Type) [Field k]
    (X Y : TopCat.{0}) [CompactSheafSource k X] [CompactSheafSource k Y]
    (f : X ⟶ Y) (P : CompactPushforwardSource k f) : IndPushforwardSource k f P := by
  refine ⟨?_⟩
  have := hasPointwiseLeftKanExtension_ind_yoneda (compactPushforward k f P ⋙ Ind.yoneda)
  infer_instance

end WantedExt.AlgebraicGeometry.IndSheafSourceRequests
