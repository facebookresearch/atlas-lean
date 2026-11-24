/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicTopology.SimplicialSet.CompatiblePushoutCartesianGeometry

public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open SSet.RezkCompatiblePushout
namespace CompatiblePushoutCartesianGeometryTest

variable {X0 X1 X2 PX Y0 Y1 Y2 PY : SSet.{u}}
variable {u0 : X0 ⟶ X1} {v0 : X0 ⟶ X2} {a : Y0 ⟶ Y1} {b : Y0 ⟶ Y2}
variable {ix1 : X1 ⟶ PX} {ix2 : X2 ⟶ PX} {iy1 : Y1 ⟶ PY} {iy2 : Y2 ⟶ PY}
variable {p0 : X0 ⟶ Y0} {p1 : X1 ⟶ Y1} {p2 : X2 ⟶ Y2} {p : PX ⟶ PY}
variable [Mono b]
variable (sx : IsPushout u0 v0 ix1 ix2) (sy : IsPushout a b iy1 iy2)
variable (hL : IsPullback u0 p0 p1 a) (hR : IsPullback v0 p0 p2 b)
variable (cL : CommSq ix1 p1 p iy1) (cR : CommSq ix2 p2 p iy2)

include sx sy hL hR cL cR

private theorem original_full_cube :
    IsPullback ix1 p1 p iy1 ∧ IsPullback ix2 p2 p iy2 ∧
      IsPullback (u0 ≫ ix1) p0 p (a ≫ iy1) ∧
      IsPullback (v0 ≫ ix2) p0 p (b ≫ iy2) :=
  strict_faces sx sy hL hR cL cR

private theorem original_cover_square :
    IsPullback (coprod.desc ix1 ix2) (coprod.map p1 p2)
      p (coprod.desc iy1 iy2) := by
  have faces := strict_faces sx sy hL hR cL cR
  exact coverSquare faces.1 faces.2.1

private theorem original_whole_arrow :
    Nonempty (Arrow.mk (coprod.map p1 p2) ≅
      Arrow.mk (pullback.snd p (coprod.desc iy1 iy2))) := by
  have faces := strict_faces sx sy hL hR cL cR
  exact ⟨coverArrowIso faces.1 faces.2.1⟩

private theorem original_four_projections :
    let faces := strict_faces sx sy hL hR cL cR
    let e := coverIso faces.1 faces.2.1
    e.hom ≫ pullback.fst p (coprod.desc iy1 iy2) = coprod.desc ix1 ix2 ∧
      e.hom ≫ pullback.snd p (coprod.desc iy1 iy2) = coprod.map p1 p2 ∧
      e.inv ≫ coprod.desc ix1 ix2 = pullback.fst p (coprod.desc iy1 iy2) ∧
      e.inv ≫ coprod.map p1 p2 = pullback.snd p (coprod.desc iy1 iy2) := by
  exact coverIso_legs (strict_faces sx sy hL hR cL cR).1
    (strict_faces sx sy hL hR cL cR).2.1

private theorem original_inverse_identities :
    let faces := strict_faces sx sy hL hR cL cR
    let e := coverIso faces.1 faces.2.1
    e.hom ≫ e.inv = 𝟙 (X1 ⨿ X2) ∧
      e.inv ≫ e.hom = 𝟙 (pullback p (coprod.desc iy1 iy2)) := by
  exact ⟨Iso.hom_inv_id _, Iso.inv_hom_id _⟩

private theorem original_same_arrow_codomain :
    let faces := strict_faces sx sy hL hR cL cR
    let e := coverArrowIso faces.1 faces.2.1
    e.hom.right = 𝟙 (Y1 ⨿ Y2) ∧ e.inv.right = 𝟙 (Y1 ⨿ Y2) := by
  simp [coverArrowIso]

private theorem original_all_forward_operators {m n : SimplexCategory}
    (δ : m ⟶ n) (z : (X1 ⨿ X2).obj (op n)) :
    let faces := strict_faces sx sy hL hR cL cR
    let e := coverIso faces.1 faces.2.1
    e.hom.app (op m) ((X1 ⨿ X2).map δ.op z) =
      (pullback p (coprod.desc iy1 iy2)).map δ.op (e.hom.app (op n) z) := by
  exact ConcreteCategory.congr_hom
    ((coverIso (strict_faces sx sy hL hR cL cR).1
      (strict_faces sx sy hL hR cL cR).2.1).hom.naturality δ.op) z

private theorem original_all_inverse_operators {m n : SimplexCategory}
    (δ : m ⟶ n) (z : (pullback p (coprod.desc iy1 iy2)).obj (op n)) :
    let faces := strict_faces sx sy hL hR cL cR
    let e := coverIso faces.1 faces.2.1
    e.inv.app (op m) ((pullback p (coprod.desc iy1 iy2)).map δ.op z) =
      (X1 ⨿ X2).map δ.op (e.inv.app (op n) z) := by
  exact ConcreteCategory.congr_hom
    ((coverIso (strict_faces sx sy hL hR cL cR).1
      (strict_faces sx sy hL hR cL cR).2.1).inv.naturality δ.op) z

end CompatiblePushoutCartesianGeometryTest
