/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Levelwise pushout assembly for length-two composable arrows

Given `R S T : ComposableArrows C 2` with maps `RS : R ⟶ S` and `RT : R ⟶ T`,
explicit levelwise pushout input data (`LevelwisePushoutData`) carries three
`IsPushout` witnesses, one per level. From this data we construct the induced
maps `P₀ ⟶ P₁ ⟶ P₂`, their four leg/naturality laws, the assembled
`ComposableArrows C 2`, the cocone legs, and the standard `IsPushout`
witness.

Orientation: the `S`/`T` legs point into the pushout apices (`inlS`/`inrT`);
the induced maps point forward (`P₀ ⟶ P₁ ⟶ P₂`); the descending map points
out of the assembled arrow into a test cocone.

Reuse: `ComposableArrows C 2` is `Fin 3 ⥤ C`, so the pinned
`IsPushout.of_forall_isPushout_app` (`IsPullback.Basic`) assembles the three
levelwise `IsPushout` witnesses into `LevelwisePushoutData.isPushout`;
consumers use that standard witness via `IsPushout.desc`, `inl_desc`,
`inr_desc`, and `hom_ext`.
The induced maps and legs still use the pinned `ComposableArrows.Basic` API
(`mk₂`, `homMk₂`, `hom_ext₂`, `naturality'`) and the levelwise witnesses.

Requires only `[Category C]`. No Preadditive, Exact, or Waldhausen
hypotheses, no composite-zero or cofiber-sequence conditions, no
cofiber-subcategory objects, and no category instances. Fully proved with no
outstanding goals. No simplicial object, nerve, realization, additivity,
spectra, or Q/S comparison is claimed.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C]

/-- Explicit levelwise-pushout input data for `RS : R ⟶ S`, `RT : R ⟶ T` in
`ComposableArrows C 2`: a pushout witness at each of the three levels. -/
structure LevelwisePushoutData where
  R : ComposableArrows C 2
  S : ComposableArrows C 2
  T : ComposableArrows C 2
  RS : R ⟶ S
  RT : R ⟶ T
  P0 : C
  P1 : C
  P2 : C
  inlS0 : S.obj' 0 ⟶ P0
  inrT0 : T.obj' 0 ⟶ P0
  inlS1 : S.obj' 1 ⟶ P1
  inrT1 : T.obj' 1 ⟶ P1
  inlS2 : S.obj' 2 ⟶ P2
  inrT2 : T.obj' 2 ⟶ P2
  isPushout0 :
    IsPushout (ComposableArrows.app' RS 0) (ComposableArrows.app' RT 0) inlS0 inrT0
  isPushout1 :
    IsPushout (ComposableArrows.app' RS 1) (ComposableArrows.app' RT 1) inlS1 inrT1
  isPushout2 :
    IsPushout (ComposableArrows.app' RS 2) (ComposableArrows.app' RT 2) inlS2 inrT2

/-- Induced map `P₀ ⟶ P₁` from the level-0 pushout universal property. -/
noncomputable def LevelwisePushoutData.inducedMap01 (D : LevelwisePushoutData C) :
    D.P0 ⟶ D.P1 :=
  D.isPushout0.desc (D.S.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫ D.inlS1)
    (D.T.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫ D.inrT1) (by
    calc ComposableArrows.app' D.RS 0 (Nat.zero_le 2) ≫
        (D.S.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫ D.inlS1)
        = (ComposableArrows.app' D.RS 0 (Nat.zero_le 2) ≫
            D.S.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1)) ≫ D.inlS1 :=
          (Category.assoc _ _ _).symm
      _ = (D.R.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫
          ComposableArrows.app' D.RS 1 (Nat.le_succ 1)) ≫ D.inlS1 := by
          rw [← ComposableArrows.naturality' D.RS 0 1]
      _ = D.R.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫
          (ComposableArrows.app' D.RS 1 (Nat.le_succ 1) ≫ D.inlS1) :=
          Category.assoc _ _ _
      _ = D.R.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫
          (ComposableArrows.app' D.RT 1 (Nat.le_succ 1) ≫ D.inrT1) := by
          rw [D.isPushout1.w]
      _ = (D.R.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫
          ComposableArrows.app' D.RT 1 (Nat.le_succ 1)) ≫ D.inrT1 :=
          (Category.assoc _ _ _).symm
      _ = (ComposableArrows.app' D.RT 0 (Nat.zero_le 2) ≫
          D.T.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1)) ≫ D.inrT1 := by
          rw [ComposableArrows.naturality' D.RT 0 1]
      _ = ComposableArrows.app' D.RT 0 (Nat.zero_le 2) ≫
          (D.T.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫ D.inrT1) :=
          Category.assoc _ _ _)

/-- Induced map `P₁ ⟶ P₂` from the level-1 pushout universal property. -/
noncomputable def LevelwisePushoutData.inducedMap12 (D : LevelwisePushoutData C) :
    D.P1 ⟶ D.P2 :=
  D.isPushout1.desc (D.S.map' 1 2 (Nat.le_succ 1) le_rfl ≫ D.inlS2)
    (D.T.map' 1 2 (Nat.le_succ 1) le_rfl ≫ D.inrT2) (by
    calc ComposableArrows.app' D.RS 1 (Nat.le_succ 1) ≫
        (D.S.map' 1 2 (Nat.le_succ 1) le_rfl ≫ D.inlS2)
        = (ComposableArrows.app' D.RS 1 (Nat.le_succ 1) ≫
            D.S.map' 1 2 (Nat.le_succ 1) le_rfl) ≫ D.inlS2 :=
          (Category.assoc _ _ _).symm
      _ = (D.R.map' 1 2 (Nat.le_succ 1) le_rfl ≫ ComposableArrows.app' D.RS 2) ≫ D.inlS2 := by
          rw [← ComposableArrows.naturality' D.RS 1 2]
      _ = D.R.map' 1 2 (Nat.le_succ 1) le_rfl ≫ (ComposableArrows.app' D.RS 2 ≫ D.inlS2) :=
          Category.assoc _ _ _
      _ = D.R.map' 1 2 (Nat.le_succ 1) le_rfl ≫ (ComposableArrows.app' D.RT 2 ≫ D.inrT2) := by
          rw [D.isPushout2.w]
      _ = (D.R.map' 1 2 (Nat.le_succ 1) le_rfl ≫ ComposableArrows.app' D.RT 2) ≫ D.inrT2 :=
          (Category.assoc _ _ _).symm
      _ = (ComposableArrows.app' D.RT 1 (Nat.le_succ 1) ≫
          D.T.map' 1 2 (Nat.le_succ 1) le_rfl) ≫ D.inrT2 := by
          rw [ComposableArrows.naturality' D.RT 1 2]
      _ = ComposableArrows.app' D.RT 1 (Nat.le_succ 1) ≫
          (D.T.map' 1 2 (Nat.le_succ 1) le_rfl ≫ D.inrT2) :=
          Category.assoc _ _ _)

/-- Assembled length-two composable arrow `P₀ ⟶ P₁ ⟶ P₂`. -/
noncomputable def LevelwisePushoutData.assembled (D : LevelwisePushoutData C) :
    ComposableArrows C 2 :=
  ComposableArrows.mk₂ D.inducedMap01 D.inducedMap12

/-- Level `0 → 1` law for the `S` leg into the assembled arrow. -/
@[simp]
theorem LevelwisePushoutData.inl_map01 (D : LevelwisePushoutData C) :
    D.inlS0 ≫ D.assembled.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) =
      D.S.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫ D.inlS1 :=
  D.isPushout0.inl_desc _ _ _

/-- Level `0 → 1` law for the `T` leg into the assembled arrow. -/
@[simp]
theorem LevelwisePushoutData.inr_map01 (D : LevelwisePushoutData C) :
    D.inrT0 ≫ D.assembled.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) =
      D.T.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫ D.inrT1 :=
  D.isPushout0.inr_desc _ _ _

/-- Level `1 → 2` law for the `S` leg into the assembled arrow. -/
@[simp]
theorem LevelwisePushoutData.inl_map12 (D : LevelwisePushoutData C) :
    D.inlS1 ≫ D.assembled.map' 1 2 (Nat.le_succ 1) le_rfl =
      D.S.map' 1 2 (Nat.le_succ 1) le_rfl ≫ D.inlS2 :=
  D.isPushout1.inl_desc _ _ _

/-- Level `1 → 2` law for the `T` leg into the assembled arrow. -/
@[simp]
theorem LevelwisePushoutData.inr_map12 (D : LevelwisePushoutData C) :
    D.inrT1 ≫ D.assembled.map' 1 2 (Nat.le_succ 1) le_rfl =
      D.T.map' 1 2 (Nat.le_succ 1) le_rfl ≫ D.inrT2 :=
  D.isPushout1.inr_desc _ _ _

/-- Cocone leg `S ⟶ assembled` with components `inlS`. -/
noncomputable def LevelwisePushoutData.legS (D : LevelwisePushoutData C) : D.S ⟶ D.assembled :=
  ComposableArrows.homMk₂ D.inlS0 D.inlS1 D.inlS2 D.inl_map01.symm D.inl_map12.symm

/-- Cocone leg `T ⟶ assembled` with components `inrT`. -/
noncomputable def LevelwisePushoutData.legT (D : LevelwisePushoutData C) : D.T ⟶ D.assembled :=
  ComposableArrows.homMk₂ D.inrT0 D.inrT1 D.inrT2 D.inr_map01.symm D.inr_map12.symm

/-- Standard pushout witness assembled pointwise from the three levelwise
`IsPushout` hypotheses via `IsPushout.of_forall_isPushout_app`
(`ComposableArrows C 2` is `Fin 3 ⥤ C`). -/
theorem LevelwisePushoutData.isPushout (D : LevelwisePushoutData C) :
    IsPushout D.RS D.RT D.legS D.legT :=
  IsPushout.of_forall_isPushout_app (F₁ := D.R) (F₂ := D.S) (F₃ := D.T)
    (F₄ := D.assembled) (f₁ := D.RS) (f₂ := D.RT) (f₃ := D.legS)
    (f₄ := D.legT) (fun X => by
      fin_cases X
      · change IsPushout _ _ D.inlS0 D.inrT0
        exact D.isPushout0
      · change IsPushout _ _ D.inlS1 D.inrT1
        exact D.isPushout1
      · change IsPushout _ _ D.inlS2 D.inrT2
        exact D.isPushout2)

end CategoryTheory.Waldhausen.SConstruction
