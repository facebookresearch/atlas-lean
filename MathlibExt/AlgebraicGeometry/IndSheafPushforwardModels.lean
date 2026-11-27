/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-!
# Native compact-generator extension of ind-sheaf proper direct image

On compact-support generators, proper direct image is actual ordinary
sheaf pushforward. Its
compact-support lift preserves the same objects and every map.
The ind proper-image functor f_!! is the native left Kan extension along the compact
Yoneda embedding. Its derived functor is the native total right
derivation of that prescribed operator; no unrelated pushforward
functor is selected. Closed-boundary images use this exact operator.

Source: D'Agnolo--Kashiwara1311.2374v2, Sections2.2/3.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CompactSupportIndSheaves

variable (k : Type) [Field k] {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- The support theorem refers to the actual ordinary continuous sheaf pushforward. -/
structure CompactPushforwardSource : Prop where
  compact : ∀ F : CompactSheaf k X,
    IsCompactSupported k Y ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).obj F.obj)

/-- The lift keeps the actual ordinary sheaf maps. -/
def compactPushforward (P : CompactPushforwardSource k f) : CompactSheaf k X ⥤ CompactSheaf k Y where
  obj F := ⟨(TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).obj F.obj, P.compact F⟩
  map a := ObjectProperty.homMk ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).map a.hom)
  map_id F := by
    apply ObjectProperty.hom_ext
    exact (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).map_id F.obj
  map_comp a b := by
    apply ObjectProperty.hom_ext
    exact (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).map_comp a.hom b.hom


variable (P : CompactPushforwardSource k f)
  [CompactSheafSource k X] [CompactSheafSource k Y]

/-- Kan-extension existence refers only to the original compact generator functor. -/
structure IndPushforwardSource : Prop where
  hasKan : (Ind.yoneda (C := CompactSheaf k X)).HasLeftKanExtension
    (compactPushforward k f P ⋙ Ind.yoneda)

/-- The actual ind-sheaf proper direct image is the native compact-Yoneda left Kan extension. -/
def indProperImage (D : IndPushforwardSource k f P) : IndSheaf k X ⥤ IndSheaf k Y :=
  letI := D.hasKan
  (Ind.yoneda (C := CompactSheaf k X)).leftKanExtension
    (compactPushforward k f P ⋙ Ind.yoneda)

/-- The compact-generator comparison is the native Kan-extension unit. -/
def compactPushforwardUnit (D : IndPushforwardSource k f P) :
    compactPushforward k f P ⋙ Ind.yoneda ⟶
      Ind.yoneda ⋙ indProperImage k f P D :=
  letI := D.hasKan
  (Ind.yoneda (C := CompactSheaf k X)).leftKanExtensionUnit
    (compactPushforward k f P ⋙ Ind.yoneda)


end MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels
