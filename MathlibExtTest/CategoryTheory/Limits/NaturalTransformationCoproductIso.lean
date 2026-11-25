/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

import MathlibExt.CategoryTheory.Limits.NaturalTransformationCoproductIso

set_option autoImplicit false
noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits

example {C : Type u} [Category.{v} C] (T : C ⥤ C) (η : 𝟭 C ⟶ T)
    {J : Type w} [HasColimitsOfShape (Discrete J) C]
    [PreservesColimitsOfShape (Discrete J) T]
    (F : J → C) (c : Cofan F) (hc : IsColimit c) :
    (NatTrans.coproductArrowIso η F c hc).hom ≫
        (NatTrans.coproductArrowIso η F c hc).inv = 𝟙 _ ∧
      (NatTrans.coproductArrowIso η F c hc).inv ≫
        (NatTrans.coproductArrowIso η F c hc).hom = 𝟙 _ :=
  ⟨(NatTrans.coproductArrowIso η F c hc).hom_inv_id,
    (NatTrans.coproductArrowIso η F c hc).inv_hom_id⟩

example {C : Type u} [Category.{v} C] (T : C ⥤ C) (η : 𝟭 C ⟶ T)
    {J : Type w} [HasColimitsOfShape (Discrete J) C]
    [PreservesColimitsOfShape (Discrete J) T]
    (F : J → C) (c : Cofan F) (hc : IsColimit c) (j : J) :
    Limits.Sigma.ι F j ≫ (NatTrans.coproductArrowIso η F c hc).hom.left = c.inj j ∧
      Limits.Sigma.ι (fun j => T.obj (F j)) j ≫ (NatTrans.coproductArrowIso η F c hc).hom.right =
        T.map (c.inj j) ∧
      c.inj j ≫ (NatTrans.coproductArrowIso η F c hc).inv.left = Limits.Sigma.ι F j ∧
      T.map (c.inj j) ≫ (NatTrans.coproductArrowIso η F c hc).inv.right =
        Limits.Sigma.ι (fun j => T.obj (F j)) j :=
  ⟨NatTrans.coproductArrowIso_hom_left_injection η F c hc j,
    NatTrans.coproductArrowIso_hom_right_injection η F c hc j,
    NatTrans.coproductArrowIso_inv_left_injection η F c hc j,
    NatTrans.coproductArrowIso_inv_right_injection η F c hc j⟩
