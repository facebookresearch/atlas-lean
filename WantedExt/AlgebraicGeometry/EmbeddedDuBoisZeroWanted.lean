/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EmbeddedDuBoisZero
public import Batteries.Util.ProofWanted

/-!
# Independence of the fixed embedded Du Bois unit

Kovács--Schwede--Smith, arXiv0801.1541v3, §2.B. The target is the
computed unit to the actual reduced-exceptional derived direct image.
The ambient scheme is smooth of finite type in characteristic zero;
the closed scheme is reduced. No arbitrary canonical/DB object appears.
-/

@[expose] public noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace MathlibExt.AlgebraicGeometry.EmbeddedDuBoisZero

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PrincipalizationModels
open MathlibExt.AlgebraicGeometry.FourierMukai

/-- An actual comparison of the fixed objects that preserves their particular native units. -/
def_wanted embedded_model_comparison
    {k : Type} [Field k] [CharZero k]
    (S : CategoryTheory.Over (Spec (.of k))) [Smooth S.hom]
    [LocallyOfFiniteType S.hom] [IsNoetherian S.left]
    (I : S.left.IdealSheafData) [IsReduced I.subscheme]
    [HasDerivedPushforwards.{0}]
    (R₁ R₂ : Principalization S I) (F₁ : ExceptionalMap R₁) (F₂ : ExceptionalMap R₂) :
    {e : duBoisZero F₁ ≅ duBoisZero F₂ // duBoisUnit F₁ ≫ e.hom = duBoisUnit F₂}

theorem_wanted embedded_model_independence
    {k : Type} [Field k] [CharZero k]
    (S : CategoryTheory.Over (Spec (.of k))) [Smooth S.hom]
    [LocallyOfFiniteType S.hom] [IsNoetherian S.left]
    (I : S.left.IdealSheafData) [IsReduced I.subscheme]
    [HasDerivedPushforwards.{0}]
    (R₁ R₂ : Principalization S I) (F₁ : ExceptionalMap R₁) (F₂ : ExceptionalMap R₂) :
    IsEmbeddedDuBois F₁ ↔ IsEmbeddedDuBois F₂ := by
  obtain ⟨e, he⟩ := ❰embedded_model_comparison❱ S I R₁ R₂ F₁ F₂
  change CategoryTheory.IsIso (duBoisUnit F₁) ↔ CategoryTheory.IsIso (duBoisUnit F₂)
  constructor
  · intro h
    let := h
    rw [← he]
    infer_instance
  · intro h
    let := h
    have hi : duBoisUnit F₂ ≫ e.inv = duBoisUnit F₁ := by
      rw [← he, CategoryTheory.Category.assoc, e.hom_inv_id,
        CategoryTheory.Category.comp_id]
    rw [← hi]
    infer_instance

end MathlibExt.AlgebraicGeometry.EmbeddedDuBoisZero
