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

/-- **Comparison of the embedded Du Bois models of two principalizations.** Let $k$ be a field of
characteristic zero, $S$ a smooth Noetherian $k$-scheme locally of finite type, $I$ an ideal sheaf
on $S$ whose closed subscheme $X$ is reduced, and assume that derived direct images exist
(`HasDerivedPushforwards`). For two principalizations of $I$, with induced maps $f_1 : E_1 → X$ and
$f_2 : E_2 → X$ from their reduced exceptional schemes, there is an isomorphism
$Rf_{1*}\mathcal O_{E_1} ≅ Rf_{2*}\mathcal O_{E_2}$ in the derived category of $X$ that carries the
unit $\mathcal O_X → Rf_{1*}\mathcal O_{E_1}$ to the unit $\mathcal O_X → Rf_{2*}\mathcal O_{E_2}$
(Kovács–Schwede–Smith, §2.B). -/
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
