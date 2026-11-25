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

import MathlibExt.AlgebraicTopology.ModelCategory.RelativeCylinder

noncomputable section
universe uC vC
open CategoryTheory Limits

namespace RelativeCylinderClients
variable {C : Type uC} [Category.{vC} C] [HasPushouts C]
  (T S : C ⥤ C) [PreservesColimitsOfShape WalkingSpan T]
  (t₀ t₁ : 𝟭 C ⟶ T) (pT : T ⟶ 𝟭 C)
  (e₀ e₁ : 𝟭 C ⟶ S) (pS : S ⟶ 𝟭 C)
  (he₀p : ∀ X : C, e₀.app X ≫ pS.app X = 𝟙 X)
  (a : S ⋙ T ⟶ S)
  (ha₀ : ∀ X : C, t₀.app (S.obj X) ≫ a.app X = 𝟙 (S.obj X))
  (ha₁ : ∀ X : C, t₁.app (S.obj X) ≫ a.app X = pS.app X ≫ e₁.app X)
  (haFixed : ∀ X : C, T.map (e₁.app X) ≫ a.app X = pT.app X ≫ e₁.app X)
  (haProjection : ∀ X : C, T.map (e₀.app X) ≫ a.app X ≫ pS.app X = pT.app X)
  {A B : C} (i : A ⟶ B) (hi : IntervalHomotopyExtension.property T t₀ i)

example :
    i ≫ (OriginalRelativeCylinder.ofHEP T S t₀ t₁ pT e₀ e₁ pS he₀p a
        ha₀ ha₁ haFixed haProjection i hi).inverse =
      e₁.app A ≫ pushout.inl (e₀.app A) i :=
  (OriginalRelativeCylinder.ofHEP T S t₀ t₁ pT e₀ e₁ pS he₀p a
    ha₀ ha₁ haFixed haProjection i hi).inverse_source

example :
    T.map (e₁.app A ≫ pushout.inl (e₀.app A) i) ≫
        (OriginalRelativeCylinder.ofHEP T S t₀ t₁ pT e₀ e₁ pS he₀p a
          ha₀ ha₁ haFixed haProjection i hi).cylinderHomotopy =
      pT.app A ≫ (e₁.app A ≫ pushout.inl (e₀.app A) i) :=
  (OriginalRelativeCylinder.ofHEP T S t₀ t₁ pT e₀ e₁ pS he₀p a
    ha₀ ha₁ haFixed haProjection i hi).cylinder_fixed

example :
    T.map i ≫ (OriginalRelativeCylinder.ofHEP T S t₀ t₁ pT e₀ e₁ pS he₀p a
        ha₀ ha₁ haFixed haProjection i hi).targetHomotopy = pT.app A ≫ i :=
  (OriginalRelativeCylinder.ofHEP T S t₀ t₁ pT e₀ e₁ pS he₀p a
    ha₀ ha₁ haFixed haProjection i hi).target_fixed

end RelativeCylinderClients
