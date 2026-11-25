/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.Embedding.StupidTruncNested

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {ι₁ ι₂ ι₃ ι : Type*}
variable {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}
  {c₃ : ComplexShape ι₃} {c : ComplexShape ι}

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
variable (K L : HomologicalComplex C c)
variable (e₁ : c₁.Embedding c) (e₂ : c₂.Embedding c)
  (e₃ : c₃.Embedding c)

section Weak

variable [e₁.IsTruncGE] [e₂.IsRelIff]

example : e₁.RangeLE e₁ :=
  ComplexShape.Embedding.RangeLE.refl e₁

example (h₁₂ : e₁.RangeLE e₂) (h₂₃ : e₂.RangeLE e₃) : e₁.RangeLE e₃ :=
  h₁₂.trans h₂₃

example (h₁₂ : e₁.RangeLE e₂) :
    K.stupidTrunc e₁ ⟶ K.stupidTrunc e₂ :=
  K.stupidTruncMapOfRangeLE e₁ e₂ h₁₂

example (h₁₂ : e₁.RangeLE e₂) {i₁ : ι₁} {i₂ : ι₂} {k : ι}
    (hi₁ : e₁.f i₁ = k) (hi₂ : e₂.f i₂ = k) :
    (K.stupidTruncMapOfRangeLE e₁ e₂ h₁₂).f k =
      (K.stupidTruncXIso e₁ hi₁).hom ≫
        (K.stupidTruncXIso e₂ hi₂).inv :=
  K.stupidTruncMapOfRangeLE_f e₁ e₂ h₁₂ hi₁ hi₂

example (h₁₂ : e₁.RangeLE e₂) (k : ι)
    (hk : ∀ i, e₁.f i ≠ k) :
    (K.stupidTruncMapOfRangeLE e₁ e₂ h₁₂).f k = 0 :=
  K.stupidTruncMapOfRangeLE_f_eq_zero e₁ e₂ h₁₂ k hk

example (h₁₂ : e₁.RangeLE e₂) (k : ι) :
    Mono ((K.stupidTruncMapOfRangeLE e₁ e₂ h₁₂).f k) :=
  inferInstance

example (h₁₂ : e₁.RangeLE e₂) :
    Mono (K.stupidTruncMapOfRangeLE e₁ e₂ h₁₂) :=
  inferInstance

end Weak

section Strong

variable [e₁.IsTruncGE] [e₂.IsTruncGE] [e₃.IsTruncGE]

example (h₁₂ : e₁.RangeLE e₂) :
    K.stupidTruncMapOfRangeLE e₁ e₂ h₁₂ ≫ K.ιStupidTrunc e₂ =
      K.ιStupidTrunc e₁ :=
  K.stupidTruncMapOfRangeLE_ιStupidTrunc e₁ e₂ h₁₂

example :
    K.stupidTruncMapOfRangeLE e₁ e₁
        (ComplexShape.Embedding.RangeLE.refl e₁) = 𝟙 _ :=
  K.stupidTruncMapOfRangeLE_refl e₁

example (h₁₂ : e₁.RangeLE e₂) (h₂₃ : e₂.RangeLE e₃) :
    K.stupidTruncMapOfRangeLE e₁ e₂ h₁₂ ≫
        K.stupidTruncMapOfRangeLE e₂ e₃ h₂₃ =
      K.stupidTruncMapOfRangeLE e₁ e₃ (h₁₂.trans h₂₃) :=
  K.stupidTruncMapOfRangeLE_comp e₁ e₂ e₃ h₁₂ h₂₃

example (h₁₂ : e₁.RangeLE e₂) (φ : K ⟶ L) :
    stupidTruncMap φ e₁ ≫ L.stupidTruncMapOfRangeLE e₁ e₂ h₁₂ =
      K.stupidTruncMapOfRangeLE e₁ e₂ h₁₂ ≫ stupidTruncMap φ e₂ :=
  stupidTruncMap_stupidTruncMapOfRangeLE_naturality e₁ e₂ h₁₂ φ

end Strong

end HomologicalComplex

end
