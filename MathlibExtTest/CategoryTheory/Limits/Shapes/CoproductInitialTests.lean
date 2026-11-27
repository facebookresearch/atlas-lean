/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Limits.Shapes.CoproductInitial

@[expose] public section

set_option autoImplicit false
noncomputable section

universe vC uC uI

open CategoryTheory CategoryTheory.Limits

namespace MathlibExtTest.CategoryTheory.Limits.CoproductInitial

variable {C : Type uC} [Category.{vC} C]

#check @coproductIsInitialOfEach
#check @coproductIsoOfInitialExcept

example {ι : Type uI} (F : ι → C) [HasCoproduct F]
    (hF : ∀ i, IsInitial (F i)) : IsInitial (∐ F) :=
  coproductIsInitialOfEach F hF

example {ι : Type uI} (F : ι → C) [HasCoproduct F] (i₀ : ι)
    (hF : ∀ i, i ≠ i₀ → IsInitial (F i)) : (∐ F) ≅ F i₀ :=
  coproductIsoOfInitialExcept F i₀ hF

example {ι : Type uI} (F : ι → C) [HasCoproduct F] (i₀ : ι)
    (hF : ∀ i, i ≠ i₀ → IsInitial (F i)) :
    (coproductIsoOfInitialExcept F i₀ hF).inv = Sigma.ι F i₀ := rfl

example {ι : Type uI} (F : ι → C) [HasCoproduct F] (i₀ : ι)
    (hF : ∀ i, i ≠ i₀ → IsInitial (F i)) :
    (coproductIsoOfInitialExcept F i₀ hF).hom ≫
      (coproductIsoOfInitialExcept F i₀ hF).inv = 𝟙 (∐ F) :=
  (coproductIsoOfInitialExcept F i₀ hF).hom_inv_id

example {ι : Type uI} (F : ι → C) [HasCoproduct F] (i₀ : ι)
    (hF : ∀ i, i ≠ i₀ → IsInitial (F i)) :
    (coproductIsoOfInitialExcept F i₀ hF).inv ≫
      (coproductIsoOfInitialExcept F i₀ hF).hom = 𝟙 (F i₀) :=
  (coproductIsoOfInitialExcept F i₀ hF).inv_hom_id

#print axioms coproductIsInitialOfEach
#print axioms coproductIsoOfInitialExcept

end MathlibExtTest.CategoryTheory.Limits.CoproductInitial
