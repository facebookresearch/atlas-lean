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

import MathlibExt.CategoryTheory.Monoidal.TensorWord

/-!
# Generic tensor-word monoid public-contract tests

Selective compile-time checks for the `tensorWordObj` / `tensorWordι` /
`tensorWordMap` / `tensorWordOne` / `tensorWordMul` / `tensorWordMon` /
`tensorWordFunctor` API: carrier and inclusion under only `ℕ`-coproducts,
`tensorWordι_desc`, map computation on an inclusion with identity and
composition, degree-zero unit as the zero inclusion, symbolic `(m,n)`
multiplication that visibly preserves the left-associated
`tensorPowObj_add` orientation, synthesized `IsMonHom` instance, and functor
object/underlying-map projections with map identity and composition. Each
check is a small `example` over a generic monoidal category; no concrete
instance is constructed and no production argument is re-proved.

Nonclaims: no `free` name, universal property, adjunction, filtration,
completion, conilpotence, bar/cobar, operadic, derived, or model-categorical
result here.
-/

namespace MathlibExtTest.TensorWord

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open CategoryTheory.MonoidalCategory.TensorWord

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section CarrierMap

variable [∀ (f : ℕ → C), HasCoproduct f]

-- Inclusion signature under only `ℕ`-coproducts.
example (X : C) (n : ℕ) : tensorPowObj X n ⟶ tensorWordObj X :=
  tensorWordι X n

-- Computation of the universal map on an inclusion.
example (X : C) {P : C} (p : ∀ n : ℕ, tensorPowObj X n ⟶ P) (n : ℕ) :
    tensorWordι X n ≫ Limits.Sigma.desc p = p n :=
  tensorWordι_desc X p n

-- Functorial map computation on an inclusion.
example {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    tensorWordι X n ≫ tensorWordMap f =
      tensorPowMap f n ≫ tensorWordι Y n :=
  tensorWordMap_ι f n

example (X : C) : tensorWordMap (𝟙 X) = 𝟙 (tensorWordObj X) :=
  tensorWordMap_id X

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    tensorWordMap f ≫ tensorWordMap g = tensorWordMap (f ≫ g) :=
  tensorWordMap_comp f g

-- Degree-zero unit is the zero inclusion.
example (X : C) : tensorWordOne X = tensorWordι X 0 :=
  rfl

end CarrierMap

section Mul

variable [∀ (f : ℕ → C), HasCoproduct f]
variable [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
variable [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
variable [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]

-- Symbolic multiplication visibly preserves the left-associated
-- `tensorPowObj_add` orientation (`inv` then inclusion at `m + n`).
example (X : C) (m n : ℕ) :
    (tensorWordι X m ⊗ₘ tensorWordι X n) ≫ tensorWordMul X =
      (tensorPowObj_add X m n).inv ≫ tensorWordι X (m + n) :=
  tensorWordMul_ι X m n

end Mul

section MonFunctor

variable [∀ (f : ℕ → C), HasCoproduct f]
variable [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
variable [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
variable [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
variable [∀ (T : C),
  PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)]

-- Synthesized monoid-morphism instance for a generic map.
example {X Y : C} (f : X ⟶ Y) : IsMonHom (tensorWordMap f) :=
  inferInstance

-- Functor object carrier projection.
example (X : C) :
    (((tensorWordFunctor (C := C)).obj X).X = tensorWordObj X) :=
  tensorWordFunctor_obj_carrier X

-- Functor underlying-map projection.
example {X Y : C} (f : X ⟶ Y) :
    ((tensorWordFunctor (C := C)).map f).hom = tensorWordMap f :=
  tensorWordFunctor_map_hom f

-- Functor map identity.
example (X : C) :
    (tensorWordFunctor (C := C)).map (𝟙 X) = 𝟙 _ :=
  (tensorWordFunctor (C := C)).map_id X

-- Functor map composition.
example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (tensorWordFunctor (C := C)).map (f ≫ g) =
      (tensorWordFunctor (C := C)).map f ≫
        (tensorWordFunctor (C := C)).map g :=
  (tensorWordFunctor (C := C)).map_comp f g

end MonFunctor

end

end MathlibExtTest.TensorWord
