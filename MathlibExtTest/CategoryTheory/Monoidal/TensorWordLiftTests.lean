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
# Generic TensorWord universal-property contract tests

Selective compile-time checks for the generic `TensorWord`
universal property: the generator beta law into a generic monoid object,
uniqueness/extensionality from agreement on generators, both directions of
the public `tensorWordHomEquiv` with an inverse computation, and target and
source and generator naturality with their correct variance and composition order.

Each check is a direct generic invocation under exactly the public
hypotheses; no concrete category is constructed and no production argument
is re-proved. Variance and composition order are already pinned by the
generic statement types.

Nonclaims: no `free` name, adjunction, filtration, or shifted-Cobar wiring.
-/

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorWord

namespace MathlibExtTest.TensorWordLiftTests

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [∀ (f : ℕ → C), HasCoproduct f]
variable [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
variable [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
variable [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
variable [∀ (T : C),
  PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)]

section Beta

-- Generator beta law into a generic monoid object, via the bundled lift.
example {X : C} (M : Mon C) (f : X ⟶ M.X) :
    tensorWordGenerator X ≫ (tensorWordLiftHom M f).hom = f :=
  tensorWordLift_beta M f

end Beta

section Unique

-- Uniqueness/extensionality from agreement on generators.
example {X : C} {M : Mon C} (f : X ⟶ M.X) (g : tensorWordMon X ⟶ M)
    (h : tensorWordGenerator X ≫ g.hom = f) :
    g = tensorWordLiftHom M f :=
  tensorWordLiftUnique f g h

end Unique

section Equiv

-- Forward direction: the equivalence acts by the lift, pinned by beta.
example {X : C} (M : Mon C) (f : X ⟶ M.X) :
    tensorWordGenerator X ≫ ((tensorWordHomEquiv X M) f).hom = f :=
  tensorWordLift_beta M f

-- Backward direction with an inverse computation.
example {X : C} (M : Mon C) (g : tensorWordMon X ⟶ M) :
    (tensorWordHomEquiv X M) (tensorWordGenerator X ≫ g.hom) = g :=
  (tensorWordHomEquiv X M).right_inv g

end Equiv

section Naturality

-- Target naturality: covariant postcomposition order.
example {X : C} {M N : Mon C} (f : X ⟶ M.X) (k : M ⟶ N) :
    tensorWordHomEquiv X N (f ≫ k.hom) =
      (tensorWordHomEquiv X M) f ≫ k :=
  tensorWordHomEquiv_target f k

-- Source naturality: precomposition order through the functorial carrier map.
example {Y X : C} {M : Mon C} (h : Y ⟶ X) (f : X ⟶ M.X) :
    tensorWordHomEquiv Y M (h ≫ f) =
      Mon.ofHom (tensorWordMap h) ≫ (tensorWordHomEquiv X M) f :=
  tensorWordHomEquiv_source h f

-- Generator naturality: degree-one inclusion commutes with functorial maps.
example {Y X : C} (h : Y ⟶ X) :
    tensorWordGenerator Y ≫ tensorWordMap h =
      h ≫ tensorWordGenerator X :=
  tensorWordGenerator_naturality h

end Naturality

end MathlibExtTest.TensorWordLiftTests
