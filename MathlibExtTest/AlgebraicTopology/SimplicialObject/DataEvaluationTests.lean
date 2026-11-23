/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialObject.DataEvaluation

/-!
# Data evaluation-to-simplicial consumer tests

Tiny public-contract coverage for `Data.evalToSimplicialIso`,
`Data.evalToSimplicial_map_eq`, and `Data.toSimplicialObject_mapObjIso`: one degree
component at `op (mk n)` with
separated indexing/target universes, plus one generic-morphism equation pinning
evaluation-after-promotion to promotion-after-evaluation, plus one target-map
hom component pinning postcomposition-promotion orientation to identity. Uses only public
declarations; no production coherence proof is duplicated. The generic-morphism
statement detects swapped evaluation/transport orientation.
-/

namespace CategoryTheory.SimplicialObject.DataEvaluationTests

open CategoryTheory

universe u₁ v₁ u₂ v₂

variable {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]
variable (X : Data (A ⥤ D)) (a : A)
variable (Y : Data A) (F : A ⥤ D)

-- Degree-object component at separated universes.
example (n : ℕ) :
    (SimplicialObject.Data.evalToSimplicialIso X a).hom.app
      (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ :=
  SimplicialObject.Data.evalToSimplicialIso_hom_app X a
    (Opposite.op (SimplexCategory.mk n))

-- Generic-morphism equation: evaluation commutes with promotion.
example {m n : SimplexCategory} (f : m ⟶ n) :
    (X.toSimplicialObject ⋙ (evaluation A D).obj a).map f.op =
      (((SimplicialObject.Data.evalFunctor a).obj X).toSimplicialObject).map f.op :=
  SimplicialObject.Data.evalToSimplicial_map_eq X a f

-- Target-map comparison: postcomposition commutes with promotion.
-- Orientation `(Y.toSimplicialObject ⋙ F) ≅ (mapObj F Y).toSimplicialObject`
-- with identity hom component at `op (mk n)`.
example (n : ℕ) :
    (SimplicialObject.Data.toSimplicialObject_mapObjIso F Y).hom.app
      (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ :=
  SimplicialObject.Data.toSimplicialObject_mapObjIso_hom_app_mk F Y n

end CategoryTheory.SimplicialObject.DataEvaluationTests
