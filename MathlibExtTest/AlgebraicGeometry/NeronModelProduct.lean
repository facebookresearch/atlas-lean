/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NeronModelProduct

/-!
# Tests for the Néron model of a product

The generic identification of the product Néron model is compatible with the projections,
and the product of finite-type Néron models has the product model.
-/

@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.NeronModelProduct

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.NeronModels
open MathlibExt.AlgebraicGeometry.SemistableModels

universe u

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {A B : Over (Spec (.of K))}

/-- On generic fibres, the first projection of the product model is the first projection of
`A ⨯ B`, through the given identifications. -/
example (M : NeronModel R K A) (N : NeronModel R K B) :
    (M.prod N).genericIso.hom ≫ prod.fst =
      (genericFunctor R K).map prod.fst ≫ M.genericIso.hom := by
  simp [NeronModel.prod_genericIso, PreservesLimitPair.iso_hom]

/-- The same for the second projection. -/
example (M : NeronModel R K A) (N : NeronModel R K B) :
    (M.prod N).genericIso.hom ≫ prod.snd =
      (genericFunctor R K).map prod.snd ≫ N.genericIso.hom := by
  simp [NeronModel.prod_genericIso, PreservesLimitPair.iso_hom]

/-- The product of finite-type Néron models has the product model. -/
example (M : FiniteTypeNeronModel R K A) (N : FiniteTypeNeronModel R K B) :
    (M.prod N).model = (M.model ⨯ N.model) := rfl

/-- Two Néron models of a product are uniquely isomorphic to the product model. -/
example (M : NeronModel R K A) (N : NeronModel R K B) (P : NeronModel R K (A ⨯ B)) :
    ∃! e : (M.prod N).model ≅ P.model,
      (genericFunctor R K).map e.hom ≫ P.genericIso.hom = (M.prod N).genericIso.hom :=
  (M.prod N).existsUnique_iso P

end MathlibExtTest.AlgebraicGeometry.NeronModelProduct
