/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NeronModelUniqueness
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Tests for uniqueness and étale base change of Néron models

The comparison isomorphism of a Néron model with itself is the identity, and étale base
change over discrete valuation rings, for the Néron model of an abelian variety, is the
special case of `NeronModel.isIso_baseChangeMap` for an étale `φ`.
-/

@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.NeronModelUniqueness

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AbelianSchemes
open MathlibExt.AlgebraicGeometry.NeronModels
open MathlibExt.AlgebraicGeometry.SemistableModels

universe u

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Over (Spec (.of K))}

/-- The comparison isomorphism of a Néron model with itself is the identity. -/
example (M : NeronModel R K A) : M.isoOfGeneric M = Iso.refl M.model :=
  (M.existsUnique_iso M).unique
    ((NeronModel.map_generic M M (𝟙 A)).trans (Category.comp_id _)) (by simp)

/-- Any isomorphism compatible with the generic identifications is the comparison one. -/
example (M N : NeronModel R K A) (e : M.model ≅ N.model)
    (he : (genericFunctor R K).map e.hom ≫ N.genericIso.hom = M.genericIso.hom) :
    e = M.isoOfGeneric N :=
  (M.existsUnique_iso N).unique he
    ((NeronModel.map_generic M N (𝟙 A)).trans (Category.comp_id _))

/-- Étale base change over discrete valuation rings for an abelian variety: the base-change
morphism to a Néron model over `R'` is an isomorphism. -/
example (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type u)
    [Field K] [Algebra R K] [IsFractionRing R K] (R' : Type u) [CommRing R'] [IsDomain R']
    [IsDiscreteValuationRing R'] (K' : Type u) [Field K'] [Algebra R' K']
    [IsFractionRing R' K'] (φ : trait R' ⟶ trait R) [Etale φ]
    (ψ : Spec (.of K') ⟶ Spec (.of K))
    (h : IsPullback ψ (genericInclusion R' K') (genericInclusion R K) φ)
    (A : AbelianScheme (Spec (.of K))) (M : NeronModel R K A.model)
    (N : NeronModel R' K' ((Over.pullback ψ).obj A.model)) :
    IsIso (baseChangeMap R K R' K' φ ψ h.w M N) :=
  NeronModel.isIso_baseChangeMap R K R' K' φ ψ h M N

/-- The model of the base-changed Néron model is the base change of the model. -/
example (R' : Type u) [CommRing R'] (K' : Type u) [Field K'] [Algebra R' K']
    [IsFractionRing R' K'] (φ : trait R' ⟶ trait R) [Smooth φ]
    (ψ : Spec (.of K') ⟶ Spec (.of K))
    (h : IsPullback ψ (genericInclusion R' K') (genericInclusion R K) φ)
    (M : NeronModel R K A) :
    (NeronModel.baseChange R K R' K' φ ψ h M).model = (Over.pullback φ).obj M.model := by
  simp

end MathlibExtTest.AlgebraicGeometry.NeronModelUniqueness
