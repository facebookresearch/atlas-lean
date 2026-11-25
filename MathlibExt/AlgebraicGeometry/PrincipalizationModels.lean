/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BirationalResolution
public import MathlibExt.AlgebraicGeometry.CartierIdealModels
public import MathlibExt.AlgebraicGeometry.NormalCrossingsModels

/-!
# Principalization with an actual strict normal crossings divisor

The ideal is the native quasi-coherent scheme ideal. On the resolving
scheme its actual inverse ideal is effective Cartier. The reduced
boundary is the radical support of that inverse ideal, with genuine
regular local parameter equations and smooth global components.

The birational map is required to be an isomorphism outside the original
ideal support. It can change smooth points lying in that support.

References: Bierstone–Milman, *Canonical desingularization in
characteristic zero*, Theorem 1.10; Stacks Tags 01WQ, 0BI9 and 0BIA. Generic SNC and
surface principalization facts in AxiomMath/Stacks are covered support.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PrincipalizationModels

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open BirationalResolution CartierIdealModels NormalCrossingsModels

universe u

structure Principalization {k : Type u} [Field k]
    (X : Over (Spec (.of k))) (I : X.left.IdealSheafData) where
  source : Over (Spec (.of k))
  [integral : IsIntegral source.left]
  [smooth : Smooth source.hom]
  map : source ⟶ X
  [proper : IsProper map.left]
  locallyProjective : IsLocallyProjectiveOver map
  birational : IsBirationalMorphism map.left
  cartier : IsEffectiveCartier (I.comap map.left)
  crossings : IsStrictNormalCrossings source (reducedPullbackBoundary map.left I)
  unchanged : ∀ U : X.left.Opens,
    Disjoint (U : Set X.left) (I.support : Set X.left) →
      IsIso (map.left.resLE U (map.left ⁻¹ᵁ U) le_rfl)

end MathlibExt.AlgebraicGeometry.PrincipalizationModels
