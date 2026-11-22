/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightMappingPointedDiagram
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontJoyalPointedDiagram

/-!
# The original right-mapping space on the named pointed Joyal carrier

Both full pointed Hom directions use the existing carrier equivalence.
The full simplicial isomorphism retains the original quotient maps,
successor simplices and every scalar operator.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping

open OriginalFixedFrontContraction

variable {K : SSet.{u}} (a b : (Δ[0] : SSet.{u}) ⟶ K)

/-- The actual full pointed Hom equivalence retains the original underlying morphism in each direction. -/
def pointedCopyHomEquiv (n : ℕ) :
    (pointedObject.{u} n ⟶ pointedInput a b) ≃
      (pointedCopyFunctor.obj (pointedObject.{u} n) ⟶ pointedCopyFunctor.obj (pointedInput a b)) where
  toFun := pointedCopyFunctor.map
  invFun := pointedRawFunctor.map
  left_inv g := by
    apply Under.UnderMorphism.ext
    rfl
  right_inv g := by
    apply Under.UnderMorphism.ext
    apply JoyalSSet.homEquiv.injective
    rfl

/-- The entire original endpoint-fixed Hom space on the genuine named Joyal carrier. -/
def pointedJoyalHomSpace : SSet.{u} :=
  pointedJoyalDiagram.op ⋙ yoneda.obj (pointedCopyFunctor.obj (pointedInput a b))

/-- Both actual full simplicial maps copy the same original pointed Hom simplices and operators. -/
def pointedHomCopyIso : pointedHomSpace a b ≅ pointedJoyalHomSpace a b :=
  NatIso.ofComponents (fun q => (pointedCopyHomEquiv a b q.unop.len).toIso) (by
    intro q r θ
    apply ConcreteCategory.hom_ext
    intro g
    apply Under.UnderMorphism.ext
    apply JoyalSSet.homEquiv.injective
    rfl)

/-- The same original right-mapping space is the entire original pointed Joyal Hom space. -/
def pointedJoyalHomSpaceIso : SSet.mappingSpaceRight K a b ≅ pointedJoyalHomSpace a b :=
  pointedHomSpaceIso a b ≪≫ pointedHomCopyIso a b

/-- Every copied full Hom simplex retains the same original quotient map. -/
theorem pointedJoyalHomSpaceIso_app (n : ℕ) (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) :
    JoyalSSet.forget.map (((pointedJoyalHomSpaceIso a b).hom.app (op ⦋n⦌)) σ).right =
      quotientMap a b σ := rfl

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
