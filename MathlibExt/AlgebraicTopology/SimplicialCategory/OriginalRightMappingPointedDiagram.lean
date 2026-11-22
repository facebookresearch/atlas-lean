/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightMappingPointedHom

/-!
# The SAME full original right-mapping pointed Hom diagram

The actual fixed-front quotient maps retain every original scalar
operator. The genuine endpoint-fixed cosimplicial diagram has exactly
the original right-mapping space as its simplicial Hom space, with both
inverse maps retaining every original quotient and successor simplex.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping

open OriginalFixedFrontContraction

variable {K : SSet.{u}} (a b : (Δ[0] : SSet.{u}) ⟶ K)

/-- The SAME original pointed-resolution Hom space, retaining the full actual endpoint-fixed diagram. -/
def pointedHomSpace : SSet.{u} := pointedCosimplicialObject.op ⋙ yoneda.obj (pointedInput a b)

/-- Every original right-mapping scalar operator retains the SAME entire pointed quotient map. -/
theorem toPointedMap_operator {n m : ℕ} (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (σ : (SSet.mappingSpaceRight K a b) _⦋m⦌) :
    pointedMap.{u} θ ≫ toPointedMap a b σ =
      toPointedMap a b ((SSet.mappingSpaceRight K a b).map θ.op σ) := by
  apply Under.UnderMorphism.ext
  exact quotientMap_operator a b θ σ

/-- Both full inverse simplicial maps identify the SAME original right-mapping space with its entire pointed Hom
space. -/
def pointedHomSpaceIso : SSet.mappingSpaceRight K a b ≅ pointedHomSpace a b :=
  NatIso.ofComponents (fun q => (pointedHomEquiv a b q.unop.len).toIso) (by
    intro q r θ
    apply ConcreteCategory.hom_ext
    intro σ
    apply Under.UnderMorphism.ext
    exact (quotientMap_operator a b θ.unop σ).symm)

/-- Every original right-mapping simplex retains its SAME entire quotient map under the full diagram isomorphism. -/
theorem pointedHomSpaceIso_app (n : ℕ) (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) :
    ((pointedHomSpaceIso a b).hom.app (op ⦋n⦌) σ).right = quotientMap a b σ := rfl

/-- Every original pointed-resolution simplex retains its SAME projected successor map under the inverse diagram
isomorphism. -/
theorem pointedHomSpaceIso_inv_successor (n : ℕ) (g : pointedObject.{u} n ⟶ pointedInput a b) :
    successor a b ((pointedHomSpaceIso a b).inv.app (op ⦋n⦌) g) = FixedFrontCollapse.projection n ≫ g.right :=
  fromPointedMap_successor a b g

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
