/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedBeadOperator

/-!
# The SAME actual original component identity relation

Every genuinely zero-dimensional full original bead has its actual
original map to the zero necklace. Thus the original coherent identity
generator has precisely the original unit component, in every scalar.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalBead SSet.OriginalNecklace SimplicialEnrichment SimplicialQuiver

variable {K : SSet.{u}} {x : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- A genuine zero-dimensional original bead has the SAME original zero-necklace component. -/
theorem zeroBead_component (b : Bead K x x q) (h0 : b.dimension = 0) :
    ConnectedComponents.mk (ofBead b) = ConnectedComponents.mk (unit K q x) := by
  cases b with
  | mk n σ hx hy p =>
    change n = 0 at h0
    subst n
    have hσ : σ = x := by
      change K.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op σ = x at hx
      rw [SimplexCategory.const_eq_id] at hx
      exact (ConcreteCategory.congr_hom (K.map_id (op ⦋0⦌)) σ).symm.trans hx
    subst σ
    let f : ofBead (Bead.mk 0 x hx hy p) ⟶ unit K q x :=
      { necklaceMap := Point.necklaceMap (beadData 0)
        over := by
          change (Point.necklaceMap (beadData 0)).map.{u} ≫
            ((complex Point.data.joints).ι ≫ SSet.yonedaEquiv.symm x) =
              (complex (beadData 0).joints).ι ≫ SSet.yonedaEquiv.symm x
          rw [← Category.assoc, Morphism.map_ι, Category.assoc]
          change (complex (beadData 0).joints).ι ≫
            SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) ≫
              SSet.yonedaEquiv.symm x = _
          rw [SimplexCategory.const_eq_id]
          rw [Functor.map_id, Category.id_comp]
        flags := HomUnitsAndEmpty.diagonalSimplex_unique
          (ULift.up.{u} (0 : Fin 1)) q _ _ }
    exact _root_.Quotient.sound (Zigzag.of_hom f)

namespace Components

/-- The SAME original coherent identity generator maps to precisely the original component unit. -/
theorem interpretation_identity {n : SimplexCategory} (σ : K.obj (op n))
    (i : coherentSimplex.{u} n) (hx : vertex K σ i = x) :
    (interpretation K).evalPath q
      (arrowPath K σ i i hx hx ((eId SSet.{u} i).app q PUnit.unit)) =
        (identity K x).app q PUnit.unit := by
  let a : Arrow K x x q :=
    arrow K σ i i hx hx ((eId SSet.{u} i).app q PUnit.unit)
  have h := ConcreteCategory.congr_hom
    (congr_app ((interpretation K).generator_eval x x) q) a
  change (interpretation K).evalPath q
    (arrowPath K σ i i hx hx ((eId SSet.{u} i).app q PUnit.unit)) =
      ConnectedComponents.mk (ofBead (trim a)) at h
  refine h.trans (zeroBead_component (trim a) ?_)
  change i.as.down.val - i.as.down.val = 0
  exact Nat.sub_self _

end Components

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
