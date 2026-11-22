/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceBeadImageOperators
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceSurjections

/-!
# Same original input simplices of complete necklace beads

The actual input of every full bead interval is its original Yoneda
simplex. Under an original flagged map, its factorization retains the
SAME complete interval operator and target bead. Total nondegeneracy is
stated on these genuine original input simplices.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace
open OriginalBeadInterval

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The SAME original input simplex on an actual full positive necklace bead. -/
def beadInputSimplex (T : Object K x y q) {a b : Fin (T.necklace.dimension + 1)}
    (h : IsBead T.necklace a b) : K _⦋length a b⦌ :=
  SSet.yonedaEquiv (beadMap h ≫ T.input)

/-- Every actual full original bead input is genuinely nondegenerate. -/
def TotallyNondegenerate (T : Object K x y q) : Prop :=
  ∀ (a b : Fin (T.necklace.dimension + 1)) (h : IsBead T.necklace a b),
    beadInputSimplex T h ∈ K.nonDegenerate (length a b)

/-- The actual input on a whole positive bead retains the SAME original image-bead factorization. -/
theorem beadInputSimplex_factor {T U : Object K x y q} (f : T ⟶ U)
    (hT : IsFlanked T) (hU : IsFlanked U)
    {a b : Fin (T.necklace.dimension + 1)} (h : IsBead T.necklace a b)
    (hab : f.necklaceMap.operator.toOrderHom a < f.necklaceMap.operator.toOrderHom b) :
    K.map (beadImageOperator f.necklaceMap h).op
        (beadInputSimplex U (bead_image f.necklaceMap h (flanked_joint_maps f hT hU) hab)) =
      beadInputSimplex T h := by
  unfold beadInputSimplex
  rw [SSet.yonedaEquiv_naturality, ← Category.assoc,
    beadMap_image_square f.necklaceMap h (flanked_joint_maps f hT hU) hab,
    Category.assoc, f.over]

/-- The SAME image-bead factor is genuinely epi, from the actual original full final flag. -/
theorem beadInputSimplex_factor_epi {T U : Object K x y q} (f : T ⟶ U)
    (hU : IsFlanked U) {a b : Fin (T.necklace.dimension + 1)}
    (h : IsBead T.necklace a b) : Epi (beadImageOperator f.necklaceMap h) :=
  beadImageOperator_epi f.necklaceMap h (flanked_operator_surjective f hU)

/-- The same complete original input vertex at any original necklace vertex. -/
def inputVertex (T : Object K x y q) (j : Fin (T.necklace.dimension + 1)) : K _⦋0⦌ :=
  SSet.yonedaEquiv (vertexMap T.necklace.joints j ≫ T.input)

/-- The whole original input vertex follows the SAME original flagged morphism. -/
theorem inputVertex_map {T U : Object K x y q} (f : T ⟶ U)
    (i : Fin (T.necklace.dimension + 1)) :
    inputVertex U (f.necklaceMap.operator.toOrderHom i) = inputVertex T i := by
  unfold inputVertex
  rw [← Morphism.vertex_map, Category.assoc, f.over]

/-- The full original source-bead simplex is the original degenerate vertex when that bead collapses. -/
theorem beadInputSimplex_collapsed {T U : Object K x y q} (f : T ⟶ U)
    {a b : Fin (T.necklace.dimension + 1)} (h : IsBead T.necklace a b)
    (hab : f.necklaceMap.operator.toOrderHom a = f.necklaceMap.operator.toOrderHom b) :
    beadInputSimplex T h = K.map (SimplexCategory.const ⦋length a b⦌ ⦋0⦌ 0).op
      (inputVertex U (f.necklaceMap.operator.toOrderHom a)) := by
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_symm_naturality_left]
  unfold beadInputSimplex inputVertex
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hm : beadMap.{u} h ≫ f.necklaceMap.map =
      SSet.stdSimplex.map (SimplexCategory.const ⦋length a b⦌ ⦋0⦌ 0) ≫
        vertexMap U.necklace.joints (f.necklaceMap.operator.toOrderHom a) := by
    apply (cancel_mono (complex.{u} U.necklace.joints).ι).1
    rw [Category.assoc, Morphism.map_ι, ← Category.assoc, beadMap_ι,
      Category.assoc, vertexMap_ι, ← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
    congr 1
    ext i : 3
    exact bead_collapsed f.necklaceMap h hab i
  calc
    beadMap h ≫ T.input = (beadMap h ≫ f.necklaceMap.map) ≫ U.input := by
      rw [Category.assoc, f.over]
    _ = _ := (congrArg (fun m => m ≫ U.input) hm).trans (Category.assoc _ _ _)

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
