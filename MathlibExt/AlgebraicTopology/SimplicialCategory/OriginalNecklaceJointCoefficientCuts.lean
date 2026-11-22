/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceJointCoefficients
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceCuts
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentIntervalFlagReadbacks
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceCutCoefficientReassembly

/-!
# Both SAME full original joint coefficient cuts

Each actual native cut retains the entire original coefficient preimage
and all its actual joints. The SAME original coherent composition of
both complete interval images reconstructs every original flag, in all
scalar degrees and with both endpoint cuts included.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace OriginalBeadInterval

variable (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints)

/-- The SAME full original prefix coefficient and its actual original joint property. -/
def leftJointCoefficient {q : SimplexCategoryᵒᵖ} (p : (fullCoefficient.{u} T).obj q) :
    (fullCoefficient.{u} (Cut.leftData T j hj)).obj q :=
  ⟨OriginalFlaggedNecklace.CutObjects.leftCoefficient (universalObject T p) j hj,
    fun i hi => p.property (Cut.leftEmbedding T j i) ((Cut.mem_leftJoints T j i).mp hi)⟩

/-- The SAME full original suffix coefficient and its actual original joint property. -/
def rightJointCoefficient {q : SimplexCategoryᵒᵖ} (p : (fullCoefficient.{u} T).obj q) :
    (fullCoefficient.{u} (Cut.rightData T j hj)).obj q :=
  ⟨OriginalFlaggedNecklace.CutObjects.rightCoefficient (universalObject T p) j hj,
    fun i hi => p.property (Cut.rightEmbedding T j i) ((Cut.mem_rightJoints T j i).mp hi)⟩

/-- Every entire original prefix flag is literally its actual full interval preimage. -/
theorem leftJointCoefficient_flags {q : SimplexCategoryᵒᵖ} (p : (fullCoefficient.{u} T).obj q)
    (t : Fin (q.unop.len + 1)) :
    ((leftJointCoefficient T j hj p).val.obj t).I =
      liftedEmbedding.{u} 0 j (Fin.zero_le j) ⁻¹' (p.val.obj t).I := rfl

/-- Every entire original suffix flag is literally its actual full interval preimage. -/
theorem rightJointCoefficient_flags {q : SimplexCategoryᵒᵖ} (p : (fullCoefficient.{u} T).obj q)
    (t : Fin (q.unop.len + 1)) :
    ((rightJointCoefficient T j hj p).val.obj t).I =
      liftedEmbedding.{u} j (Fin.last T.dimension) (Fin.le_last j) ⁻¹' (p.val.obj t).I := rfl

private instance {J : Type u} [LinearOrder J] (a b : J)
    (p r : SimplicialThickening.Path a b) : Subsingleton (p ⟶ r) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- Both SAME entire original cut coefficients reconstruct the original full coefficient
by actual coherent composition. -/
theorem jointCoefficient_composition {q : SimplexCategoryᵒᵖ} (p : (fullCoefficient.{u} T).obj q) :
    (CompositionFace.composition (ULift.up.{u} (0 : Fin (T.dimension + 1))) (ULift.up.{u} j)
      (ULift.up.{u} (Fin.last T.dimension))).app q
      ((homIso.{u} 0 j (Fin.zero_le j)).hom.app q (leftJointCoefficient T j hj p).val,
        (homIso.{u} j (Fin.last T.dimension) (Fin.le_last j)).hom.app q
          (rightJointCoefficient T j hj p).val) = p.val := by
  refine Functor.ext (fun t => ?_) ?_
  · apply SimplicialThickening.Path.ext
    have hL := homIso_hom_flags.{u} 0 j (Fin.zero_le j) (leftJointCoefficient T j hj p).val t
    have hR := homIso_hom_flags.{u} j (Fin.last T.dimension) (Fin.le_last j)
      (rightJointCoefficient T j hj p).val t
    exact (congrArg₂ (fun S R => S ∪ R) hL hR).trans
      (OriginalFlaggedNecklace.CutObjects.flag_preimage_union T j (p.val.obj t).I)
  · intro i k f
    exact Subsingleton.elim _ _

/-- Every SAME original scalar operator commutes with the entire prefix coefficient preimage. -/
theorem leftJointCoefficient_scalar {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r)
    (p : (fullCoefficient.{u} T).obj q) :
    (fullCoefficient (Cut.leftData T j hj)).map θ (leftJointCoefficient T j hj p) =
      leftJointCoefficient T j hj ((fullCoefficient T).map θ p) := rfl

/-- Every SAME original scalar operator commutes with the entire suffix coefficient preimage. -/
theorem rightJointCoefficient_scalar {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r)
    (p : (fullCoefficient.{u} T).obj q) :
    (fullCoefficient (Cut.rightData T j hj)).map θ (rightJointCoefficient T j hj p) =
      rightJointCoefficient T j hj ((fullCoefficient T).map θ p) := rfl

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
