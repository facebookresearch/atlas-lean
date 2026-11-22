/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceVertexFibreDescent

/-!
# The actual descended original necklace operator

The SAME native ordinal section gives the genuine operator through a
pair of original flanked surjections. All original endpoint and joint
maps are proved from the complete vertex-fibre theorem; every full
original target simplex is retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace OriginalBeadInterval

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The SAME native ordinal section composite of two original flanked maps. -/
def pairedOperator {A T V : Object K x y q} (f : A ⟶ T) (g : A ⟶ V) (hV : IsFlanked V) :
    ⦋V.necklace.dimension⦌ ⟶ ⦋T.necklace.dimension⦌ := by
  let := flanked_operator_epi g hV
  let := isSplitEpi_of_epi g.necklaceMap.operator
  exact section_ g.necklaceMap.operator ≫ f.necklaceMap.operator

/-- The SAME original vertex-fibre proof gives the entire genuine ordinal factorization. -/
theorem pairedOperator_factor {A T V : Object K x y q} (f : A ⟶ T) (g : A ⟶ V)
    (hA : IsFlanked A) (hT : IsFlanked T) (hV : IsFlanked V) (hND : TotallyNondegenerate T) :
    g.necklaceMap.operator ≫ pairedOperator f g hV = f.necklaceMap.operator := by
  let := flanked_operator_epi g hV
  let := isSplitEpi_of_epi g.necklaceMap.operator
  change g.necklaceMap.operator ≫ (section_ g.necklaceMap.operator ≫ f.necklaceMap.operator) = _
  ext i : 3
  apply paired_vertex_fibre_constant f g hA hT hV hND
  exact SimplexCategory.congr_toOrderHom_apply (IsSplitEpi.id g.necklaceMap.operator)
    (g.necklaceMap.operator.toOrderHom i)

/-- The descended original operator retains the SAME original initial vertex. -/
theorem pairedOperator_source {A T V : Object K x y q} (f : A ⟶ T) (g : A ⟶ V)
    (hA : IsFlanked A) (hT : IsFlanked T) (hV : IsFlanked V) (hND : TotallyNondegenerate T) :
    (pairedOperator f g hV).toOrderHom 0 = 0 := by
  have h := SimplexCategory.congr_toOrderHom_apply (pairedOperator_factor f g hA hT hV hND) 0
  change (pairedOperator f g hV).toOrderHom (g.necklaceMap.operator.toOrderHom 0) = _ at h
  rw [g.necklaceMap.source, f.necklaceMap.source] at h
  exact h

/-- The descended original operator retains the SAME original terminal vertex. -/
theorem pairedOperator_target {A T V : Object K x y q} (f : A ⟶ T) (g : A ⟶ V)
    (hA : IsFlanked A) (hT : IsFlanked T) (hV : IsFlanked V) (hND : TotallyNondegenerate T) :
    (pairedOperator f g hV).toOrderHom (Fin.last V.necklace.dimension) = Fin.last T.necklace.dimension := by
  have h := SimplexCategory.congr_toOrderHom_apply (pairedOperator_factor f g hA hT hV hND)
    (Fin.last A.necklace.dimension)
  change (pairedOperator f g hV).toOrderHom (g.necklaceMap.operator.toOrderHom _) = _ at h
  rw [g.necklaceMap.target, f.necklaceMap.target] at h
  exact h

/-- Every actual original source joint of the descended map goes to an original target joint. -/
theorem pairedOperator_joint_maps {A T V : Object K x y q} (f : A ⟶ T) (g : A ⟶ V)
    (hA : IsFlanked A) (hT : IsFlanked T) (hV : IsFlanked V) (hND : TotallyNondegenerate T)
    (j : Fin (V.necklace.dimension + 1)) (hj : j ∈ V.necklace.joints) :
    (pairedOperator f g hV).toOrderHom j ∈ T.necklace.joints := by
  obtain ⟨i, hi, hij⟩ := (flanked_joint_image g hA hV j).mp hj
  have he := SimplexCategory.congr_toOrderHom_apply (pairedOperator_factor f g hA hT hV hND) i
  change (pairedOperator f g hV).toOrderHom (g.necklaceMap.operator.toOrderHom i) = _ at he
  rw [hij] at he
  exact he.symm ▸ flanked_joint_maps f hA hT i hi

/-- The descended original operator retains EVERY full native source simplex. -/
theorem pairedOperator_lands {A T V : Object K x y q} (f : A ⟶ T) (g : A ⟶ V)
    (hA : IsFlanked A) (hT : IsFlanked T) (hV : IsFlanked V) (hND : TotallyNondegenerate T) :
    complex.{0} V.necklace.joints ≤ (complex.{0} T.necklace.joints).preimage
      (SSet.stdSimplex.map (pairedOperator f g hV)) := by
  rintro ⟨⟨d⟩⟩ s hs
  obtain ⟨a, ha⟩ := map_surjective_all_simplices.{0} g.necklaceMap
    (flanked_operator_surjective g hV) (flanked_joint_image g hA hV) d ⟨s, hs⟩
  have hg : (SSet.stdSimplex.map g.necklaceMap.operator).app (op ⦋d⦌) a.val = s :=
    congrArg Subtype.val ha
  have hl := f.necklaceMap.lands (op ⦋d⦌) a.property
  change (SSet.stdSimplex.map f.necklaceMap.operator).app (op ⦋d⦌) a.val ∈
    (complex.{0} T.necklace.joints).obj (op ⦋d⦌) at hl
  have he : SSet.stdSimplex.map g.necklaceMap.operator ≫
      SSet.stdSimplex.map (pairedOperator f g hV) = SSet.stdSimplex.map f.necklaceMap.operator := by
    rw [← SSet.stdSimplex.map_comp, pairedOperator_factor f g hA hT hV hND]
  rw [← he, NatTrans.comp_app_apply, hg] at hl
  exact hl

/-- The SAME original descended native necklace morphism, with its full actual simplex containment. -/
def pairedMorphism {A T V : Object K x y q} (f : A ⟶ T) (g : A ⟶ V)
    (hA : IsFlanked A) (hT : IsFlanked T) (hV : IsFlanked V) (hND : TotallyNondegenerate T) :
    V.necklace ⟶ T.necklace where
  operator := pairedOperator f g hV
  source := pairedOperator_source f g hA hT hV hND
  target := pairedOperator_target f g hA hT hV hND
  lands := pairedOperator_lands f g hA hT hV hND

/-- Both SAME full original native maps have the genuine original composition readback. -/
theorem pairedMorphism_factor {A T V : Object K x y q} (f : A ⟶ T) (g : A ⟶ V)
    (hA : IsFlanked A) (hT : IsFlanked T) (hV : IsFlanked V) (hND : TotallyNondegenerate T) :
    g.necklaceMap ≫ pairedMorphism f g hA hT hV hND = f.necklaceMap :=
  SSet.OriginalNecklace.Morphism.ext (pairedOperator_factor f g hA hT hV hND)

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
