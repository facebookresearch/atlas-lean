/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklacePairedOperator

/-!
# Genuine original paired-surjection lifting

The actual original map to a totally nondegenerate target descends
uniquely through the other full original flanked map. The result retains
both complete native maps, the full original input square and EVERY
original coefficient flag. No existence or comparison certificate is
supplied.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace OriginalBead.TerminalFlag

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The SAME whole native original map factorization is the original simplicial-set composition. -/
theorem pairedMorphism_map_factor {A T V : Object K x y q} (f : A ⟶ T) (g : A ⟶ V)
    (hA : IsFlanked A) (hT : IsFlanked T) (hV : IsFlanked V) (hND : TotallyNondegenerate T) :
    g.necklaceMap.map.{u} ≫ (pairedMorphism f g hA hT hV hND).map = f.necklaceMap.map := by
  have h := congrArg (fun m : A.necklace ⟶ T.necklace => m.map.{u})
    (pairedMorphism_factor f g hA hT hV hND)
  change (SSet.OriginalNecklace.Morphism.comp g.necklaceMap
    (pairedMorphism f g hA hT hV hND)).map = _ at h
  rw [SSet.OriginalNecklace.Morphism.map_comp] at h
  exact h

/-- The entire original input maps commute for the SAME actual descended morphism. -/
theorem pairedMorphism_over {A T V : Object K x y q} (f : A ⟶ T) (g : A ⟶ V)
    (hA : IsFlanked A) (hT : IsFlanked T) (hV : IsFlanked V) (hND : TotallyNondegenerate T) :
    (pairedMorphism f g hA hT hV hND).map.{u} ≫ T.input = V.input := by
  let := flanked_full_map_epi g hA hV
  apply (cancel_epi g.necklaceMap.map.{u}).1
  rw [← Category.assoc, pairedMorphism_map_factor, f.over, g.over]

/-- EVERY original target flag is the SAME exact direct image under the actual descended morphism. -/
theorem pairedMorphism_flags {A T V : Object K x y q} (f : A ⟶ T) (g : A ⟶ V)
    (hA : IsFlanked A) (hT : IsFlanked T) (hV : IsFlanked V) (hND : TotallyNondegenerate T) :
    (OriginalBead.OuterOperator.map (pairedMorphism f g hA hT hV hND).operator
      (pairedMorphism f g hA hT hV hND).source
      (pairedMorphism f g hA hT hV hND).target).app q V.coefficient = T.coefficient := by
  have hf := f.flags
  rw [← pairedMorphism_factor f g hA hT hV hND] at hf
  change (OriginalBead.OuterOperator.map
    (g.necklaceMap.operator ≫ (pairedMorphism f g hA hT hV hND).operator)
    ((congrArg (pairedMorphism f g hA hT hV hND).operator.toOrderHom g.necklaceMap.source).trans
      (pairedMorphism f g hA hT hV hND).source)
    ((congrArg (pairedMorphism f g hA hT hV hND).operator.toOrderHom g.necklaceMap.target).trans
      (pairedMorphism f g hA hT hV hND).target)).app q A.coefficient = T.coefficient at hf
  rw [OriginalBead.OuterOperator.map_comp] at hf
  change (OriginalBead.OuterOperator.map (pairedMorphism f g hA hT hV hND).operator
    (pairedMorphism f g hA hT hV hND).source (pairedMorphism f g hA hT hV hND).target).app q
    ((OriginalBead.OuterOperator.map g.necklaceMap.operator g.necklaceMap.source
      g.necklaceMap.target).app q A.coefficient) = T.coefficient at hf
  rw [g.flags] at hf
  exact hf

/-- The SAME actual original flagged-necklace lift through the pair of original full surjections. -/
def pairedLift {A T V : Object K x y q} (f : A ⟶ T) (g : A ⟶ V)
    (hA : IsFlanked A) (hT : IsFlanked T) (hV : IsFlanked V) (hND : TotallyNondegenerate T) : V ⟶ T where
  necklaceMap := pairedMorphism f g hA hT hV hND
  over := pairedMorphism_over f g hA hT hV hND
  flags := pairedMorphism_flags f g hA hT hV hND

/-- The SAME actual original lift has its whole original composition readback. -/
theorem pairedLift_factor {A T V : Object K x y q} (f : A ⟶ T) (g : A ⟶ V)
    (hA : IsFlanked A) (hT : IsFlanked T) (hV : IsFlanked V) (hND : TotallyNondegenerate T) :
    g ≫ pairedLift f g hA hT hV hND = f :=
  Hom.ext (pairedMorphism_factor f g hA hT hV hND)

/-- The original paired-surjection lift is unique, retaining the SAME source and target maps. -/
theorem pairedLift_unique {A T V : Object K x y q} (f : A ⟶ T) (g : A ⟶ V)
    (hA : IsFlanked A) (hT : IsFlanked T) (hV : IsFlanked V) (hND : TotallyNondegenerate T)
    (l : V ⟶ T) : l = pairedLift f g hA hT hV hND :=
  totallyNondegenerate_map_unique l (pairedLift f g hA hT hV hND) hV hT hND

/-- The genuine paired-surjection descent has a unique ACTUAL original flagged map and exact original readback. -/
theorem existsUnique_pairedLift {A T V : Object K x y q} (f : A ⟶ T) (g : A ⟶ V)
    (hA : IsFlanked A) (hT : IsFlanked T) (hV : IsFlanked V) (hND : TotallyNondegenerate T) :
    ∃! l : V ⟶ T, g ≫ l = f :=
  ⟨pairedLift f g hA hT hV hND, pairedLift_factor f g hA hT hV hND,
    fun l _hl => pairedLift_unique f g hA hT hV hND l⟩

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
