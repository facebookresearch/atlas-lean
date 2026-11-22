/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedJoinedBeadMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentPathReadbacks

/-!
# The SAME original full component composition relation

Both full original interval generators map from their actual native
concatenation to the SAME complete original composition generator.
The original whole input simplex, all coefficients and the entire
original composition equation are retained, in every scalar degree.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components

open OriginalBead OriginalBeadInterval SimplicialEnrichment SimplicialQuiver SSet.OriginalNecklace

variable {K : SSet.{u}} {n : SimplexCategory} {q : SimplexCategoryᵒᵖ}
    (σ : K.obj (op n)) (i j k : coherentSimplex.{u} n) {x y z : K _⦋0⦌}
    (hx : vertex K σ i = x) (hy : vertex K σ j = y) (hz : vertex K σ k = z)
    (a : (i ⟶[SSet.{u}] j).obj q) (b : (j ⟶[SSet.{u}] k).obj q)

/-- The SAME entire original first generator in the original composition equation. -/
def compositionLeft : Arrow K x y q := arrow K σ i j hx hy a

/-- The SAME entire original second generator in the original composition equation. -/
def compositionRight : Arrow K y z q := arrow K σ j k hy hz b

/-- The SAME actual original coherent composition generator with its full union coefficient. -/
def compositionTarget : Arrow K x z q :=
  arrow K σ i k hx hz ((eComp SSet.{u} i j k).app q (a, b))

private theorem leftOrder (a : (i ⟶[SSet.{u}] j).obj q) : i.as.down ≤ j.as.down :=
  show i.as ≤ j.as from ((show (nerve (SimplicialThickening.Path i.as j.as)).obj q from a).obj 0).le

private theorem rightOrder (b : (j ⟶[SSet.{u}] k).obj q) : j.as.down ≤ k.as.down :=
  show j.as ≤ k.as from ((show (nerve (SimplicialThickening.Path j.as k.as)).obj q from b).obj 0).le

/-- The SAME original full native map from the two original generator necklaces to their original composition. -/
def generatorCompositionMorphism :
    (concat (generatorObject (compositionLeft σ i j hx hy a))
      (generatorObject (compositionRight σ j k hy hz b))).necklace ⟶
        (generatorObject (compositionTarget σ i j k hx hz a b)).necklace :=
  joinedBeadMorphism i.as.down j.as.down k.as.down (leftOrder i j a) (rightOrder j k b)

/-- Both entire original generator input maps commute under their SAME actual native composition map. -/
theorem generatorComposition_over :
    (generatorCompositionMorphism σ i j k hx hy hz a b).map.{u} ≫
      (generatorObject (compositionTarget σ i j k hx hz a b)).input =
        (concat (generatorObject (compositionLeft σ i j hx hy a))
          (generatorObject (compositionRight σ j k hy hz b))).input := by
  apply (concat_isPushout (beadData (length i.as.down j.as.down))
    (beadData (length j.as.down k.as.down))).hom_ext
  · exact (joinedBead_prefix_input.{u} i.as.down j.as.down k.as.down
      (leftOrder i j a) (rightOrder j k b) K σ).trans
      (concat_first_input (generatorObject (compositionLeft σ i j hx hy a))
        (generatorObject (compositionRight σ j k hy hz b))).symm
  · exact (joinedBead_suffix_input.{u} i.as.down j.as.down k.as.down
      (leftOrder i j a) (rightOrder j k b) K σ).trans
      (concat_second_input (generatorObject (compositionLeft σ i j hx hy a))
        (generatorObject (compositionRight σ j k hy hz b))).symm

/-- EVERY actual original full composition flag retains precisely the SAME native image equation. -/
theorem generatorComposition_flags :
    (OriginalBead.OuterOperator.map
      (generatorCompositionMorphism σ i j k hx hy hz a b).operator
      (generatorCompositionMorphism σ i j k hx hy hz a b).source
      (generatorCompositionMorphism σ i j k hx hy hz a b).target).app q
      (concat (generatorObject (compositionLeft σ i j hx hy a))
        (generatorObject (compositionRight σ j k hy hz b))).coefficient =
      (generatorObject (compositionTarget σ i j k hx hz a b)).coefficient :=
  joinedCoefficient i.as.down j.as.down k.as.down (leftOrder i j a) (rightOrder j k b) a b

/-- The SAME entire original composition equation is witnessed by its actual full flagged map. -/
def generatorCompositionMap :
    concat (generatorObject (compositionLeft σ i j hx hy a))
      (generatorObject (compositionRight σ j k hy hz b)) ⟶
        generatorObject (compositionTarget σ i j k hx hz a b) where
  necklaceMap := generatorCompositionMorphism σ i j k hx hy hz a b
  over := generatorComposition_over σ i j k hx hy hz a b
  flags := generatorComposition_flags σ i j k hx hy hz a b

/-- The SAME actual full coherent composition generator has the two original generator components as its composition. -/
theorem composition_component :
    ConnectedComponents.mk (generatorObject (compositionTarget σ i j k hx hz a b)) =
      concatenate (ConnectedComponents.mk (generatorObject (compositionLeft σ i j hx hy a)))
        (ConnectedComponents.mk (generatorObject (compositionRight σ j k hy hz b))) :=
  (_root_.Quotient.sound (Zigzag.of_hom (generatorCompositionMap σ i j k hx hy hz a b))).symm

/-- The actual original coherent composition equation is retained on the SAME entire original paths. -/
theorem interpretation_composition :
    (interpretation K).evalPath q
      (arrowPath K σ i k hx hz ((eComp SSet.{u} i j k).app q (a, b))) =
      (interpretation K).evalPath q
        (@Quiver.Path.comp (K _⦋0⦌) (quiverAt (generatingQuiver K) q) x y z
          (arrowPath K σ i j hx hy a) (arrowPath K σ j k hy hz b)) := by
  rw [interpretation_comp]
  exact (interpretation_arrow (compositionTarget σ i j k hx hz a b)).trans
    ((composition_component σ i j k hx hy hz a b).trans
      (congrArg₂ concatenate (interpretation_arrow (compositionLeft σ i j hx hy a)).symm
        (interpretation_arrow (compositionRight σ j k hy hz b)).symm))

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components
