/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexResolutionAugmentationWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanPointFiberComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHomotopyInvarianceUniverses
import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexWeakEquivalences

/-!
# The original full simplex-index nerve weak span

The canonical original identity-pullback simplex resolution retains
all representing simplices. Its augmentation is genuinely weak. Each
full coefficient is the same original standard simplex through the
actual second pullback projection, so the canonical full-index nerve
projection is weak as well. No choice of simplices or fibrancy premise
is supplied.
-/

noncomputable section

universe u

open CategoryTheory Opposite Limits MorphismProperty
open scoped Simplicial

namespace SSet

/-- The actual canonical original identity simplex-pullback resolution. -/
def originalSimplexIndexResolution (K : SSet.{u}) : SSet.{u} :=
  simplexResolution (𝟙 K)

/-- The same full original resolution augmentation retaining every representing source simplex. -/
def originalSimplexIndexAugmentation (K : SSet.{u}) : originalSimplexIndexResolution K ⟶ K :=
  simplexResolutionAugmentation (𝟙 K)

/-- The same entire original simplex-index nerve projection from its actual identity-pullback resolution. -/
def originalSimplexIndexNerveProjection (K : SSet.{u}) :
    originalSimplexIndexResolution K ⟶ nerve (SimplexIndex K) :=
  bkHocolimToNerve (simplexPullbackDiagram (𝟙 K))

/-- Every whole original identity-pullback coefficient has its genuinely weak point projection. -/
theorem originalSimplexIndexCoefficient_point_weak (K : SSet.{u}) (s : SimplexIndex K) :
    realizationWeakEquivalences
      (stdSimplex.isTerminalObj₀.from ((simplexPullbackDiagram (𝟙 K)).obj s)) := by
  let e : pullback (𝟙 K) s.hom ⟶ SSet.stdSimplex.obj s.left := pullback.snd (𝟙 K) s.hom
  have hw : realizationWeakEquivalences e := realizationWeakEquivalences.of_isIso e
  have ht := stdSimplex_to_point_mem_realizationWeakEquivalences s.left
  have he : e ≫ stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj s.left) =
      stdSimplex.isTerminalObj₀.from ((simplexPullbackDiagram (𝟙 K)).obj s) :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  exact he ▸ realizationWeakEquivalences.comp_mem _ _ hw ht

/-- The same canonical full original simplex-index augmentation is weak in every universe. -/
theorem originalSimplexIndexAugmentation_weak (K : SSet.{u}) :
    realizationWeakEquivalences (originalSimplexIndexAugmentation K) :=
  simplexResolutionAugmentation_mem_realizationWeakEquivalences (𝟙 K)

/-- The same canonical full original simplex-index nerve projection is weak in every universe. -/
theorem originalSimplexIndexNerveProjection_weak (K : SSet.{u}) :
    realizationWeakEquivalences (originalSimplexIndexNerveProjection K) := by
  have hw := bkHocolimMap_weak_universes
    (bkDiagramToPoint (simplexPullbackDiagram (𝟙 K)))
    (originalSimplexIndexCoefficient_point_weak K)
  exact RespectsIso.postcomp realizationWeakEquivalences (bkPointIsoNerve (SimplexIndex K)).hom
    (bkHocolimMap (bkDiagramToPoint (simplexPullbackDiagram (𝟙 K)))) hw

end SSet
