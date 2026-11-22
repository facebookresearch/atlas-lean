/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexPullbackQuillen
import MathlibExt.CategoryTheory.MorphismProperty.SharpOverPullbackRecognition

/-!
# Genuine sharpness recognition by all original simplex transitions

For the SAME original simplicial map, sharpness is equivalent to weakness
of every full original transition in its actual simplex-pullback diagram.
Necessity uses the original universal base-change condition. Sufficiency
uses the proved full face/horn geometry, the SAME actual pullback Quillen
adjunction and Brown preservation of every weak original over-map.
This proves Rezk's Theorem 4.1 in simplicial sets with every base and arity.
It assumes no Kan, quasicategory or desired global weak outcome.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty
open scoped Simplicial

namespace SSet

variable {E B : SSet.{u}}

/-- A fully sharp original map makes every SAME complete original simplex transition weak. -/
theorem sharpMaps_simplexPullbackTransition (p : E ⟶ B)
    (hp : sharpMaps realizationWeakEquivalences p)
    {s t : SimplexIndex B} (a : s ⟶ t) :
    realizationWeakEquivalences ((simplexPullbackDiagram p).map a) := by
  have ht : realizationWeakEquivalences.IsStableUnderBaseChangeAlong (pullback.snd p t.hom) :=
    hp (pullback.fst p t.hom) t.hom (pullback.snd p t.hom) (IsPullback.of_hasPullback p t.hom).flip
  exact ht.of_isPullback (simplexPullbackTransition_isPullback p a).flip
    (stdSimplex_map_mem_realizationWeakEquivalences (SSet.stdSimplex.map a.left))

/-- Full sharpness is recognized by ALL actual original simplex-pullback transitions,
on the SAME original map and every original coefficient universe. -/
theorem sharpMaps_iff_simplexPullbackTransitions (p : E ⟶ B) :
    sharpMaps realizationWeakEquivalences p ↔
      ∀ {s t : SimplexIndex B} (a : s ⟶ t),
        realizationWeakEquivalences ((simplexPullbackDiagram p).map a) := by
  constructor
  · exact sharpMaps_simplexPullbackTransition p
  · intro h
    exact (MorphismProperty.sharpMaps_iff_overPullback realizationWeakEquivalences p).mpr
      (fun {_ _} f hf => SimplexPullback.pullback_map_mem_realizationWeakEquivalences p h f hf)

end SSet
