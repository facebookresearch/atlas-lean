/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalSimplexIndexNerveSpan
import MathlibExt.AlgebraicTopology.SimplicialObject.CosimplicialHomInputEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveIndependentHomEquivalenceWeak

/-!
# Actual full Hom-input comma contractibility

The original simplex-resolution augmentation and full-index nerve
projection are weak. The same original point-map hypothesis therefore
makes the entire full simplex-index nerve point projection weak. The
canonical actual Hom input equivalence retains every source map.
-/

noncomputable section

universe u v

open CategoryTheory Opposite MorphismProperty
open scoped Simplicial

namespace SSet

/-- A genuinely weak original point projection implies weakness of the same full simplex-index nerve point map. -/
theorem originalSimplexIndexNerve_point_weak (K : SSet.{u})
    (hK : realizationWeakEquivalences (stdSimplex.isTerminalObj₀.from K)) :
    realizationWeakEquivalences (stdSimplex.isTerminalObj₀.from (nerve (SimplexIndex K))) := by
  have h := realizationWeakEquivalences.comp_mem _ _ (originalSimplexIndexAugmentation_weak K) hK
  have he : originalSimplexIndexAugmentation K ≫ stdSimplex.isTerminalObj₀.from K =
      originalSimplexIndexNerveProjection K ≫ stdSimplex.isTerminalObj₀.from (nerve (SimplexIndex K)) :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  exact realizationWeakEquivalences.of_precomp (originalSimplexIndexNerveProjection K) _
    (originalSimplexIndexNerveProjection_weak K) (he ▸ h)

end SSet
