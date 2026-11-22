/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceHocolimNerveWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklacePointedInputEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveIndependentHomEquivalenceWeak

/-!
# The same full native input-category nerve point map

The two genuine original hocolim augmentations detect point weakness of
the same complete native input category. Its original raw endpoint Hom
point hypothesis is explicit and does not assert the right-Q comparison.
The actual pointed input equivalence retains all original arrows.
-/

noncomputable section

universe u

open CategoryTheory Opposite MorphismProperty
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceInput

/-- The same complete original native input nerve has weak point projection when its actual raw endpoint Hom does. -/
theorem inputNerve_point_weak (K : SSet.{u}) (x y : K _⦋0⦌)
    (hK : SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from (hom K x y))) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from (nerve (Object K x y))) := by
  have hc := SSet.realizationWeakEquivalences.comp_mem _ _ (hocolimRawAugmentation_weak K x y) hK
  have he : hocolimRawAugmentation K x y ≫ SSet.stdSimplex.isTerminalObj₀.from (hom K x y) =
      hocolimNerveProjection K x y ≫ SSet.stdSimplex.isTerminalObj₀.from (nerve (Object K x y)) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact SSet.realizationWeakEquivalences.of_precomp (hocolimNerveProjection K x y) _
    (hocolimNerveProjection_weak K x y) (he ▸ hc)

end CategoryTheory.CoherentRealization.OriginalNecklaceInput
