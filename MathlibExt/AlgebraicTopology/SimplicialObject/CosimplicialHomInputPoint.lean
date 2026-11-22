/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialObject.CosimplicialHomInputEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalSimplexIndexContractible
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence

/-!
# Genuine original Hom input-category nerve point comparison

The full same original Hom simplex-input equivalence and actual
canonical simplex-resolution weak span give contractibility of the
entire original cosimplicial input category from the genuine full
Hom point-map property. Category object and Hom universes remain
independent.
-/

noncomputable section

universe u v

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The full same original Hom input-category nerve has weak point projection when its actual Hom simplicial object
does. -/
theorem homInputNerve_point_weak (D : CosimplicialObject C) (K : C)
    (hK : SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from (homSpace D K))) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from (nerve (CostructuredArrow D K))) := by
  let e := homInputEquivalence D K
  have hf : SSet.realizationWeakEquivalences (nerveMap e.functor) :=
    nerveMap_mem_realizationWeakEquivalences_of_isEquivalence e.functor
  have hp := SSet.originalSimplexIndexNerve_point_weak (homSpace D K) hK
  have he : nerveMap e.functor ≫ SSet.stdSimplex.isTerminalObj₀.from (nerve (CostructuredArrow D K)) =
      SSet.stdSimplex.isTerminalObj₀.from (nerve (SSet.SimplexIndex (homSpace D K))) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact SSet.realizationWeakEquivalences.of_precomp (nerveMap e.functor) _ hf (he.symm ▸ hp)

end CategoryTheory.CosimplicialObject
