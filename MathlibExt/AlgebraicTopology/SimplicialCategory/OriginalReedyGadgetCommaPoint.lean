/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalReedyFibrantGadgetFunctor
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalReedyPointedHomIso
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveIndependentHomEquivalenceWeak

/-!
# Genuine original Reedy fibrant-gadget comma point weakness

The canonical pre-equivalence and full-subcategory post-equivalence
retain every original input into the same actual fibrant gadget.
The genuine original full Reedy Hom point theorem contracts the entire
comma nerve, with the original source and target maps unchanged.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The full original Reedy comma category is the whole original plain pointed Hom input category at its gadget
target. -/
def reedyGadgetCommaEquivalence (K : OriginalPointed.Category.{u})
    (Y : CostructuredArrow OriginalPointed.fibrantGadgetFullInclusion K) :
    CostructuredArrow (reedyIntoFibrantGadgetInputs K) Y ≌
      CostructuredArrow plainReedyDiagram Y.left.obj.obj := by
  let _ : OriginalPointed.fibrantGadgetFullInclusion.{u}.Full := by
    change (ObjectProperty.ι _ ⋙ ObjectProperty.ι _).Full
    infer_instance
  let _ : OriginalPointed.fibrantGadgetFullInclusion.{u}.Faithful := by
    change (ObjectProperty.ι _ ⋙ ObjectProperty.ι _).Faithful
    infer_instance
  exact (reedyFibrantCommaEquivalence K Y).trans
    (CostructuredArrow.post fibrantReedyGadgetDiagram OriginalPointed.fibrantGadgetFullInclusion Y.left).asEquivalence

/-- Every same actual full original Reedy-to-fibrant-gadget comma nerve has genuine weak point projection. -/
theorem reedyGadgetCommaNerve_point_weak (K : OriginalPointed.Category.{u})
    (Y : CostructuredArrow OriginalPointed.fibrantGadgetFullInclusion K) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (CostructuredArrow (reedyIntoFibrantGadgetInputs K) Y))) := by
  let e := reedyGadgetCommaEquivalence K Y
  have hf := nerveMapHomDown_mem_realizationWeakEquivalences_of_isEquivalence e.functor
  have hp := plainReedyInputNerve_point_weak Y.left
  have he : nerveMapHomDown e.functor ≫ SSet.stdSimplex.isTerminalObj₀.from
      (nerve (CostructuredArrow plainReedyDiagram Y.left.obj.obj)) =
      SSet.stdSimplex.isTerminalObj₀.from (nerve (CostructuredArrow (reedyIntoFibrantGadgetInputs K) Y)) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact he ▸ SSet.realizationWeakEquivalences.comp_mem _ _ hf hp

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
