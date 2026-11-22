/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceGadgetCommaEquivalence
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceInputNervePoint
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedBoundaryReadback
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveIndependentHomEquivalenceWeak

/-!
# Genuine original native gadget comma point weakness

The actual native comma category is the same entire original native
input category over the supplied gadget's full carrier. Its SAME raw
Hom point property and the proved original hocolim weak span supply
point weakness. All original objects, arrows and input maps are retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceInput

/-- The same full original pointed native input nerve is weakly contractible at every actual original gadget. -/
theorem pointedNativeInputNerve_point_weak (X : OriginalPointed.MappingGadgets.{u}) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (CostructuredArrow pointedNativeFunctor X.obj))) := by
  let K := X.obj.right
  let x := OriginalPointed.sourceVertex X.obj
  let y := OriginalPointed.targetVertex X.obj
  let e := pointedInputEquivalence K x y
  have hobj : Under.mk (SSet.boundaryOneMap x y) = X.obj := by
    apply StructuredArrow.obj_ext (T := 𝟭 SSet.{u}) (Under.mk (SSet.boundaryOneMap x y)) X.obj rfl
    change SSet.boundaryOneMap x y ≫ 𝟙 K = X.obj.hom
    exact (Category.comp_id _).trans (OriginalPointed.hom_eq_boundaryOneMap X.obj).symm
  have hf := nerveMapHomDown_mem_realizationWeakEquivalences_of_isEquivalence e.functor
  have hp := inputNerve_point_weak K x y X.property.1
  have he : nerveMapHomDown e.functor ≫ SSet.stdSimplex.isTerminalObj₀.from
      (nerve (CostructuredArrow pointedNativeFunctor (Under.mk (SSet.boundaryOneMap x y)))) =
      SSet.stdSimplex.isTerminalObj₀.from (nerve (Object K x y)) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have h := SSet.realizationWeakEquivalences.of_precomp (nerveMapHomDown e.functor) _ hf (he.symm ▸ hp)
  exact Eq.mp (congrArg (fun Z : OriginalPointed.Category.{u} => SSet.realizationWeakEquivalences
    (SSet.stdSimplex.isTerminalObj₀.from (nerve (CostructuredArrow pointedNativeFunctor Z)))) hobj) h

/-- Every same actual full original native gadget comma nerve has a genuinely weak point projection. -/
theorem nativeGadgetCommaNerve_point_weak (K : OriginalPointed.Category.{u})
    (Y : CostructuredArrow OriginalPointed.gadgetInclusion K) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (CostructuredArrow (nativeGadgetInputs K) Y))) := by
  let e := nativeGadgetCommaEquivalence K Y
  have hf := nerveMapHomDown_mem_realizationWeakEquivalences_of_isEquivalence e.functor
  have hp := pointedNativeInputNerve_point_weak Y.left
  have he : nerveMapHomDown e.functor ≫ SSet.stdSimplex.isTerminalObj₀.from
      (nerve (CostructuredArrow pointedNativeFunctor Y.left.obj)) =
      SSet.stdSimplex.isTerminalObj₀.from (nerve (CostructuredArrow (nativeGadgetInputs K) Y)) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact he ▸ SSet.realizationWeakEquivalences.comp_mem _ _ hf hp

end CategoryTheory.CoherentRealization.OriginalNecklaceInput
