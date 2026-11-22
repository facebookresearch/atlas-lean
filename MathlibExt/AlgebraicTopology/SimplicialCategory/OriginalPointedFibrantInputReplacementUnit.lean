/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedGadgetInputs

/-!
# The same original second full input replacement unit

The actual canonical original replacement unit and target retraction
retain the entire input triangle on genuinely fibrant original gadget
inputs. This is the second full natural comparison required for the
original nerve equivalence; every original map is kept.
-/

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.CoherentRealization.OriginalPointed

/-- The same full original unit on the genuine fibrant input composite retains every exact original pointed input
triangle. -/
def fibrantGadgetInputReplacementUnit (K : Category.{u}) (r : replacementFunctor.obj K ⟶ K)
    (hr : replacementUnit.app K ≫ r = 𝟙 K) :
    𝟭 (CostructuredArrow fibrantGadgetFullInclusion K) ⟶ fibrantInputInclusion K ⋙ gadgetInputReplacement K r where
  app X := CostructuredArrow.homMk (fibrantGadgetReplacementUnit.app X.left) (by
    change replacementUnit.app X.left.obj.obj ≫ (replacementFunctor.map X.hom ≫ r) = X.hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ r) (replacementUnit.naturality X.hom).symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun f => X.hom ≫ f) hr).trans (Category.comp_id _)))))
  naturality X Y f := by
    apply CostructuredArrow.hom_ext
    exact fibrantGadgetReplacementUnit.naturality f.left

end CategoryTheory.CoherentRealization.OriginalPointed
