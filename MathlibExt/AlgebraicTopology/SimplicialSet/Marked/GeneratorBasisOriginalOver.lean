/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.GeneratorBasisOver

/-!
# The marked basis colimit with its original slice object as point

The entire original marked basis diagram has its actual original slice
object as cocone point. Its legs are the unchanged whole marked maps,
and native slice colimit reflection reuses the proved total-space
density. No replacement or point-isomorphism choice is needed.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SSet.Marked.GeneratorBasis

/-- The original marked basis cocone retains the actual original slice object and every whole leg. -/
def originalOverCocone {Z : Marked.{u}} (X : Over Z) : Cocone (overDiagram X) where
  pt := X
  ι :=
    { app i := Over.homMk i.hom rfl
      naturality i j f := by
        apply Over.OverMorphism.ext
        exact (CostructuredArrow.w f).trans (Category.comp_id i.hom).symm }

/-- The actual original slice object is the genuine colimit of its complete original marked basis. -/
def originalOverIsColimit {Z : Marked.{u}} (X : Over Z) : IsColimit (originalOverCocone X) :=
  isColimitOfReflects (Over.forget Z) (isColimit X.left)

end SSet.Marked.GeneratorBasis
