/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentNerveQuasicategory
import MathlibExt.AlgebraicTopology.SimplicialCategory.LiftUniverse
import MathlibExt.AlgebraicTopology.SimplicialSet.ULiftKan

/-!
# The actual locally Kan coherent nerve in independent original universes

The existing original carrier lift retains individual objects and whole
Hom simplices. Genuine scalar Kan preservation under universe lifting
therefore gives the coherent quasicategory theorem for independent
original object, Hom and auxiliary common universes.
-/

noncomputable section
universe u v w
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment
variable (C : Type v) [EnrichedCategory SSet.{u} C]

/-- Every actual Hom of the original common-universe carrier lift is Kan when its corresponding original Hom
  is genuinely Kan. -/
theorem liftedCarrier_homKan (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (x y : liftedCarrier.{u, v, w} C) : SSet.KanComplex (x ⟶[SSet.{max u v w}] y) := by
  change SSet.KanComplex (SSet.uliftFunctor.{max v w, u}.obj (x.down ⟶[SSet.{u}] y.down))
  exact @SSet.kanComplex_ulift.{u, max v w} (x.down ⟶[SSet.{u}] y.down) (hKan x.down y.down)

/-- The genuine coherent nerve of the original locally Kan enrichment, with independent object and Hom
  universes and exact individual-object lifting, is a quasicategory. -/
theorem liftedCoherentNerve_quasicategory (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) :
    SSet.Quasicategory (coherentNerveFunctor.obj (liftedCarrier.{u, v, w} C)) :=
  coherentNerve_quasicategory _ (liftedCarrier_homKan C hKan)

end CategoryTheory.SimplicialEnrichment
