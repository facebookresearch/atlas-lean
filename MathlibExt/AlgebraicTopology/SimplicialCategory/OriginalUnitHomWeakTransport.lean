/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CodiscreteEnrichment
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence

/-!
# The actual original unit projection through full weak Hom maps

The SAME full scalar map has its literal unit projection. The terminal
coefficient map commutes with that original map in every degree. Actual
two out of three transports weakness of the unit projection in either
direction, without a fibrancy or assumed contractibility premise.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.CodiscreteEnrichment

/-- The entire original Hom map retains its literal map to the unit in every degree. -/
@[reassoc]
theorem toUnit_comp {X Y : SSet.{u}} (f : X ⟶ Y) :
    f ≫ toUnit Y = toUnit X := by
  ext q a
  change PUnit.unit = PUnit.unit
  rfl

/-- A genuine weak original full Hom map detects weakness of the SAME unit projections. -/
theorem toUnit_weak_iff {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : SSet.realizationWeakEquivalences f) :
    SSet.realizationWeakEquivalences (toUnit X) ↔
      SSet.realizationWeakEquivalences (toUnit Y) := by
  constructor
  · intro h
    exact SSet.realizationWeakEquivalences.of_precomp f (toUnit Y) hf
      ((congrArg (fun g : X ⟶ 𝟙_ SSet.{u} => SSet.realizationWeakEquivalences g)
        (toUnit_comp f)).mpr h)
  · intro h
    have hc := SSet.realizationWeakEquivalences.comp_mem f (toUnit Y) hf h
    exact (congrArg (fun g : X ⟶ 𝟙_ SSet.{u} => SSet.realizationWeakEquivalences g)
      (toUnit_comp f)).mp hc

end CategoryTheory.SimplicialEnrichment.CodiscreteEnrichment
