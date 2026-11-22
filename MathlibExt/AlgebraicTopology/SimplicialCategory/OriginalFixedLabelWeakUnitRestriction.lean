/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabelPushforwardQuillen
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectCodiscreteTerminal

/-!
# The SAME full original weak-unit property survives every original label restriction

Every complete original Hom is literally the source Hom at its actual
image labels. Both original unit maps are the SAME whole coefficient
map to the scalar unit, so no fibrancy or cofibrancy is required.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.LabelRestriction

/-- Every actual original restricted unit map is weak from the SAME source's original full weak-unit maps. -/
theorem toTerminal_weak {A O : Type u} (a : A → O) (C : FixedObjects O)
    (hC : FixedObjectModel.weakEquivalences O (CodiscreteTerminal.toTerminal C)) :
    FixedObjectModel.weakEquivalences A (CodiscreteTerminal.toTerminal (object a C)) := by
  apply (FixedObjectModel.weakEquivalences_iff _).mpr
  intro s t
  have h := (FixedObjectModel.weakEquivalences_iff _).mp hC (a s) (a t)
  have h₀ : SSet.realizationWeakEquivalences (CodiscreteEnrichment.toUnit (hom C (a s) (a t))) :=
    (congrArg (fun f : hom C (a s) (a t) ⟶ 𝟙_ SSet.{u} => SSet.realizationWeakEquivalences f)
      (CodiscreteTerminal.toTerminal_homMap C (a s) (a t))).mp h
  exact (congrArg (fun f : hom (object a C) s t ⟶ 𝟙_ SSet.{u} => SSet.realizationWeakEquivalences f)
    (CodiscreteTerminal.toTerminal_homMap (object a C) s t)).mpr h₀

end CategoryTheory.SimplicialEnrichment.FixedObjects.LabelRestriction
