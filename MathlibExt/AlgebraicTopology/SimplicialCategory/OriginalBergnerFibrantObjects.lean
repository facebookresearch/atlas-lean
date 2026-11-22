/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerTerminalPoint
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Actual original Bergner fibrancy is precisely full local Kan fibrancy

The same original terminal point map has exactly the full scalar maps
to the tensor unit and genuine component isomorphism lifting. Terminal
transport in the original model proves the complete fibrancy
recognition, including empty original object types.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.Bergner
attribute [local instance] modelCategory

private theorem toUnit_fibration_iff (X : SSet.{u}) :
    Fibration (CodiscreteEnrichment.toUnit X) ↔ SSet.KanComplex X :=
  (isFibrant_iff_of_isTerminal (CodiscreteEnrichment.toUnit X)
    (CartesianMonoidalCategory.isTerminalTensorUnit : IsTerminal (𝟙_ SSet.{u}))).symm

/-- The full original point map is a genuine Bergner fibration exactly when all same original Homs are Kan. -/
theorem toPoint_fibration_iff (C : Carrier.{u}) :
    Fibration (toPoint C) ↔ ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y) := by
  constructor
  · intro h x y
    have h' : localFibrations (toPoint C) := (fibration_iff_original (toPoint C)).mp h
    exact (toUnit_fibration_iff _).mp (h'.1 x y)
  · intro h
    exact (fibration_iff_original (toPoint C)).mpr
      ⟨fun x y => (toUnit_fibration_iff _).mpr (h x y), toPoint_component_isIsofibration C⟩

/-- The actual original global Bergner fibrant objects are precisely the SAME full locally Kan enrichments. -/
theorem isFibrant_iff_original_homKan (C : Carrier.{u}) :
    IsFibrant C ↔ ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y) :=
  (isFibrant_iff_of_isTerminal (toPoint C) pointIsTerminal).trans (toPoint_fibration_iff C)

/-- Every genuine original global-model fibrant object retains Kan fibrancy of each same complete original Hom. -/
theorem homKan_of_isFibrant (C : Carrier.{u}) [IsFibrant C] (x y : C) :
    SSet.KanComplex (x ⟶[SSet.{u}] y) :=
  (isFibrant_iff_original_homKan C).mp inferInstance x y

/-- Genuine full local Kan fibrancy supplies actual fibrancy in the SAME original global model. -/
theorem isFibrant_of_original_homKan (C : Carrier.{u})
    (h : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) : IsFibrant C :=
  (isFibrant_iff_original_homKan C).mpr h

end CategoryTheory.SimplicialEnrichment.Bergner
