/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakFiniteProducts

/-!
# Tensor forms of realization weak product preservation

These adapters use the existing finite-product weak preservation theorem
and its native tensor-to-product comparison. All coefficients remain
arbitrary; no Kan or finiteness premise is required.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace SSet.realizationWeakEquivalences

/-- Tensoring on the left preserves every realization weak map. -/
theorem whiskerLeft (K : SSet.{u}) {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : SSet.realizationWeakEquivalences f) :
    SSet.realizationWeakEquivalences (K ◁ f) :=
  (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
    (SSet.tensorLeftProductArrowIso K f)).mpr
      (SSet.realizationWeak_prodMap_id_left K f hf)

/-- Tensoring on the right preserves every realization weak map. -/
theorem whiskerRight {X Y : SSet.{u}} (f : X ⟶ Y) (K : SSet.{u})
    (hf : SSet.realizationWeakEquivalences f) :
    SSet.realizationWeakEquivalences (f ▷ K) := by
  have h : SSet.realizationWeakEquivalences (f ▷ K) ↔
      SSet.realizationWeakEquivalences (K ◁ f) :=
    SSet.realizationWeakEquivalences.arrow_mk_iso_iff
      (Arrow.isoMk (β_ X K) (β_ Y K)
        (CategoryTheory.BraidedCategory.braiding_naturality_left f K).symm)
  exact h.mpr (whiskerLeft K f hf)

/-- Tensoring two realization weak maps preserves weakness. -/
theorem tensorHom {X Y A B : SSet.{u}} (f : X ⟶ Y) (g : A ⟶ B)
    (hf : SSet.realizationWeakEquivalences f) (hg : SSet.realizationWeakEquivalences g) :
    SSet.realizationWeakEquivalences (f ⊗ₘ g) := by
  rw [tensorHom_def]
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    (whiskerRight f A hf) (whiskerLeft Y g hg)

end SSet.realizationWeakEquivalences
