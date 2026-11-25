/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Enriched.HomCongr

/-!
# Congruence of enriched identities

This file complements Mathlib's enriched-hom congruence isomorphism with its compatibility with
enriched identity morphisms.
-/

@[expose] public section

namespace CategoryTheory.Iso

open CategoryTheory Category

universe uV vV uC vC

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V]
variable {C : Type uC} [Category.{vC} C] [EnrichedOrdinaryCategory V C]
variable {X Y : C}

/-- Transporting an enriched identity along the same isomorphism in source and target gives the
enriched identity of the target. -/
@[reassoc]
theorem eId_comp_eHomCongr (e : X ≅ Y) :
    eId V X ≫ (Iso.eHomCongr V e e).hom = eId V Y := by
  change eId V X ≫
      (eHomWhiskerRight V e.inv X ≫ eHomWhiskerLeft V Y e.hom) =
    eId V Y
  rw [← Category.assoc, eId_comp_eHomWhiskerRight,
    eHomEquiv_comp_eHomWhiskerLeft, e.inv_hom_id, eHomEquiv_id]

end CategoryTheory.Iso
