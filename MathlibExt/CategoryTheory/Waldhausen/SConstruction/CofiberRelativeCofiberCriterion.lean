/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeEvaluation

/-!
# Joint cofiber reflection with the genuine relative corner

A whole pair of cofiber-row morphisms is a cofiber sequence for the
original relative Waldhausen value precisely when its first morphism
has the genuine relative corner and each original evaluation is a
cofiber sequence. The original zero row is retained in the pushout
reflection, including its three independently evaluated zero objects.
-/

public section

open CategoryTheory Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

private theorem isPushoutOfCofiberAtZero {X Y Z O : C} {i : X ⟶ Y} {p : Y ⟶ Z}
    (h : IsCofiberSequence i p) (hO : IsZero O) (z : X ⟶ O) (q : O ⟶ Z) :
    IsPushout z i q p := by
  obtain ⟨_, z₀, q₀, hPushout⟩ := h
  let e : (0 : C) ≅ O := hO.isoZero.symm
  apply hPushout.of_iso (Iso.refl X) e (Iso.refl Y) (Iso.refl Z)
  · simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id] using
      (hO.eq_of_tgt (z₀ ≫ e.hom) z)
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id] using
      ((isZero_zero C).eq_of_src q₀ (e.hom ≫ q))
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The original three evaluated cofiber sequences jointly reflect the
whole relative cofiber sequence when the genuine first relative corner is retained. -/
theorem isCofiberSequence_relative_iff_evaluations
    {X Y Z : CofiberSequenceCategory C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      IsCofiberSequence f g) ↔
        relativeCofibrations C f ∧
          ∀ k : Fin 3, IsCofiberSequence
            (((forget C) ⋙ (evaluation (Fin 3) C).obj k).map f)
            (((forget C) ⋙ (evaluation (Fin 3) C).obj k).map g) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  constructor
  · intro h
    refine ⟨(isCofibration_relativeWaldhausenCategory_iff C f).mp h.1, ?_⟩
    intro k
    exact (evaluationIsRelativeWaldhausenExact C k).map_cofibrationSequence h
  · rintro ⟨hf, hRows⟩
    let O : CofiberSequenceCategory C := 0
    let z : X ⟶ O := (isZero_zero (CofiberSequenceCategory C)).from_ X
    let q : O ⟶ Z := (isZero_zero (CofiberSequenceCategory C)).to_ Z
    refine ⟨(isCofibration_relativeWaldhausenCategory_iff C f).mpr hf, z, q, ?_⟩
    apply IsPushout.of_map_of_faithful (forget C)
    apply IsPushout.of_forall_isPushout_app
    intro k
    let E := (forget C) ⋙ (evaluation (Fin 3) C).obj k
    have hO : IsZero (E.obj O) :=
      (evaluationIsRelativeWaldhausenExact C k).map_isZero
        (isZero_zero (CofiberSequenceCategory C))
    change IsPushout (E.map z) (E.map f) (E.map q) (E.map g)
    exact isPushoutOfCofiberAtZero C (hRows k) hO (E.map z) (E.map q)

end CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory
