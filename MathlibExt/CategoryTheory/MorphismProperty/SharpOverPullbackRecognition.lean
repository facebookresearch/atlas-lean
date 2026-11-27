/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.MorphismProperty.SharpMaps

/-!
# Full native over-pullback preservation detects sharpness

All original base changes and all `W` arrows between objects over the
base are retained. The converse uses the actual pullback pasting square
and both native comparison Isos. No model structure is assumed.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  (W : MorphismProperty C) [W.RespectsIso]

/-- The SAME native over-pullback preserves all original `W` arrows precisely
when the original map is fully sharp. Object and Hom universes are independent. -/
theorem sharpMaps_iff_overPullback {E B : C} (p : E ⟶ B) :
    sharpMaps W p ↔ ∀ {V T : Over B} (f : V ⟶ T), W f.left → W ((Over.pullback p).map f).left := by
  constructor
  · exact fun hp _ _ f hf => sharpMaps_pullback_map W hp f hf
  · intro preserves P A e b a sq
    constructor
    intro A' P' a' k g square hg
    let f : CategoryTheory.Over.mk (g ≫ b) ⟶ CategoryTheory.Over.mk b :=
      CategoryTheory.Over.homMk g (by rfl)
    let m := ((Over.pullback p).map f).left
    have m_fst : m ≫ pullback.fst b p = pullback.fst (g ≫ b) p ≫ g := pullback.lift_fst _ _ _
    have m_snd : m ≫ pullback.snd b p = pullback.snd (g ≫ b) p := pullback.lift_snd _ _ _
    have outer := square.paste_vert sq
    let eP : P' ≅ pullback (g ≫ b) p := outer.isoPullback
    let eQ : P ≅ pullback b p := sq.isoPullback
    have comm : eP.hom ≫ m = k ≫ eQ.hom := by
      apply pullback.hom_ext
      · change (eP.hom ≫ m) ≫ pullback.fst b p = (k ≫ eQ.hom) ≫ pullback.fst b p
        rw [Category.assoc, m_fst, ← Category.assoc, outer.isoPullback_hom_fst,
          Category.assoc, sq.isoPullback_hom_fst]
        exact square.w
      · change (eP.hom ≫ m) ≫ pullback.snd b p = (k ≫ eQ.hom) ≫ pullback.snd b p
        rw [Category.assoc, m_snd, outer.isoPullback_hom_snd,
          Category.assoc, sq.isoPullback_hom_snd]
    let eArrow : CategoryTheory.Arrow.mk k ≅ CategoryTheory.Arrow.mk m :=
      CategoryTheory.Arrow.isoMk eP eQ comm
    exact (W.arrow_mk_iso_iff eArrow).mpr (preserves f hg)

end CategoryTheory.MorphismProperty
