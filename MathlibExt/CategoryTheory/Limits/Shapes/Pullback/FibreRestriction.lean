/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Restriction between fibres is a base change of the square comparison

A map between the actual pullbacks at compatible base maps is a base
change of the original map to the square pullback. The construction uses
the original pullback objects, projections, and base map, with independent
object and morphism universes.
-/

noncomputable section
universe v u
open CategoryTheory Limits

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
    {D A BD BA T : C}
    (f : D ⟶ A) (pD : D ⟶ BD) (pA : A ⟶ BA) (g : BD ⟶ BA)
    (h : f ≫ pA = pD ≫ g) (r : T ⟶ BD) (rA : T ⟶ BA)
    (hr : r ≫ g = rA)

/-- The original square comparison restricts to the same compatible fibres. -/
def fibreRestriction : pullback pD r ⟶ pullback pA rA :=
  pullback.map pD r pA rA f (𝟙 T) g h.symm (by simpa using hr)

/-- The restriction keeps the original total-space coordinate. -/
@[reassoc (attr := simp)]
theorem fibreRestriction_fst :
    fibreRestriction f pD pA g h r rA hr ≫ pullback.fst pA rA =
      pullback.fst pD r ≫ f := by
  exact pullback.lift_fst ..

/-- The restriction keeps the original parameter coordinate. -/
@[reassoc (attr := simp)]
theorem fibreRestriction_snd :
    fibreRestriction f pD pA g h r rA hr ≫ pullback.snd pA rA = pullback.snd pD r := by
  simp only [fibreRestriction, pullback.map, pullback.lift_snd, Category.comp_id]

variable {P : C} {a : P ⟶ A} {b : P ⟶ BD}
    (sq : IsPullback a b pA g) (d : D ⟶ P)
    (hdA : d ≫ a = f) (hdB : d ≫ b = pD)

/-- The fibre maps into the original square pullback using its two original coordinates. -/
def fibreToSquare : pullback pA rA ⟶ P :=
  sq.lift (pullback.fst pA rA) (pullback.snd pA rA ≫ r)
    (by rw [pullback.condition, Category.assoc, hr])

include hdA hdB in
/-- The actual map of fibres is the base change of the original square comparison. -/
theorem fibreRestriction_isPullback :
    IsPullback (pullback.fst pD r) (fibreRestriction f pD pA g h r rA hr)
      d (fibreToSquare pA g r rA hr sq) := by
  have hs : IsPullback (fibreToSquare pA g r rA hr sq) (pullback.snd pA rA) b r :=
    IsPullback.of_right' (by rw [hr]; exact IsPullback.of_hasPullback pA rA) sq
  have hw : pullback.fst pD r ≫ d =
      fibreRestriction f pD pA g h r rA hr ≫ fibreToSquare pA g r rA hr sq := by
    apply sq.hom_ext
    · rw [Category.assoc, hdA, Category.assoc, fibreToSquare, IsPullback.lift_fst,
        fibreRestriction_fst]
    · rw [Category.assoc, hdB, Category.assoc, fibreToSquare, IsPullback.lift_snd,
        ← Category.assoc, fibreRestriction_snd, pullback.condition]
  have ho : IsPullback (pullback.fst pD r)
      (fibreRestriction f pD pA g h r rA hr ≫ pullback.snd pA rA) (d ≫ b) r := by
    rw [fibreRestriction_snd, hdB]
    exact IsPullback.of_hasPullback pD r
  exact ho.of_bot hw hs

end CategoryTheory.Limits
