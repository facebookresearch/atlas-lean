/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Sharp maps for an original morphism property

Rezk's sharpness condition retains every base change and every weak map
of objects over the base. It is the native universal closure of stability
along a map, rather than stability along just the original base map.
The full native pullback functor on over categories is retained.
-/

noncomputable section
universe v u
open CategoryTheory Limits

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

/-- Maps all of whose original base changes preserve `W` by pullback. -/
def sharpMaps : MorphismProperty C :=
  universally (fun (_ _ : C) p => W.IsStableUnderBaseChangeAlong p)

/-- Sharp maps retain the native universal base-change stability. -/
instance sharpMaps_isStableUnderBaseChange : (sharpMaps W).IsStableUnderBaseChange :=
  universally_isStableUnderBaseChange _

/-- Sharpness retains the native invariance under original arrow isomorphisms. -/
instance sharpMaps_respectsIso : (sharpMaps W).RespectsIso := universally_respectsIso _

/-- Composing two sharp original maps preserves their full base-change condition. -/
instance sharpMaps_isStableUnderComposition [HasPullbacks C] :
    (sharpMaps W).IsStableUnderComposition := by
  let P : MorphismProperty C := fun _ _ p => W.IsStableUnderBaseChangeAlong p
  let _ : P.IsStableUnderComposition := ⟨fun f g hf hg => by
    let _ : W.IsStableUnderBaseChangeAlong f := hf
    let _ : W.IsStableUnderBaseChangeAlong g := hg
    exact inferInstanceAs (W.IsStableUnderBaseChangeAlong (f ≫ g))⟩
  exact inferInstanceAs P.universally.IsStableUnderComposition

/-- The SAME full map of native original pullbacks is itself a pullback square. -/
theorem overPullbackMap_isPullback [HasPullbacks C] {E B : C} (p : E ⟶ B)
    {X Y : Over B} (g : X ⟶ Y) :
    IsPullback ((Over.pullback p).map g).left (pullback.fst X.hom p)
      (pullback.fst Y.hom p) g.left := by
  have source : IsPullback (pullback.snd X.hom p) (pullback.fst X.hom p)
      p (g.left ≫ Y.hom) := by
    rw [g.w]
    exact (IsPullback.of_hasPullback X.hom p).flip
  have outer : IsPullback
      (((Over.pullback p).map g).left ≫ pullback.snd Y.hom p)
      (pullback.fst X.hom p) p (g.left ≫ Y.hom) := by
    simpa only [Over.pullback_map_left, pullback.lift_snd] using source
  exact outer.of_right
    (by simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback Y.hom p).flip

/-- Every sharp original map preserves all original `W` arrows through the
literal native over-pullback functor, including their full projections. -/
theorem sharpMaps_pullback_map [HasPullbacks C] {E B : C} {p : E ⟶ B}
    (hp : sharpMaps W p) {X Y : Over B} (g : X ⟶ Y) (hg : W g.left) :
    W ((Over.pullback p).map g).left := by
  have hY : W.IsStableUnderBaseChangeAlong (pullback.fst Y.hom p) :=
    hp (pullback.snd Y.hom p) Y.hom (pullback.fst Y.hom p)
      (IsPullback.of_hasPullback Y.hom p)
  exact hY.of_isPullback (overPullbackMap_isPullback p g).flip hg

end CategoryTheory.MorphismProperty
