/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Limits.Shapes.PullbackFibreBaseChange
import MathlibExt.CategoryTheory.Limits.Shapes.Pullback.FibreRestriction

/-!
# Canonical changing-base fibre restriction at fixed target points

The supplied actual point-square equality identifies the original
composite target point with its prescribed whole point. The existing
generic fibre restriction retains both chosen pullbacks and projections.
The compatibility name is used by the native mapping and weak-map clients;
the Arrow comparison retains their actual target-point transport.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Limits.PullbackFibreBaseChange
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {E E' B B' T : C}
open HomotopicalAlgebra.SharpFibreMapWeak

/-- The actual whole target-point equality gives the SAME genuine chosen pullback transport. -/
def targetPointIso (p' : E' ⟶ B') (a a' : T ⟶ B') (ha : a = a') :
    pullback p' a ≅ pullback p' a' := eqToIso (congrArg (fun v : T ⟶ B' => pullback p' v) ha)

/-- The entire original target-point transport preserves its SAME total-space projection. -/
@[reassoc] theorem targetPointIso_fst (p' : E' ⟶ B') (a a' : T ⟶ B') (ha : a = a') :
    (targetPointIso p' a a' ha).hom ≫ pullback.fst p' a' = pullback.fst p' a := by
  subst a'
  exact Category.id_comp _

/-- The entire original target-point transport preserves its SAME original point projection. -/
@[reassoc] theorem targetPointIso_snd (p' : E' ⟶ B') (a a' : T ⟶ B') (ha : a = a') :
    (targetPointIso p' a a' ha).hom ≫ pullback.snd p' a' = pullback.snd p' a := by
  subst a'
  exact Category.id_comp _

/-- Compatibility name for the canonical restriction to the prescribed target point. -/
abbrev fibreMapTo (e : E ⟶ E') (p : E ⟶ B) (p' : E' ⟶ B') (b : B ⟶ B')
    (h : p ≫ b = e ≫ p') (a : T ⟶ B) (a' : T ⟶ B') (ha : a ≫ b = a') :
    pullback p a ⟶ pullback p' a' :=
  fibreRestriction e p p' b h.symm a a' ha

/-- The whole fixed-target fibre map keeps the SAME original total-space comparison. -/
@[reassoc] theorem fibreMapTo_fst (e : E ⟶ E') (p : E ⟶ B) (p' : E' ⟶ B') (b : B ⟶ B')
    (h : p ≫ b = e ≫ p') (a : T ⟶ B) (a' : T ⟶ B') (ha : a ≫ b = a') :
    fibreMapTo e p p' b h a a' ha ≫ pullback.fst p' a' = pullback.fst p a ≫ e :=
  fibreRestriction_fst e p p' b h.symm a a' ha

/-- The whole fixed-target fibre map keeps the SAME original source-point projection. -/
@[reassoc] theorem fibreMapTo_snd (e : E ⟶ E') (p : E ⟶ B) (p' : E' ⟶ B') (b : B ⟶ B')
    (h : p ≫ b = e ≫ p') (a : T ⟶ B) (a' : T ⟶ B') (ha : a ≫ b = a') :
    fibreMapTo e p p' b h a a' ha ≫ pullback.snd p' a' = pullback.snd p a :=
  fibreRestriction_snd e p p' b h.symm a a' ha

/-- Both full original fibre-map Arrows retain the SAME source and actual fixed-target-point
transport. -/
def fibreMapToArrowIso (e : E ⟶ E') (p : E ⟶ B) (p' : E' ⟶ B') (b : B ⟶ B')
    (h : p ≫ b = e ≫ p') (a : T ⟶ B) (a' : T ⟶ B') (ha : a ≫ b = a') :
    Arrow.mk (fibreMap p p' e b h.symm a) ≅ Arrow.mk (fibreMapTo e p p' b h a a' ha) :=
  Arrow.isoMk (Iso.refl _) (targetPointIso p' (a ≫ b) a' ha) (by
    change 𝟙 _ ≫ fibreMapTo e p p' b h a a' ha =
      fibreMap p p' e b h.symm a ≫ (targetPointIso p' (a ≫ b) a' ha).hom
    rw [Category.id_comp]
    apply pullback.hom_ext
    · rw [fibreMapTo_fst e p p' b h a a' ha, Category.assoc,
        targetPointIso_fst p' (a ≫ b) a' ha, fibreMap_fst e p p' b h a]
    · rw [fibreMapTo_snd e p p' b h a a' ha, Category.assoc,
        targetPointIso_snd p' (a ≫ b) a' ha, fibreMap_snd e p p' b h a])

end CategoryTheory.Limits.PullbackFibreBaseChange
