/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Limits.Shapes.Pullback.FibreRestriction
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Actual changing-base fibre maps through the SAME relative pullback

A supplied commuting square has its literal factor into the base
pullback. The native pullback pasting identifies each factor fibre
with the original changing-base fibre. Both whole projections and
both complete Arrow legs retain the supplied original maps.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite

namespace HomotopicalAlgebra.SharpFibreMapWeak
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {E E' B B' A : C}

/-- The SAME full original total/base square factors into its native target-projection pullback. -/
def toBasePullback (p : E ⟶ B) (q : E' ⟶ B') (f : E ⟶ E') (g : B ⟶ B')
    (h : f ≫ q = p ≫ g) : E ⟶ pullback q g := pullback.lift f p h

/-- The native original fibre map retains all original total, point and base maps. -/
abbrev fibreMap (p : E ⟶ B) (q : E' ⟶ B') (f : E ⟶ E') (g : B ⟶ B')
    (h : f ≫ q = p ≫ g) (a : A ⟶ B) : pullback p a ⟶ pullback q (a ≫ g) :=
  fibreRestriction f p q g h a (a ≫ g) rfl

end HomotopicalAlgebra.SharpFibreMapWeak

namespace CategoryTheory.Limits.PullbackFibreBaseChange
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {E E' B B' T : C}
open HomotopicalAlgebra.SharpFibreMapWeak

/-- The entire original total map is retained by the relative factor's first projection. -/
@[reassoc] theorem factor_fst (e : E ⟶ E') (p : E ⟶ B) (p' : E' ⟶ B') (b : B ⟶ B')
    (h : p ≫ b = e ≫ p') : toBasePullback p p' e b h.symm ≫ pullback.fst p' b = e :=
      pullback.lift_fst _ _ _

/-- The entire original source projection is retained by the relative factor's second projection. -/
@[reassoc] theorem factor_snd (e : E ⟶ E') (p : E ⟶ B) (p' : E' ⟶ B') (b : B ⟶ B')
    (h : p ≫ b = e ≫ p') : toBasePullback p p' e b h.symm ≫ pullback.snd p' b = p :=
      pullback.lift_snd _ _ _

/-- The actual nested point pullback has the SAME original changing-base pullback universal
property. -/
theorem point_isPullback (p' : E' ⟶ B') (b : B ⟶ B') (a : T ⟶ B) :
    IsPullback (pullback.fst (pullback.snd p' b) a ≫ pullback.fst p' b)
      (pullback.snd (pullback.snd p' b) a) p' (a ≫ b) :=
  (IsPullback.of_hasPullback (pullback.snd p' b) a).paste_horiz (IsPullback.of_hasPullback p' b)

/-- The native nested fibre is genuinely isomorphic to the SAME original changing-base fibre. -/
def pointIso (p' : E' ⟶ B') (b : B ⟶ B') (a : T ⟶ B) :
    pullback (pullback.snd p' b) a ≅ pullback p' (a ≫ b) :=
  pullbackLeftPullbackSndIso p' b a

/-- The entire point-pasting comparison retains both original total-space projections. -/
@[reassoc] theorem pointIso_fst (p' : E' ⟶ B') (b : B ⟶ B') (a : T ⟶ B) :
    (pointIso p' b a).hom ≫ pullback.fst p' (a ≫ b) =
      pullback.fst (pullback.snd p' b) a ≫ pullback.fst p' b :=
  pullbackLeftPullbackSndIso_hom_fst p' b a

/-- The entire point-pasting comparison retains the SAME original source-point projection. -/
@[reassoc] theorem pointIso_snd (p' : E' ⟶ B') (b : B ⟶ B') (a : T ⟶ B) :
    (pointIso p' b a).hom ≫ pullback.snd p' (a ≫ b) = pullback.snd (pullback.snd p' b) a :=
  pullbackLeftPullbackSndIso_hom_snd p' b a

/-- The SAME relative factor gives its entire original same-base fibre map. -/
def factorFibreMap (e : E ⟶ E') (p : E ⟶ B) (p' : E' ⟶ B') (b : B ⟶ B')
    (h : p ≫ b = e ≫ p') (a : T ⟶ B) :
    pullback p a ⟶ pullback (pullback.snd p' b) a :=
  pullback.map p a (pullback.snd p' b) a (toBasePullback p p' e b h.symm) (𝟙 T) (𝟙 B)
    ((Category.comp_id _).trans (factor_snd e p p' b h).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The whole same-base factor fibre map retains the SAME original relative total projection. -/
@[reassoc] theorem factorFibreMap_fst (e : E ⟶ E') (p : E ⟶ B) (p' : E' ⟶ B') (b : B ⟶ B')
    (h : p ≫ b = e ≫ p') (a : T ⟶ B) :
    factorFibreMap e p p' b h a ≫ pullback.fst (pullback.snd p' b) a =
      pullback.fst p a ≫ toBasePullback p p' e b h.symm := pullback.lift_fst _ _ _

/-- The whole same-base factor fibre map keeps the SAME original point projection. -/
@[reassoc] theorem factorFibreMap_snd (e : E ⟶ E') (p : E ⟶ B) (p' : E' ⟶ B') (b : B ⟶ B')
    (h : p ≫ b = e ≫ p') (a : T ⟶ B) :
    factorFibreMap e p p' b h a ≫ pullback.snd (pullback.snd p' b) a = pullback.snd p a :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The SAME actual changing-base fibre map reads the original total-space projection. -/
@[reassoc] theorem fibreMap_fst (e : E ⟶ E') (p : E ⟶ B) (p' : E' ⟶ B') (b : B ⟶ B')
    (h : p ≫ b = e ≫ p') (a : T ⟶ B) :
    fibreMap p p' e b h.symm a ≫ pullback.fst p' (a ≫ b) = pullback.fst p a ≫ e :=
  fibreRestriction_fst e p p' b h.symm a (a ≫ b) rfl

/-- The SAME actual changing-base fibre map reads the original source-point projection. -/
@[reassoc] theorem fibreMap_snd (e : E ⟶ E') (p : E ⟶ B) (p' : E' ⟶ B') (b : B ⟶ B')
    (h : p ≫ b = e ≫ p') (a : T ⟶ B) :
    fibreMap p p' e b h.symm a ≫ pullback.snd p' (a ≫ b) = pullback.snd p a :=
  fibreRestriction_snd e p p' b h.symm a (a ≫ b) rfl

/-- Both entire factor-fibre and original fibre maps agree through the SAME native
pullback-pasting comparison. -/
@[reassoc] theorem factorFibreMap_comparison
    (e : E ⟶ E') (p : E ⟶ B) (p' : E' ⟶ B') (b : B ⟶ B')
    (h : p ≫ b = e ≫ p') (a : T ⟶ B) :
    factorFibreMap e p p' b h a ≫ (pointIso p' b a).hom = fibreMap p p' e b h.symm a := by
  apply pullback.hom_ext
  · rw [Category.assoc, pointIso_fst p' b a, ← Category.assoc,
      factorFibreMap_fst e p p' b h a, Category.assoc, factor_fst e p p' b h,
      fibreMap_fst e p p' b h a]
  · rw [Category.assoc, pointIso_snd p' b a, factorFibreMap_snd e p p' b h a,
      fibreMap_snd e p p' b h a]

/-- Both complete original fibre-map Arrows retain their SAME source and original
changing-base target. -/
def factorFibreArrowIso (e : E ⟶ E') (p : E ⟶ B) (p' : E' ⟶ B') (b : B ⟶ B')
    (h : p ≫ b = e ≫ p') (a : T ⟶ B) :
    Arrow.mk (factorFibreMap e p p' b h a) ≅ Arrow.mk (fibreMap p p' e b h.symm a) :=
  Arrow.isoMk (Iso.refl _) (pointIso p' b a)
    ((Category.id_comp _).trans (factorFibreMap_comparison e p p' b h a).symm)

end CategoryTheory.Limits.PullbackFibreBaseChange
