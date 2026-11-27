/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Total preimages of simplicial pushouts

Pulling the four objects of a simplicial pushout back from its apex along an
arbitrary map gives another pushout when the second input leg is mono.  The
construction uses only canonical pullbacks and presheaf adhesivity.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SSet.PreimagePushout

variable {A B₀ D B₁ E : SSet.{u}}
  {t : A ⟶ B₀} {i : A ⟶ D} {r : B₀ ⟶ B₁} {b : D ⟶ B₁}

/-- Canonical map from the total over the common boundary to the total over
the old base. -/
noncomputable def boundaryToOld (p : E ⟶ B₁) :
    pullback p (t ≫ r) ⟶ pullback p r :=
  (IsPullback.of_hasPullback p r).lift
    (pullback.fst p (t ≫ r))
    (pullback.snd p (t ≫ r) ≫ t)
    (by simpa only [Category.assoc] using
      pullback.condition (f := p) (g := t ≫ r))

/-- Canonical map from the total over the common boundary to the total over
the attached cell. -/
noncomputable def boundaryToCell (sq : IsPushout t i r b) (p : E ⟶ B₁) :
    pullback p (t ≫ r) ⟶ pullback p b :=
  (IsPullback.of_hasPullback p b).lift
    (pullback.fst p (t ≫ r))
    (pullback.snd p (t ≫ r) ≫ i)
    (by
      calc
        pullback.fst p (t ≫ r) ≫ p =
            pullback.snd p (t ≫ r) ≫ (t ≫ r) := pullback.condition
        _ = pullback.snd p (t ≫ r) ≫ (i ≫ b) :=
          congrArg (pullback.snd p (t ≫ r) ≫ ·) sq.w
        _ = (pullback.snd p (t ≫ r) ≫ i) ≫ b :=
          (Category.assoc _ _ _).symm)

@[reassoc (attr := simp)]
theorem boundaryToOld_fst (p : E ⟶ B₁) :
    boundaryToOld p ≫ pullback.fst p r = pullback.fst p (t ≫ r) :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
theorem boundaryToOld_snd (p : E ⟶ B₁) :
    boundaryToOld p ≫ pullback.snd p r = pullback.snd p (t ≫ r) ≫ t :=
  IsPullback.lift_snd _ _ _ _

@[reassoc (attr := simp)]
theorem boundaryToCell_fst (sq : IsPushout t i r b) (p : E ⟶ B₁) :
    boundaryToCell sq p ≫ pullback.fst p b = pullback.fst p (t ≫ r) :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
theorem boundaryToCell_snd (sq : IsPushout t i r b) (p : E ⟶ B₁) :
    boundaryToCell sq p ≫ pullback.snd p b = pullback.snd p (t ≫ r) ≫ i :=
  IsPullback.lift_snd _ _ _ _

/-- The canonical boundary-to-old square is a pullback. -/
theorem boundaryToOld_isPullback (p : E ⟶ B₁) :
    IsPullback (boundaryToOld p) (pullback.snd p (t ≫ r))
      (pullback.snd p r) t := by
  simpa only [boundaryToOld] using
    IsPullback.of_right' (IsPullback.of_hasPullback p (t ≫ r))
      (IsPullback.of_hasPullback p r)

/-- The canonical boundary-to-cell square is a pullback. -/
theorem boundaryToCell_isPullback (sq : IsPushout t i r b)
    (p : E ⟶ B₁) :
    IsPullback (boundaryToCell sq p) (pullback.snd p (t ≫ r))
      (pullback.snd p b) i := by
  have outer : IsPullback (pullback.fst p (t ≫ r))
      (pullback.snd p (t ≫ r)) p (i ≫ b) := by
    simpa only [sq.w] using IsPullback.of_hasPullback p (t ≫ r)
  simpa only [boundaryToCell] using
    IsPullback.of_right' outer (IsPullback.of_hasPullback p b)

/-- The canonical total-preimage square over a pushout is a pushout. -/
theorem isPushout (sq : IsPushout t i r b) [Mono i] (p : E ⟶ B₁) :
    IsPushout (boundaryToOld p) (boundaryToCell sq p)
      (pullback.fst p r) (pullback.fst p b) := by
  let oldSq : IsPullback (pullback.fst p r) (pullback.snd p r) p r :=
    IsPullback.of_hasPullback p r
  let cellSq : IsPullback (pullback.fst p b) (pullback.snd p b) p b :=
    IsPullback.of_hasPullback p b
  have topComm : CommSq (boundaryToOld p) (boundaryToCell sq p)
      (pullback.fst p r) (pullback.fst p b) :=
    ⟨by rw [boundaryToOld_fst, boundaryToCell_fst]⟩
  exact ((Adhesive.van_kampen' sq)
    (boundaryToOld p) (boundaryToCell sq p)
    (pullback.fst p r) (pullback.fst p b)
    (pullback.snd p (t ≫ r)) (pullback.snd p r)
    (pullback.snd p b) p
    (boundaryToOld_isPullback p) (boundaryToCell_isPullback sq p)
    oldSq.toCommSq cellSq.toCommSq topComm).2 ⟨oldSq, cellSq⟩

end SSet.PreimagePushout
