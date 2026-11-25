/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.LogStructures

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MathlibExt.AlgebraicGeometry.LogStructures

private abbrev N := CommMonCat.of ℕ

private def zeroArrow : CommMonCat.of PUnit ⟶ N :=
  CommMonCat.ofHom (1 : PUnit →* ℕ)

private abbrev Q : CommMonCat := pushout (C := CommMonCat) zeroArrow zeroArrow

private def leftProjection : Q ⟶ N :=
  pushout.desc (𝟙 N) (CommMonCat.ofHom (1 : ℕ →* ℕ))
    (by rfl)

private def x : Q :=
  (pushout.inl zeroArrow zeroArrow) 2

private def y : Q :=
  (pushout.inr zeroArrow zeroArrow) 2

/-- The native commutative-monoid colimit both commutes and retains its two
independent generators; this detects an accidental collapsed colimit. -/
example : x * y = y * x := mul_comm _ _

example : x ≠ y := by
  have hl : pushout.inl zeroArrow zeroArrow ≫ leftProjection = 𝟙 N :=
    pushout.inl_desc ..
  have hr : pushout.inr zeroArrow zeroArrow ≫ leftProjection = CommMonCat.ofHom (1 : ℕ →* ℕ) :=
    pushout.inr_desc ..
  have hx : leftProjection x = 2 := by
    change (pushout.inl zeroArrow zeroArrow ≫ leftProjection) 2 = _
    rw [hl]
    rfl
  have hy : leftProjection y = 1 := by
    change (pushout.inr zeroArrow zeroArrow ≫ leftProjection) 2 = _
    rw [hr]
    rfl
  intro h
  have ht : (2 : N) = 1 := hx.symm.trans ((congrArg leftProjection h).trans hy)
  exact Nat.succ_ne_self 1 ht

private abbrev X := Spec (CommRingCat.of ℚ)
private abbrev J := Opens.grothendieckTopology X
private abbrev O : RingSheaf J := X.sheaf
private def L : LogStructure J O := trivialLog J O

/-- On an actual scheme, the forced map of the trivial log's unit sheaf is
the identity, with no inversion or scalar twist. -/
example : unitMap J L = 𝟙 (units J O) := by
  have : Mono (unitInclusion J O) := unitInclusion_mono J O
  apply (cancel_mono (unitInclusion J O)).1
  change unitMap J L ≫ alpha J L = _
  exact (unitMap_alpha J L).trans (Category.id_comp _).symm

/-- The logification comparison preserves the given native prelog map. -/
example : toAssociated J L.obj ≫ associatedMap J L (𝟙 L.obj) = 𝟙 L.obj := by
  exact toAssociated_associatedMap J L (𝟙 L.obj)
