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

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.TorBalance
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Exactness
public import MathlibExt.Algebra.Homology.HomologicalComplex.CyclesComplex

/-!
# Tor vanishing and flatness of balanced tensor

The opposite-variable Tor comparison turns first-variable Tor₁ vanishing
into exactness of the coefficient tensor functor and vanishing of higher Tor.
The derived exact sequence shows that flat middle and quotient modules have
flat kernels. This applies to the cycles, term and outgoing-image sequence
in every complex shape.

The ring and modules are arbitrary; projectivity of the modules or
differential images is not required.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits

universe u v w

namespace ModuleCat.BalancedTensor

variable (R : Type u) [Ring R]
  [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
  [HasProjectiveResolutions (ModuleCat.{v} R)]

/-- Exactness in the coefficient variable is detected by the actual first-variable Tor₁. -/
theorem groupBifunctor_obj_preservesFiniteLimits_iff_torFirst_one
    (A : ModuleCat.{v} Rᵐᵒᵖ) :
    PreservesFiniteLimits ((groupBifunctor R).obj A) ↔
      ∀ B : ModuleCat.{v} R, IsZero (((torFirst R 1).obj A).obj B) := by
  let F : ModuleCat.{v} R ⥤ AddCommGrpCat.{v} := (groupBifunctor R).obj A
  constructor
  · intro h B
    letI : PreservesFiniteLimits F := h
    have hSecond : IsZero (((torSecond R 1).obj A).obj B) := by
      change IsZero ((F.leftDerived 1).obj B)
      exact Functor.isZero_leftDerived_obj_succ_of_preservesHomology F B 0
    exact hSecond.of_iso (torBalanceObjIso R A B 1).symm
  · intro h
    apply Functor.preservesFiniteLimits_of_isZero_leftDerived_one F
    intro B
    have hSecond := (h B).of_iso (torBalanceObjIso R A B 1)
    change IsZero ((F.leftDerived 1).obj B) at hSecond
    exact hSecond

/-- First-variable Tor₁ vanishing implies vanishing in every positive degree. -/
theorem isZero_torFirst_obj_succ_of_torFirst_one (A : ModuleCat.{v} Rᵐᵒᵖ)
    (hA : ∀ B : ModuleCat.{v} R, IsZero (((torFirst R 1).obj A).obj B))
    (B : ModuleCat.{v} R) (n : ℕ) :
    IsZero (((torFirst R (n + 1)).obj A).obj B) := by
  let F : ModuleCat.{v} R ⥤ AddCommGrpCat.{v} := (groupBifunctor R).obj A
  letI : PreservesFiniteLimits F :=
    (groupBifunctor_obj_preservesFiniteLimits_iff_torFirst_one R A).2 hA
  have hSecond : IsZero (((torSecond R (n + 1)).obj A).obj B) := by
    change IsZero ((F.leftDerived (n + 1)).obj B)
    exact Functor.isZero_leftDerived_obj_succ_of_preservesHomology F B n
  exact hSecond.of_iso (torBalanceObjIso R A B (n + 1)).symm

omit [HasProjectiveResolutions (ModuleCat.{v} R)] in
/-- Tensoring an original right-module short exact sequence with a fixed
left coefficient stays short exact when that single quotient Tor₁ value vanishes. -/
theorem shortExact_map_tensor_of_isZero_torFirst_one
    {S : ShortComplex (ModuleCat.{v} Rᵐᵒᵖ)} (hS : S.ShortExact)
    (B : ModuleCat.{v} R) (h₃ : IsZero (((torFirst R 1).obj S.X₃).obj B)) :
    (S.map ((groupBifunctor R).flip.obj B)).ShortExact := by
  let F : ModuleCat.{v} Rᵐᵒᵖ ⥤ AddCommGrpCat.{v} := (groupBifunctor R).flip.obj B
  letI : F.Additive := Functor.LeftDerivedBalance.flippedObjAdditive (groupBifunctor R) B
  have h₁ : IsZero ((F.leftDerived 1).obj S.X₃) := by
    change IsZero (((torFirst R 1).obj S.X₃).obj B)
    exact h₃
  exact ShortComplex.ShortExact.map_of_isZero_leftDerived_one F hS h₁

omit [HasProjectiveResolutions (ModuleCat.{v} R)] in
/-- Tensoring an original right-module short exact sequence stays short exact
when its quotient is Tor₁-flat; the other two modules need no flatness premise. -/
theorem shortExact_map_tensor_of_torFirst_one
    {S : ShortComplex (ModuleCat.{v} Rᵐᵒᵖ)} (hS : S.ShortExact)
    (h₃ : ∀ B : ModuleCat.{v} R, IsZero (((torFirst R 1).obj S.X₃).obj B))
    (B : ModuleCat.{v} R) :
    (S.map ((groupBifunctor R).flip.obj B)).ShortExact :=
  shortExact_map_tensor_of_isZero_torFirst_one R hS B (h₃ B)

/-- A kernel of a surjection between Tor₁-flat right modules is Tor₁-flat,
using the genuine Tor₂ → Tor₁ → Tor₁ segment of the native derived sequence. -/
theorem isZero_torFirst_one_of_shortExact
    {S : ShortComplex (ModuleCat.{v} Rᵐᵒᵖ)} (hS : S.ShortExact)
    (h₂ : ∀ B : ModuleCat.{v} R, IsZero (((torFirst R 1).obj S.X₂).obj B))
    (h₃ : ∀ B : ModuleCat.{v} R, IsZero (((torFirst R 1).obj S.X₃).obj B))
    (B : ModuleCat.{v} R) : IsZero (((torFirst R 1).obj S.X₁).obj B) := by
  let F : ModuleCat.{v} Rᵐᵒᵖ ⥤ AddCommGrpCat.{v} := (groupBifunctor R).flip.obj B
  letI : F.Additive := Functor.LeftDerivedBalance.flippedObjAdditive (groupBifunctor R) B
  have hSource : IsZero ((F.leftDerived (1 + 1)).obj S.X₃) := by
    change IsZero (((torFirst R (1 + 1)).obj S.X₃).obj B)
    exact isZero_torFirst_obj_succ_of_torFirst_one R S.X₃ h₃ B 1
  have hTarget : IsZero ((F.leftDerived 1).obj S.X₂) := by
    change IsZero (((torFirst R 1).obj S.X₂).obj B)
    exact h₂ B
  change IsZero ((F.leftDerived 1).obj S.X₁)
  exact Functor.isZero_leftDerived_obj_of_shortExact F 1 hS hSource hTarget

/-- Flat original terms and outgoing images give flat actual cycles in any shape. -/
theorem isZero_torFirst_one_cycles {ι : Type w} {c : ComplexShape ι}
    (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c)
    (hP : ∀ i B, IsZero (((torFirst R 1).obj (P.X i)).obj B))
    (hI : ∀ i B,
      IsZero (((torFirst R 1).obj (Abelian.image (P.d i (c.next i)))).obj B))
    (i : ι) (B : ModuleCat.{v} R) :
    IsZero (((torFirst R 1).obj (P.cycles i)).obj B) := by
  let S := HomologicalComplex.cyclesImageSequence P i (c.next i)
  have hS : S.ShortExact :=
    HomologicalComplex.cyclesImageSequence_shortExact P i (c.next i) rfl
  exact isZero_torFirst_one_of_shortExact R hS (hP i) (hI i) B

omit [HasProjectiveResolutions (ModuleCat.{v} R)] in
/-- The original cycles/term/outgoing-image point sequence remains exact after
balanced tensoring with an arbitrary coefficient when that image is flat. -/
theorem cyclesImageSequence_map_tensor_shortExact {ι : Type w} {c : ComplexShape ι}
    (P : HomologicalComplex (ModuleCat.{v} Rᵐᵒᵖ) c) (i : ι)
    (hI : ∀ B : ModuleCat.{v} R,
      IsZero (((torFirst R 1).obj (Abelian.image (P.d i (c.next i)))).obj B))
    (B : ModuleCat.{v} R) :
    ((HomologicalComplex.cyclesImageSequence P i (c.next i)).map
      ((groupBifunctor R).flip.obj B)).ShortExact :=
  shortExact_map_tensor_of_torFirst_one R
    (HomologicalComplex.cyclesImageSequence_shortExact P i (c.next i) rfl) hI B

end ModuleCat.BalancedTensor
