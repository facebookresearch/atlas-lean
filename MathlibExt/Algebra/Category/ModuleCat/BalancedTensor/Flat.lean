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
# Flatness criteria from balanced Tor

Let `R` be an arbitrary ring, and assume the right and left module categories in the chosen
carrier universe have projective resolutions. A right module `A` has an exact tensor functor
`A ⊗_R -` precisely when `Tor¹_R(A, B)` vanishes for every left module `B`. This condition
also gives vanishing in all positive Tor degrees.

For a short exact sequence of right modules, vanishing of `Tor¹` for the quotient at a fixed
left module makes tensoring preserve the sequence. If the middle and quotient modules satisfy
the all-left-module vanishing condition, so does the kernel. Consequently, flat complex terms
and flat outgoing differential images give flat cycles, for arbitrary complex shapes.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits

universe u v w

namespace ModuleCat.BalancedTensor

variable (R : Type u) [Ring R]
  [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
  [HasProjectiveResolutions (ModuleCat.{v} R)]

/-- Exactness of a balanced tensor functor is detected by Tor one.

For a right `R`-module `A`, preservation of finite limits by the group-valued tensor functor
`A ⊗_R -` is equivalent to `Tor¹_R(A, B) = 0` for every left module `B`, assuming both module
categories have projective resolutions. -/
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

/-- All-left-module Tor-one vanishing gives every positive Tor degree.

If `Tor¹_R(A, B)` vanishes for every left module `B`, then `Tor^(n+1)_R(A, B)` vanishes for
every natural `n` and every left module `B`. -/
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
/-- Tensor preserves a short exact sequence when quotient Tor one vanishes.

Let `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of right modules. If `Tor¹_R(S.X₃,
B)` is zero for a fixed left module `B`, tensoring the sequence with `B` gives a short exact
sequence of additive groups. -/
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
/-- Flat quotient makes each tensor image sequence short exact.

A short exact sequence of right modules remains short exact after tensoring with any left
module `B` if the quotient has zero `Tor¹` against every left module. -/
theorem shortExact_map_tensor_of_torFirst_one
    {S : ShortComplex (ModuleCat.{v} Rᵐᵒᵖ)} (hS : S.ShortExact)
    (h₃ : ∀ B : ModuleCat.{v} R, IsZero (((torFirst R 1).obj S.X₃).obj B))
    (B : ModuleCat.{v} R) :
    (S.map ((groupBifunctor R).flip.obj B)).ShortExact :=
  shortExact_map_tensor_of_isZero_torFirst_one R hS B (h₃ B)

/-- Flat middle and quotient modules give a flat kernel.

In a short exact sequence of right modules, suppose the middle and quotient modules have zero
`Tor¹` against every left module. Then the kernel has zero `Tor¹` against each left module
`B`. -/
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

/-- Flat terms and outgoing images give flat cycles.

For a complex of right modules in any complex shape, suppose every term and every outgoing
differential image has zero `Tor¹` against every left module. Then each cycle object also has
zero `Tor¹` against every left module. -/
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
/-- Cycles-to-term-to-image sequence remains exact under tensor.

For a right-module complex `P` and index `i`, assume its outgoing differential image at `i`
has zero `Tor¹` against every left module. The short exact sequence from `P.cycles i` to `P.X
i` to that image remains short exact after tensoring with any left module `B`. -/
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
