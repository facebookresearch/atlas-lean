/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeIndDifferentialContexts

/-!
# Original inverse-image ring sheaves with normalized native beta scalars

The ring is the actual ordinary sheaf pullback. Its constants are the
original sheaf pullback adjunction unit followed by the actual subopen
restriction. This qualifies the projected DX and DP rings used by the
real graph and product calculations.
Source: DK1311.2374v2 Section4.10; Mathlib56a005, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PulledBetaRingModels

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open CompactSupportIndSheaves NativeIndDifferentialContexts RingedComplexCoefficientModels

variable {X Y : TopCat.{0}} (f : Y ⟶ X) (R : TopCat.Sheaf RingCat.{0} X)

def pullbackRing : TopCat.Sheaf RingCat.{0} Y := (TopCat.Sheaf.pullback RingCat.{0} f).obj R

def pullbackSection (U : Opens X) (a : R.obj.obj (op U))
    (V : Opens Y) (h : V ≤ (Opens.map f).obj U) : (pullbackRing f R).obj.obj (op V) :=
  let initial := (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{0} f).unit.app R).hom.app
    (op U)).hom a
  ((pullbackRing f R).obj.map (homOfLE h).op).hom initial

variable [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ X] [IndSpaceSource X] [BetaRingSource X R]

def pullbackConstant (c : ℂ) (V : Opens Y) : (pullbackRing f R).obj.obj (op V) :=
  letI : Algebra ℂ (R.obj.obj (op ⊤)) :=
    ComplexRingSheafSource.algebra (X := X) (R := R) ⊤
  let initial := (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{0} f).unit.app R).hom.app
    (op ⊤)).hom (algebraMap ℂ (R.obj.obj (op ⊤)) c)
  ((pullbackRing f R).obj.map (homOfLE (show V ≤ (Opens.map f).obj ⊤ from
    fun _ _ => trivial)).op).hom initial

variable [HasSheafify (Opens.grothendieckTopology Y) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ Y] [IndSpaceSource Y]

/-- A β-ring structure (`BetaRingSource`) on the inverse-image ring sheaf $f^{-1}R$ on $Y$ whose
complex scalars come from $R$: on every open $V$ of $Y$, $c ∈ ℂ$ maps to the restriction to $V$ of
the image of the constant $c$ of $R$ under the unit $R → f_*f^{-1}R$. -/
class PulledBetaRingSource where
  [source : BetaRingSource Y (pullbackRing f R)]
  constants : ∀ (V : Opens Y) (c : ℂ),
    letI : Algebra ℂ ((pullbackRing f R).obj.obj (op V)) :=
      ComplexRingSheafSource.algebra (X := Y) (R := pullbackRing f R) V
    algebraMap ℂ ((pullbackRing f R).obj.obj (op V)) c = pullbackConstant f R c V

attribute [instance_reducible, instance] PulledBetaRingSource.source

end MathlibExt.AlgebraicGeometry.PulledBetaRingModels
