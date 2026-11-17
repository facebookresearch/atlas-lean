/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IndSheafMonoidalModels
public import MathlibExt.AlgebraicGeometry.PresheafRingMonoidModels
public import MathlibExt.AlgebraicGeometry.DifferentialOperatorScalars

/-!
# Actual ring coefficient sheaves and their native beta monoids

The coefficient presheaf is every original ring-sheaf section with its
prescribed complex scalar action. Ordinary unit/multiplication agree on
all actual section values and tensor generators. Beta then maps this
specific ring monoid by the native monoidal-functor construction.
This is the beta-A carrier of DK Section 4.10, with local-End actions.

Source: DK arXiv:1311.2374v2, Section 4.10; native monoid constructors
at Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BetaDifferentialRingModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj
open _root_.Opposite TopologicalSpace
open CompactSupportIndSheaves IndSheafCoefficientModels IndSheafAlphaBetaModels
open RingedComplexCoefficientModels PresheafRingMonoidModels IndSheafMonoidalModels

variable (X : TopCat.{0}) (R : TopCat.Sheaf RingCat.{0} X) [ComplexRingSheafSource X R]

structure RingCoefficientSheafSource : Prop where
  isSheaf : Presheaf.IsSheaf (Opens.grothendieckTopology X) (ringModulePresheaf X R)

def ringCoefficientSheaf (S : RingCoefficientSheafSource X R) : OrdinarySheaf ℂ X :=
  ⟨ringModulePresheaf X R, S.isSheaf⟩

variable [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)]
  [OrdinaryMonoidalSource ℂ X] (S : RingCoefficientSheafSource X R)

/-- Ordinary monoid construction is fixed by the original unit and every product. -/
structure OrdinaryRingMonoidSource where
  [monoid : MonObj (ringCoefficientSheaf X R S)]
  unitValue : ∀ (U : Opens X) (c : ℂ),
    (η[ringCoefficientSheaf X R S]).hom.app (op U) (sourceUnitSection ℂ X U c) =
      algebraMap ℂ (R.obj.obj (op U)) c
  multiplyValue : ∀ (U : Opens X) (a b : R.obj.obj (op U)),
    (μ[ringCoefficientSheaf X R S]).hom.app (op U)
      (sourceTensorSection ℂ X (ringCoefficientSheaf X R S) (ringCoefficientSheaf X R S) U a b) =
        a * b

variable (T : CompactTensorSource ℂ X) (I : IndTensorSource ℂ X T)
  [IndMonoidalSource ℂ X T I]
  (A : AlphaSource ℂ X) (B : BetaSource ℂ X A)

def betaRingMonoid (P : BetaMonoidalSource ℂ X T I A B)
    (M : OrdinaryRingMonoidSource X R S) : Mon (IndSheaf ℂ X) :=
  letI := P.monoidal
  letI := M.monoid
  (IndSheafMonoidalModels.betaMonoid ℂ X T I A B P).obj (Mon.mk (ringCoefficientSheaf X R S))

end MathlibExt.AlgebraicGeometry.BetaDifferentialRingModels
