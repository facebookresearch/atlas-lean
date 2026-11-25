/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.Additive
public import MathlibExt.Algebra.Homology.Linear
public import MathlibExt.CategoryTheory.Abelian.RightDerived.NatIso

/-!
# Linearity of right-derived functors

For a linear additive functor between linear abelian categories, its
right-derived functors are linear. Injective-resolution lifts, the
homotopy quotient and homology preserve the scalar action.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Category

universe t u v u' v'

namespace CategoryTheory

variable (R : Type t) [Semiring R]

/-- Injective resolutions retain a supplied category scalar action. -/
instance injectiveResolutions_linear
    (C : Type u) [Category.{v} C] [Abelian C] [CategoryTheory.Linear R C]
    [HasInjectiveResolutions C] : (injectiveResolutions C).Linear R where
  map_smul {X Y} f r := by
    dsimp [injectiveResolutions]
    suffices h : (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc (r • f) (injectiveResolution Y)
          (injectiveResolution X)) =
      (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
        (r • InjectiveResolution.desc f (injectiveResolution Y)
          (injectiveResolution X)) by
      rw [h]
      exact (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map_smul r _
    apply HomotopyCategory.eq_of_homotopy
    apply InjectiveResolution.descHomotopy (r • f)
    · exact InjectiveResolution.desc_commutes (r • f) _ _
    · rw [Linear.comp_smul, InjectiveResolution.desc_commutes f,
        Functor.map_smul, Linear.smul_comp]

/-- The right-derived functors of a linear additive functor are linear. -/
instance Functor.rightDerived_linear
    {C : Type u} [Category.{v} C] [Abelian C] [CategoryTheory.Linear R C]
    [HasInjectiveResolutions C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [CategoryTheory.Linear R D]
    (F : C ⥤ D) [F.Additive] [CategoryTheory.Functor.Linear R F] (n : ℕ) :
    (F.rightDerived n).Linear R := by
  dsimp only [Functor.rightDerived, Functor.rightDerivedToHomotopyCategory]
  infer_instance

end CategoryTheory
