/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSCoefficientForgetHomologyNaturality

/-! # Tests for forgotten coefficient-homology naturality -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.SInverseSCoefficientForgetHomologyNaturalityTests

open SInverseS

local instance : HasCoproducts.{0} AddCommGrpCat.{0} := by
  let h : HasColimitsOfSize.{0, 0} AddCommGrpCat.{0} := inferInstance
  exact fun J => h.has_colimits_of_shape (Discrete J)

local instance (A : Type) [Ring A] : HasCoproducts.{0} (ModuleCat.{0} A) := by
  let h : HasColimitsOfSize.{0, 0} (ModuleCat.{0} A) := inferInstance
  exact fun J => h.has_colimits_of_shape (Discrete J)

variable {J A : Type} [Category.{0} J] [CommRing A]
  {M N P : J ⥤ ModuleCat.{0} A}

local notation "U" => forget₂ (ModuleCat A) AddCommGrpCat

#check homologyWithCoefficientsForgetIso_hom_naturality

example (α : M ⟶ N) (n : ℕ) :
    (U).map
          ((CategoryHomology.homologyWithCoefficientsFunctor
            (C := J) (A := ModuleCat A) n).map α) ≫
        (homologyWithCoefficientsForgetIso N n).hom =
      (homologyWithCoefficientsForgetIso M n).hom ≫
        (CategoryHomology.homologyWithCoefficientsFunctor
          (C := J) (A := AddCommGrpCat) n).map
            (Functor.whiskerRight α U) := by
  let K_M : ChainComplex (ModuleCat.{0} A) ℕ :=
    CategoryHomology.normalizedCoefficientBarComplex M
  let K_N : ChainComplex (ModuleCat.{0} A) ℕ :=
    CategoryHomology.normalizedCoefficientBarComplex N
  let K_MU : ChainComplex AddCommGrpCat.{0} ℕ :=
    CategoryHomology.normalizedCoefficientBarComplex (M ⋙ U)
  let K_NU : ChainComplex AddCommGrpCat.{0} ℕ :=
    CategoryHomology.normalizedCoefficientBarComplex (N ⋙ U)
  let nM : K_M ⟶ K_N :=
    (CategoryHomology.normalizedCoefficientBarComplexFunctor
      (C := J) (A := ModuleCat A)).map α
  let nU : K_MU ⟶ K_NU :=
    (CategoryHomology.normalizedCoefficientBarComplexFunctor
      (C := J) (A := AddCommGrpCat)).map (Functor.whiskerRight α U)
  let eM : (U).obj (K_M.homology n) ≅ K_MU.homology n :=
    homologyWithCoefficientsForgetIso M n
  let eN : (U).obj (K_N.homology n) ≅ K_NU.homology n :=
    homologyWithCoefficientsForgetIso N n
  change (U).map (HomologicalComplex.homologyMap nM n) ≫ eN.hom =
    eM.hom ≫ HomologicalComplex.homologyMap nU n
  exact homologyWithCoefficientsForgetIso_hom_naturality
    (J := J) (A := A) (M := M) (N := N) α n

example (n : ℕ) :=
  homologyWithCoefficientsForgetIso_hom_naturality (𝟙 M) n

example (α : M ⟶ N) (β : N ⟶ P) (n : ℕ) :=
  homologyWithCoefficientsForgetIso_hom_naturality (α ≫ β) n

example (α : M ⟶ N) :=
  homologyWithCoefficientsForgetIso_hom_naturality α 0

example (n : ℕ) :=
  homologyWithCoefficientsForgetIso_hom_naturality
    (𝟙 ((Functor.const J).obj (ModuleCat.of A PUnit))) n

section SmallCategories

variable {A₀ : Type} [CommRing A₀]

example {M₀ N₀ : Discrete PUnit ⥤ ModuleCat A₀}
    (α : M₀ ⟶ N₀) (n : ℕ) :=
  homologyWithCoefficientsForgetIso_hom_naturality α n

example {M₀ N₀ : Discrete PEmpty ⥤ ModuleCat A₀}
    (α : M₀ ⟶ N₀) (n : ℕ) :=
  homologyWithCoefficientsForgetIso_hom_naturality α n

end SmallCategories

example {M₀ N₀ : Discrete PUnit ⥤ ModuleCat (ZMod 1)}
    (α : M₀ ⟶ N₀) (n : ℕ) :=
  homologyWithCoefficientsForgetIso_hom_naturality α n

#print axioms homologyWithCoefficientsForgetIso_hom_naturality

end CategoryTheory.SInverseSCoefficientForgetHomologyNaturalityTests

end
