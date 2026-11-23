/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarChangeOfCategory
import Mathlib.RepresentationTheory.Rep.Basic

/-! Direct generic coefficient-category comparison contracts, including the
same Rep-to-Module specialization consumed by the homotopy-fiber proof. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology AlgebraicTopology
open scoped Simplicial

universe uG vG uA vA uB vB w

#check @nervePullbackCoefficientDegreeChangeOfCategoryIso
#print axioms nervePullbackCoefficientDegreeChangeOfCategoryIso
#check @nervePullbackCoefficientDegreeChangeOfCategoryIso_ι
#print axioms nervePullbackCoefficientDegreeChangeOfCategoryIso_ι
#check @nervePullbackCoefficientDegreeChangeOfCategoryIso_inv_ι
#print axioms nervePullbackCoefficientDegreeChangeOfCategoryIso_inv_ι
#check @nervePullbackCoefficientSimplicialChangeOfCategoryIso
#print axioms nervePullbackCoefficientSimplicialChangeOfCategoryIso
#check @nervePullbackCoefficientComplexChangeOfCategoryIso
#print axioms nervePullbackCoefficientComplexChangeOfCategoryIso
#check @nervePullbackCoefficientComplexChangeOfCategoryIso_hom_f
#print axioms nervePullbackCoefficientComplexChangeOfCategoryIso_hom_f
#check @nervePullbackCoefficientComplexChangeOfCategoryIso_base
#print axioms nervePullbackCoefficientComplexChangeOfCategoryIso_base

section Generic

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A] [HasCoproducts.{max uG vG} A]
variable {B : Type uB} [Category.{vB} B] [HasCoproducts.{max uG vG} B]
variable (F : A ⥤ B) [PreservesColimitsOfSize.{max uG vG, max uG vG} F]
variable {T : SSet.{max uG vG}} (φ : T ⟶ CategoryTheory.nerve G) (M : G ⥤ A)

-- Forward and inverse coordinates on every actual simplex, without preadditivity.
example (n : ℕ) (σ : T _⦋n⦌) :
    F.map (nervePullbackCoefficientι φ M σ) ≫
        (nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M n).hom =
      nervePullbackCoefficientι φ (M ⋙ F) σ :=
  nervePullbackCoefficientDegreeChangeOfCategoryIso_ι F φ M n σ

example (n : ℕ) (σ : T _⦋n⦌) :
    nervePullbackCoefficientι φ (M ⋙ F) σ ≫
        (nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M n).inv =
      F.map (nervePullbackCoefficientι φ M σ) :=
  nervePullbackCoefficientDegreeChangeOfCategoryIso_inv_ι F φ M n σ

-- The actual simplicial comparison commutes with every simplex-category map.
example {Δ Δ' : SimplexCategoryᵒᵖ} (a : Δ ⟶ Δ') :
    F.map ((nervePullbackCoefficientSimplicial φ M).map a) ≫
        (nervePullbackCoefficientSimplicialChangeOfCategoryIso F φ M).hom.app Δ' =
      (nervePullbackCoefficientSimplicialChangeOfCategoryIso F φ M).hom.app Δ ≫
        (nervePullbackCoefficientSimplicial φ (M ⋙ F)).map a :=
  (nervePullbackCoefficientSimplicialChangeOfCategoryIso F φ M).hom.naturality a

section Complex

variable [Preadditive A] [Preadditive B] [F.Additive]

example (n : ℕ) :
    (nervePullbackCoefficientComplexChangeOfCategoryIso F φ M).hom.f n =
      (nervePullbackCoefficientDegreeChangeOfCategoryIso F φ M n).hom :=
  nervePullbackCoefficientComplexChangeOfCategoryIso_hom_f F φ M n

-- The complete original base map is preserved, for independent source and
-- coefficient object/Hom universes; no exactness or flatness is supplied.
example {U : SSet.{max uG vG}} (f : T ⟶ U) (ψ : U ⟶ CategoryTheory.nerve G) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (nervePullbackCoefficientBaseComplexMap f ψ M) ≫
        (nervePullbackCoefficientComplexChangeOfCategoryIso F ψ M).hom =
      (nervePullbackCoefficientComplexChangeOfCategoryIso F (f ≫ ψ) M).hom ≫
        nervePullbackCoefficientBaseComplexMap f ψ (M ⋙ F) :=
  nervePullbackCoefficientComplexChangeOfCategoryIso_base F M f ψ

end Complex
end Generic

section ActualForget

variable {G : Type w} [Category.{w} G] {Γ : Type w} [Group Γ]

local instance (I : Type w) : HasColimitsOfShape (Discrete I) AddCommGrpCat.{w} :=
  letI : Small.{w} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

local instance (I : Type w) : HasColimitsOfShape (Discrete I) (ModuleCat.{w} ℤ) :=
  letI : Small.{w} (Discrete I) := small_self (Discrete I)
  letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{w} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

local instance : HasCoproducts.{w} (ModuleCat.{w} ℤ) :=
  fun I =>
    letI : Small.{w} (Discrete I) := small_self (Discrete I)
    letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{w} :=
      AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
    ModuleCat.hasColimitsOfShape (J := Discrete I) (R := ℤ)

local instance : HasCoproducts.{w} (Rep.{w} ℤ Γ) :=
  fun I => inferInstanceAs (HasColimitsOfShape (Discrete I) (Rep.{w} ℤ Γ))

-- The actual forgetful comparison used by the original regular-chain proof.
example {T U : SSet.{w}} (f : T ⟶ U) (ψ : U ⟶ CategoryTheory.nerve G)
    (M : G ⥤ Rep.{w} ℤ Γ) :
    ((forget₂ (Rep.{w} ℤ Γ) (ModuleCat.{w} ℤ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (nervePullbackCoefficientBaseComplexMap f ψ M) ≫
      (nervePullbackCoefficientComplexChangeOfCategoryIso
        (forget₂ (Rep.{w} ℤ Γ) (ModuleCat.{w} ℤ)) ψ M).hom =
    (nervePullbackCoefficientComplexChangeOfCategoryIso
      (forget₂ (Rep.{w} ℤ Γ) (ModuleCat.{w} ℤ)) (f ≫ ψ) M).hom ≫
      nervePullbackCoefficientBaseComplexMap f ψ
        (M ⋙ forget₂ (Rep.{w} ℤ Γ) (ModuleCat.{w} ℤ)) :=
  nervePullbackCoefficientComplexChangeOfCategoryIso_base
    (forget₂ (Rep.{w} ℤ Γ) (ModuleCat.{w} ℤ)) M f ψ

end ActualForget

end
