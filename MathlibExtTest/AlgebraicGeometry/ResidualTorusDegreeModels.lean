/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ResidualTorusDegreeModels

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open AlgebraicWeightBundleModels AlgebraicSplitTorusModels TorusPolynomialDegreeModels
open IntegralChowChernModels ComplexAnalytification SymplecticTorusSourceModels
open CoefficientBettiModels TorusBorelCoefficientModels ResidualTorusDegreeModels
open MathlibExt.Topology.ContinuousBorelGroupMaps

namespace ResidualTorusDegreeModelsTest

variable {A T : Over base} [GrpObj A] [GrpObj T]
  {MA : TorusModel A} {MT : TorusModel T} {S : Subtorus A T}
  {P : TorusSplitting S} {F : SchemeData} [ModObj T F.scheme]
  {AF : AnalyticTorusAction MT F.scheme}
  (R : ResidualGeometry MA MT S P F AF) (C : CoefficientCoordinates MT)
  (ρ : PolynomialAction MT C F.scheme AF)

-- The predicate used by the stable-envelope degree condition: zero satisfies every strict
-- half-degree bound, including codimension zero.
example (c : ℕ) : strictHalfDegree R C ρ c 0 := Or.inl rfl

-- In codimension zero only the zero class has strictly smaller half degree.
example (a : H MT F.scheme AF) (h : strictHalfDegree R C ρ 0 a) :
    a = 0 := by
  rcases h with h | ⟨d, hd, _⟩
  · exact h
  · omega

-- A class of half degree at most `d` satisfies the bound in codimension `2 * d + 1`, but the
-- bound is strict: codimension `2 * d` is not enough for degree `d`.
example (d : ℕ) (a : H MT F.scheme AF)
    (ha : a ∈ degreeFiltration R C ρ d) : strictHalfDegree R C ρ (2 * d + 1) a :=
  Or.inr ⟨d, by omega, ha⟩

end ResidualTorusDegreeModelsTest
