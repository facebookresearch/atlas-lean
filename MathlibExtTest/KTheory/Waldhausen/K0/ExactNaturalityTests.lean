/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The dimension lift follows the Atlas Waldhausen K₀ client. The short-exact
rank calculation is adapted from Formal-Math's `KTheory/Ring/G0/DivisionRing.lean`
(Authors: @toskua, Avocado).
-/

module

import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Free
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Discrete.Basic
import MathlibExt.CategoryTheory.ExactCategory.Abelian
import MathlibExt.KTheory.Waldhausen.K0.Exact

/-! # Concrete naturality of the exact/Waldhausen `K₀` comparison

A diagram on the discrete two-point category is a pair of finite-dimensional rational
vector spaces. Evaluate at `true` and test the square on the pair `(0, ℚ)` (indexed
by `false` and `true`, respectively). Both routes give integer dimension `1`.
-/

open CategoryTheory Limits
open scoped ZeroObject

namespace MathlibExtTest.WaldhausenK0Comparison

private abbrev Vect := FGModuleCat.{0} ℚ
private abbrev PairVect := Discrete Bool ⥤ Vect

private abbrev evaluateRight : PairVect ⥤ Vect :=
  (evaluation (Discrete Bool) Vect).obj (Discrete.mk true)

private local instance : evaluateRight.IsExact where
  map_admissibleExact sequence admissible :=
    (show sequence.ShortExact from admissible).map_of_exact evaluateRight

private noncomputable local instance : WaldhausenCategoryWithoutGluing PairVect :=
  ExactCategory.waldhausenCategory PairVect

private noncomputable local instance : WaldhausenCategoryWithoutGluing Vect :=
  ExactCategory.waldhausenCategory Vect

private noncomputable def dimensionOnSkeleton : Skeleton Vect → ℤ :=
  Quotient.lift (fun space : Vect => (Module.finrank ℚ space : ℤ))
    (fun _ _ ⟨iso⟩ => congrArg Int.ofNat (FGModuleCat.isoToLinearEquiv iso).finrank_eq)

private theorem dimensionOnSkeleton_mk (space : Vect) :
    dimensionOnSkeleton (toSkeleton space) = (Module.finrank ℚ space : ℤ) := rfl

private theorem dimension_add (sequence : ShortComplex Vect) (admissible :
    ExactCategory.IsAdmissibleExact sequence) :
    dimensionOnSkeleton (toSkeleton sequence.X₂) =
      dimensionOnSkeleton (toSkeleton sequence.X₁) +
        dimensionOnSkeleton (toSkeleton sequence.X₃) := by
  let inclusion := forget₂ Vect (ModuleCat.{0} ℚ)
  let _ : inclusion.Additive := { map_add := fun {_ _} _ _ => rfl }
  have mapped : (sequence.map inclusion).ShortExact :=
    (show sequence.ShortExact from admissible).map_of_exact inclusion
  let _ : Module.Finite ℚ (sequence.map inclusion).X₁ := sequence.X₁.property
  let _ : Module.Finite ℚ (sequence.map inclusion).X₃ := sequence.X₃.property
  have ranks : Module.finrank ℚ sequence.X₂ =
      Module.finrank ℚ sequence.X₁ + Module.finrank ℚ sequence.X₃ :=
    ModuleCat.free_shortExact_finrank_add (R := ℚ) mapped rfl rfl
  simp only [dimensionOnSkeleton_mk]
  exact_mod_cast ranks

private noncomputable def dimension : AlgebraicKTheory.K0 Vect →+ ℤ :=
  AlgebraicKTheory.K0.lift dimensionOnSkeleton dimension_add

private theorem dimension_mk (space : Vect) :
    dimension (AlgebraicKTheory.K0.mk space) = (Module.finrank ℚ space : ℤ) := by
  rw [dimension, AlgebraicKTheory.K0.lift_mk, dimensionOnSkeleton_mk]

private noncomputable def generatorDiagram : PairVect :=
  Discrete.functor fun side : Bool => if side then FGModuleCat.of ℚ ℚ else 0

private noncomputable def generator : WaldhausenKTheory.K0 PairVect :=
  WaldhausenKTheory.K0.mk generatorDiagram

private noncomputable def topThenRight :
    WaldhausenKTheory.K0 PairVect →+ AlgebraicKTheory.K0 Vect :=
  (WaldhausenKTheory.K0.toExact Vect).comp (WaldhausenKTheory.K0.map evaluateRight)

private noncomputable def leftThenBottom :
    WaldhausenKTheory.K0 PairVect →+ AlgebraicKTheory.K0 Vect :=
  (AlgebraicKTheory.K0.map evaluateRight).comp (WaldhausenKTheory.K0.toExact PairVect)

example : topThenRight = leftThenBottom :=
  WaldhausenKTheory.K0.toExact_naturality PairVect evaluateRight

private theorem topDimension : dimension (topThenRight generator) = 1 := by
  rw [topThenRight, AddMonoidHom.comp_apply, generator, WaldhausenKTheory.K0.map_mk,
    WaldhausenKTheory.K0.toExact_mk, dimension_mk]
  change (Module.finrank ℚ ℚ : ℤ) = 1
  simp

example : dimension (leftThenBottom generator) = 1 := by
  rw [leftThenBottom, AddMonoidHom.comp_apply, generator, WaldhausenKTheory.K0.toExact_mk,
    AlgebraicKTheory.K0.map_mk, dimension_mk]
  change (Module.finrank ℚ ℚ : ℤ) = 1
  simp

example : generator ≠ 0 := by
  intro vanishes
  have contradiction := topDimension
  rw [vanishes, map_zero, map_zero] at contradiction
  exact zero_ne_one contradiction

end MathlibExtTest.WaldhausenK0Comparison
