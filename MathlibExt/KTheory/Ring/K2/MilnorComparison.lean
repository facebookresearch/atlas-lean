/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.AbelianFunctor
public import MathlibExt.KTheory.Ring.K2.SteinbergSymbol
public import MathlibExt.KTheory.Milnor.ClassicalK2Lift
import MathlibExt.KTheory.Ring.K2.SteinbergSymbolBilinearity
import MathlibExt.KTheory.Ring.K2.SteinbergSymbolSteinbergRelation

/-! # Forward Milnor comparison in degree two

Descending the algebraic `K₂` Steinberg symbol through
`MilnorK.liftK2OfBimap` via the bundled `SteinbergBimap` API.

The algebraic `K₂` Steinberg symbol is separately multiplicative and
satisfies the Steinberg relation, so it forms a `MilnorK.SteinbergBimap`
with target `Additive (K₂ F)`. Its universal lift is the forward
comparison `MilnorK F 2 →ₗ[ℤ] K₂ F`.
-/

public section

open scoped IsMulCommutative

universe u

namespace AlgebraicKTheory

namespace K2

/-- Bundled Steinberg bimap for the algebraic `K₂` symbol. -/
noncomputable def steinbergBimap (F : Type u) [Field F] :
    MilnorK.SteinbergBimap F (Additive (K2 F)) where
  toFun a b := Additive.ofMul (steinbergSymbol a b)
  map_mul_left a₁ a₂ b := by
    simp only [steinbergSymbol_mul_left, ofMul_mul]
  map_mul_right a b₁ b₂ := by
    simp only [steinbergSymbol_mul_right, ofMul_mul]
  steinberg a ha0 ha1 := by
    simp only [steinbergSymbol_steinberg a ha0 ha1, ofMul_one]

/-- Comparison from degree-two Milnor K-theory to algebraic K2. -/
noncomputable def milnorComparison (F : Type u) [Field F] :
    MilnorK F 2 →ₗ[ℤ] Additive (K2 F) :=
  MilnorK.liftK2OfBimap (steinbergBimap F)

/-- The comparison sends a Milnor symbol to the algebraic `K₂` Steinberg symbol. -/
@[simp]
theorem milnorComparison_k2Symbol (F : Type u) [Field F] (a b : Fˣ) :
    milnorComparison F (MilnorK.k2Symbol F a b) =
      Additive.ofMul (K2.steinbergSymbol a b) := by
  simp [milnorComparison, steinbergBimap]

end K2

end AlgebraicKTheory

end
