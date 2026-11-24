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

public import MathlibExt.KTheory.Ring.K2.MilnorComparison
public import MathlibExt.KTheory.Milnor.ClassicalMapSymbols

/-! # Naturality of the degree-two Milnor comparison

The degree-two Milnor comparison commutes with field homomorphisms.
-/

@[expose] public section

open scoped IsMulCommutative

universe u

namespace AlgebraicKTheory.K2

/-- The degree-two Milnor comparison commutes with field homomorphisms. -/
@[simp]
theorem mapRingHom_milnorComparison
    {F K : Type u} [Field F] [Field K]
    (f : F →+* K) (x : MilnorK F 2) :
    (K2.mapRingHom f).toAdditive (milnorComparison F x) =
      milnorComparison K (MilnorK.map f 2 x) := by
  have h_eq : (K2.mapRingHom f).toAdditive.toIntLinearMap.comp (milnorComparison F) =
      (milnorComparison K).comp (MilnorK.map f 2) := by
    apply MilnorK.k2Symbol_ext
    intro a b
    apply Additive.ext
    simp only [LinearMap.comp_apply, milnorComparison_k2Symbol, MilnorK.map_k2Symbol,
      AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive, Function.comp_apply,
      toMul_ofMul]
    rw [K2.mapRingHom_steinbergSymbol]
  have hx := LinearMap.congr_fun h_eq x
  simp only [LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap] at hx
  exact hx

end AlgebraicKTheory.K2

end
