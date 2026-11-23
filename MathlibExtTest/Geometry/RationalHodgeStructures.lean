/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.RationalHodgeStructures

@[expose] public section

/-!
# Tests for rational Hodge data

The rational carrier of a complexification is finite-dimensional and its
comparison map is rational linear for the compatible scalar actions. Every
complexification carries the weight-zero Hodge structure of type `(0, 0)`
(`Fᵖ = ⊤` for `p ≤ 0`, `⊥` otherwise), whose opposedness uses that conjugation
is surjective. The complexification of the zero subspace is zero, and mixed
Hodge maps compose and have identities through their realization maps.
-/

noncomputable section

open MathlibExt.Geometry.RationalHodgeStructures

namespace MathlibExtTest.Geometry.RationalHodgeStructures

variable {V : ModuleCat.{0} ℚ} (C : RationalComplexification V)

example : FiniteDimensional ℚ V := C.finiteDimensional

/-- The comparison map is rational linear, and rational scalars act on the
complex space through `ℚ → ℂ`. -/
example (q : ℚ) (v : V) :
    C.comparisonMap (q • v) = (q : ℂ) • C.comparisonMap v := by
  rw [map_smul, ← algebraMap_smul ℂ q (C.comparisonMap v), eq_ratCast]

/-- Conjugation maps the whole complex space onto itself. -/
private theorem map_conjugation_top :
    (⊤ : Submodule ℂ C.complexSpace).map C.conjugation.toLinearMap = ⊤ := by
  rw [Submodule.map_top]
  exact C.conjugation.range

/-- The weight-zero Hodge structure of type `(0, 0)`. -/
example : PureHodgeStructure C 0 where
  F p := if p ≤ 0 then ⊤ else ⊥
  antitone := by
    intro p q hpq
    by_cases hq : q ≤ 0
    · simp [hq, show p ≤ 0 by omega]
    · simp [hq]
  exhaustive := ⟨0, by simp⟩
  opposed := by
    intro p
    by_cases hp : p ≤ 0
    · simpa [hp, show ¬ (1 ≤ p) by omega] using isCompl_top_bot
    · simp only [hp, show 0 + 1 - p ≤ 0 by omega, ↓reduceIte]
      rw [map_conjugation_top]
      exact isCompl_bot_top

example : complexifiedSubspace C ⊥ = ⊥ := by
  simp [complexifiedSubspace]

section Maps

variable {V' V'' : ModuleCat.{0} ℚ} {C' : RationalComplexification V'}
  {C'' : RationalComplexification V''} {H : MixedHodgeStructure C}
  {H' : MixedHodgeStructure C'} {H'' : MixedHodgeStructure C''}

example : (MixedHodgeMap.id H).rationalMap = LinearMap.id := rfl

example (g : MixedHodgeMap H' H'') (f : MixedHodgeMap H H') :
    (g.comp f).rationalMap = g.rationalMap.comp f.rationalMap ∧
      (g.comp f).complexMap = g.complexMap.comp f.complexMap :=
  ⟨rfl, rfl⟩

end Maps

end MathlibExtTest.Geometry.RationalHodgeStructures
