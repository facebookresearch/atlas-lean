/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.HigherUnits
public import MathlibExt.NumberTheory.NumberField.HeckeCharacter

@[expose] public section

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal

namespace HigherUnitsTest

variable (p : HeightOneSpectrum (𝓞 ℚ))

/-- The higher unit group at level `0` is the set of units of valuation `1`. -/
example (u : (p.adicCompletion ℚ)ˣ) :
    u ∈ higherUnitsAt ℚ p 0 ↔ Valued.v (u : p.adicCompletion ℚ) = 1 := by
  simp [mem_higherUnitsAt_iff]

private theorem valued_unif :
    Valued.v (AdelicLevel.uniformizerUnit (𝓞 ℚ) ℚ p : p.adicCompletion ℚ) =
      WithZero.exp (-1 : ℤ) :=
  AdelicLevel.valued_uniformizerUnit (𝓞 ℚ) ℚ p

private theorem valued_one_add_unif :
    Valued.v (1 + (AdelicLevel.uniformizerUnit (𝓞 ℚ) ℚ p : p.adicCompletion ℚ)) = 1 :=
  Valuation.map_one_add_of_lt _ (by rw [valued_unif]; exact WithZero.exp_lt_one_iff.mpr (by norm_num))

/-- The unit `1 + ϖ` for the uniformizer `ϖ = uniformizerUnit (𝓞 ℚ) ℚ p`. -/
private noncomputable def onePlusUnif : (p.adicCompletion ℚ)ˣ :=
  Units.mk0 (1 + (AdelicLevel.uniformizerUnit (𝓞 ℚ) ℚ p : p.adicCompletion ℚ)) fun h => by
    have := valued_one_add_unif p
    rw [h, map_zero] at this
    exact zero_ne_one this

/-- A uniformizer has valuation `exp (-1) ≠ 1`, so it is not in the level-zero group. -/
example : AdelicLevel.uniformizerUnit (𝓞 ℚ) ℚ p ∉ higherUnitsAt ℚ p 0 := fun h => by
  have h1 := ((mem_higherUnitsAt_iff ℚ p).mp h).1
  rw [valued_unif, ← WithZero.exp_zero, WithZero.exp_inj] at h1
  norm_num at h1

/-- `1 + ϖ` is congruent to `1` modulo `𝔭`, so it lies in the level-one group. -/
example : onePlusUnif p ∈ higherUnitsAt ℚ p 1 := by
  refine (mem_higherUnitsAt_iff ℚ p).mpr ⟨valued_one_add_unif p, Or.inr ?_⟩
  rw [onePlusUnif, Units.val_mk0, add_sub_cancel_left, valued_unif]
  rfl

/-- `1 + ϖ` is not congruent to `1` modulo `𝔭²`, so it is not in the level-two group: the
exponent in the definition is exactly `n`. -/
example : onePlusUnif p ∉ higherUnitsAt ℚ p 2 := fun h => by
  rcases ((mem_higherUnitsAt_iff ℚ p).mp h).2 with h2 | h2
  · exact two_ne_zero h2
  · rw [onePlusUnif, Units.val_mk0, add_sub_cancel_left, valued_unif, WithZero.exp_le_exp] at h2
    norm_num at h2

end HigherUnitsTest
