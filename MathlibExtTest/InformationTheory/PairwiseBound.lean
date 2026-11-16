/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.PairwiseBound
import Mathlib.Tactic.NormNum

@[expose] public section

open InformationTheory MathlibExt.Quantum.ClassicalFuchsVanDeGraaf

namespace MathlibExtTest.InformationTheory.PairwiseBound

/-- Equal point masses: the whole mass `1` is bounded by the coefficient, which is `1`. -/
example : ∑ _x ∈ Finset.univ.filter (fun _ : Fin 1 => (1 : ℝ) ≤ 1), (1 : ℝ)
    ≤ bhattacharyyaCoeff (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 1) :=
  pairwise_error_le (fun _ => 1) (fun _ => 1) (fun _ => zero_le_one)

/-- The alphabet can be any finite type, here `Bool`. -/
example (p q : Bool → ℝ) (hp0 : ∀ b, 0 ≤ p b) :
    ∑ b ∈ Finset.univ.filter (fun b => p b ≤ q b), p b ≤ bhattacharyyaCoeff p q :=
  pairwise_error_le p q hp0

/-- `p = (1/4, 3/4)` and `q = (1, 0)` on `Bool`, listing `true` first. -/
noncomputable def p₁ : Bool → ℝ := fun b => if b then 1 / 4 else 3 / 4

/-- See `p₁`. -/
noncomputable def q₁ : Bool → ℝ := fun b => if b then 1 else 0

/-- The region where `q₁ ≥ p₁` is `{true}`, of `p₁`-mass `1/4`. -/
theorem mass_p₁_q₁ : ∑ b ∈ Finset.univ.filter (fun b => p₁ b ≤ q₁ b), p₁ b = 1 / 4 := by
  rw [Finset.sum_filter, Fintype.sum_bool]
  norm_num [p₁, q₁]

/-- The bound applied to `p₁` and `q₁`: the Bhattacharyya coefficient `1/2` bounds the mass
`1/4`. -/
example : (1 / 4 : ℝ) ≤ bhattacharyyaCoeff p₁ q₁ :=
  mass_p₁_q₁ ▸ pairwise_error_le p₁ q₁ fun b => by cases b <;> norm_num [p₁]

end MathlibExtTest.InformationTheory.PairwiseBound

end
