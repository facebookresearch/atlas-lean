/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.LagrangeDuality
import Mathlib.Analysis.Calculus.FDeriv.Add

namespace MathlibExt.Analysis.Convex.LagrangeDuality

/-! The problem `minimize x subject to 1 - x ≤ 0` over `ℝ`, with optimal value `1`. -/

private def f₀ : ℝ → ℝ := fun x => x
private def f : Unit → ℝ → ℝ := fun _ x => 1 - x

private theorem hf₀ : ConvexOn ℝ Set.univ f₀ := convexOn_id convex_univ
private theorem hf : ∀ i, ConvexOn ℝ Set.univ (f i) := fun _ =>
  ((concaveOn_id convex_univ).neg.add (convexOn_const 1 convex_univ)).congr
    fun x _ => by simp [f]; ring
private theorem hslater : ∃ x ∈ (Set.univ : Set ℝ), ∀ i, f i x < 0 :=
  ⟨2, Set.mem_univ _, fun _ => by norm_num [f]⟩

-- The KKT conditions hold at `x = 1` with multiplier `μ = 1`, certifying `p⋆ = d⋆ = 1`.
example : primalValue Set.univ f₀ f = 1 ∧ dualFunction Set.univ f₀ f (fun _ => 1) = 1 := by
  obtain ⟨-, hg, hp⟩ := kkt_sufficient (f₀' := ContinuousLinearMap.id ℝ ℝ)
    (f' := fun _ => -ContinuousLinearMap.id ℝ ℝ) (x := (1 : ℝ)) (μ := fun _ => 1)
    hf₀ hf (Set.mem_univ _) (hasFDerivAt_id 1)
    (fun _ => (hasFDerivAt_id (1 : ℝ)).const_sub 1)
    (fun _ => by norm_num [f]) (fun _ => zero_le_one) (fun _ => by norm_num [f])
    (by ext; simp)
  exact ⟨by simpa [f₀] using hp, by simpa [f₀] using hg⟩

-- Strong duality: Slater's condition holds (at `x = 2`), so `d⋆ = p⋆`.
example : dualValue Set.univ f₀ f = primalValue Set.univ f₀ f :=
  dualValue_eq_primalValue_of_slater hf₀ hf hslater

-- The central point `x = 1 + 1 / t` for `t = 1`, i.e. `x = 2`, is at most `m / t = 1`
-- suboptimal, with dual certificate `μ = -1 / (t (1 - x)) = 1`.
example : ∀ y : ℝ, 1 - y ≤ 0 → (2 : ℝ) - 1 ≤ y := by
  obtain ⟨-, -, hgap⟩ := central_point_duality_gap (f₀' := ContinuousLinearMap.id ℝ ℝ)
    (f' := fun _ => -ContinuousLinearMap.id ℝ ℝ) (x := (2 : ℝ)) (t := 1)
    hf₀ hf (Set.mem_univ _) (hasFDerivAt_id 2)
    (fun _ => (hasFDerivAt_id (2 : ℝ)).const_sub 1)
    (fun _ => by norm_num [f]) one_pos (by ext; norm_num [f])
  intro y hy
  simpa [f₀, f] using hgap y (Set.mem_univ _) (fun _ => hy)

-- Weak duality needs no convexity: any `μ ≥ 0` gives a lower bound.
example (μ : Unit → ℝ) (hμ : 0 ≤ μ) :
    dualFunction Set.univ f₀ f μ ≤ primalValue Set.univ f₀ f :=
  (le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : Unit → ℝ | 0 ≤ μ}) => dualFunction Set.univ f₀ f μ)
    μ hμ le_rfl).trans (dualValue_le_primalValue _ _ _)

end MathlibExt.Analysis.Convex.LagrangeDuality
