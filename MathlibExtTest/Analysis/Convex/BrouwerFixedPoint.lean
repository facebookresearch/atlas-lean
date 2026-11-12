/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.BrouwerFixedPoint

/-! `x ↦ 1 - x` on `[0, 1]` has a fixed point by Brouwer's theorem (it is `1/2`), and every
continuous self-map of the two-vertex simplex has one. Each hypothesis matters: `x ↦ 1 - x` on the
nonconvex `{0, 1}`, `x ↦ x + 1` on the noncompact `[0, ∞)`, and a discontinuous jump on `[0, 1]`
have no fixed point. -/

@[expose] public section

open MathlibExt.Analysis.Convex.BrouwerFixedPoint

namespace MathlibExtTest.Analysis.Convex.BrouwerFixedPoint

/-- The map `x ↦ 1 - x` on `[0, 1]` has a fixed point, via `exists_fixedPoint`. -/
example : ∃ x ∈ Set.Icc (0 : ℝ) 1, 1 - x = x := by
  have hKc : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have hKcv : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  have hKne : (Set.Icc (0 : ℝ) 1).Nonempty := Set.nonempty_Icc.mpr (by norm_num)
  have hf : ContinuousOn (fun x : ℝ => 1 - x) (Set.Icc (0 : ℝ) 1) :=
    (continuous_const.sub continuous_id).continuousOn
  have hfK : Set.MapsTo (fun x : ℝ => 1 - x) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [Set.mem_Icc] at hx ⊢
    constructor <;> linarith
  obtain ⟨x, hxK, hfix⟩ := exists_fixedPoint hKc hKcv hKne hf hfK
  exact ⟨x, hxK, hfix⟩

/-- Every continuous self-map of the 2-vertex simplex has a fixed point. -/
example (f : Convexity.StdSimplex ℝ (Fin 2) → Convexity.StdSimplex ℝ (Fin 2))
    (hf : Continuous f) : ∃ x, f x = x :=
  exists_fixedPoint_stdSimplex (n := 1) f hf

example (hKKM : KKMProperty) : ∃ x ∈ Set.Icc (0 : ℝ) 1, 1 - x = x := by
  obtain ⟨x, hxK, hfx⟩ := exists_fixedPoint_of_kkm hKKM (K := Set.Icc (0 : ℝ) 1)
    (f := fun x => 1 - x) isCompact_Icc (convex_Icc 0 1)
    (Set.nonempty_Icc.mpr (by norm_num)) (continuous_const.sub continuous_id).continuousOn
    (fun x hx => by
      simp only [Set.mem_Icc] at hx ⊢
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  exact ⟨x, hxK, hfx⟩

example : ∃ x ∈ Set.Icc (0 : ℝ) 1, 1 - x = x ∧ x = 1 / 2 :=
  ⟨1 / 2, by norm_num [Set.mem_Icc], by norm_num, rfl⟩

example : ¬ ∃ x ∈ ({0, 1} : Set ℝ), 1 - x = x := by
  rintro ⟨x, hx, hfx⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> norm_num at hfx

example : ¬ ∃ x ∈ Set.Ici (0 : ℝ), x + 1 = x := by
  rintro ⟨x, hx, hfx⟩
  have h10 : (1:ℝ) = 0 := by linarith [hfx]
  norm_num at h10

example : ¬ ∃ x ∈ Set.Icc (0 : ℝ) 1, (if x < 1 / 2 then (1 : ℝ) else 0) = x := by
  rintro ⟨x, hx, hfx⟩
  simp only [Set.mem_Icc] at hx
  split_ifs at hfx with h
  · linarith [hx.1, hx.2]
  · linarith [hx.1, hx.2]

end MathlibExtTest.Analysis.Convex.BrouwerFixedPoint
