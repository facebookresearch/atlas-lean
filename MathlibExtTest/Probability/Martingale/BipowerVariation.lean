/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Martingale.BipowerVariation
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal
open MathlibExt.Probability.Martingale

namespace MathlibExtTest.Probability.Martingale.BipowerVariation

noncomputable section

/-! ### Jump robustness, from the definitions

One jump of size `1` at time `1/2`, observed on the grid of mesh `1/4`. The jump falls in the
cell `(1/4, 1/2]`. Realized variance sees it; bipower variation does not. -/

/-- The increments of the path with one jump of size `1` at time `1/2`. -/
def oneJump (n i : ℕ) : ℝ := jumpIncrement {0} (fun _ : ℕ => (1 / 2 : ℝ)) (fun _ => 1) n i

lemma oneJump_four :
    oneJump 4 0 = 0 ∧ oneJump 4 1 = 1 ∧ oneJump 4 2 = 0 ∧ oneJump 4 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [oneJump, jumpIncrement, jumpPath]

-- Realized variance of the four increments is the squared jump, `1`.
example : ∑ i ∈ Finset.range 4, oneJump 4 i ^ 2 = 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := oneJump_four
  simp [Finset.sum_range_succ, h0, h1, h2, h3]

-- Bipower variation of the same four increments is `0`.
example : bipowerVariation (oneJump 4) 3 = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := oneJump_four
  simp [bipowerVariation, Finset.sum_range_succ, h0, h1, h2, h3]

/-! ### Boundary: the jump-separation hypothesis cannot be dropped

Jumps of size `1` at times `3/10` and `6/10` are `3/10` apart. On the grid of mesh `1/4`
(`2/n = 1/2 > 3/10`) they fall in the adjacent cells `(1/4, 1/2]` and `(1/2, 3/4]`, and the
bipower variation of the jump increments alone is `1`: with zero continuous part (`M = 0`) the
bound `2 M ∑ₖ |ξ k| = 0` of `abs_bipowerVariation_add_jumpIncrement_sub_le` fails. On the grid
of mesh `1/8` (`2/n = 1/4 < 3/10`) the cells `(1/4, 3/8]` and `(1/2, 5/8]` are not adjacent and
the bipower variation is `0`, as `eventually_jumpIncrement_mul_succ_eq_zero` predicts. -/

/-- The jump times `3/10` and `6/10`. -/
def twoTimes (k : ℕ) : ℝ := if k = 0 then 3 / 10 else 6 / 10

/-- The increments of the path with jumps of size `1` at times `3/10` and `6/10`. -/
def twoJumps (n i : ℕ) : ℝ := jumpIncrement {0, 1} twoTimes (fun _ => 1) n i

lemma twoJumps_four :
    twoJumps 4 0 = 0 ∧ twoJumps 4 1 = 1 ∧ twoJumps 4 2 = 1 ∧ twoJumps 4 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [twoJumps, jumpIncrement, jumpPath, Finset.sum_pair (show (0 : ℕ) ≠ 1 by norm_num)]
     norm_num [twoTimes])

example : bipowerVariation (twoJumps 4) 3 = 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := twoJumps_four
  simp [bipowerVariation, Finset.sum_range_succ, h0, h1, h2, h3]

-- The separation hypothesis fails at `n = 4`, and so does the conclusion with `c = 0`, `M = 0`.
example : ¬ (2 / ((4 : ℕ) : ℝ) ≤ |twoTimes 0 - twoTimes 1|) := by
  norm_num [twoTimes, abs_of_neg]

example : ¬ (|bipowerVariation (fun i => (0 : ℝ) + twoJumps 4 i) 3 -
    bipowerVariation (fun _ => (0 : ℝ)) 3| ≤ 2 * 0 * ∑ _k ∈ ({0, 1} : Finset ℕ), |(1 : ℝ)|) := by
  obtain ⟨h0, h1, h2, h3⟩ := twoJumps_four
  simp [bipowerVariation, Finset.sum_range_succ, h0, h1, h2, h3]

lemma twoJumps_eight : twoJumps 8 0 = 0 ∧ twoJumps 8 1 = 0 ∧ twoJumps 8 2 = 1 ∧
    twoJumps 8 3 = 0 ∧ twoJumps 8 4 = 1 ∧ twoJumps 8 5 = 0 ∧ twoJumps 8 6 = 0 ∧
    twoJumps 8 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [twoJumps, jumpIncrement, jumpPath, Finset.sum_pair (show (0 : ℕ) ≠ 1 by norm_num)]
     norm_num [twoTimes])

example : bipowerVariation (twoJumps 8) 7 = 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := twoJumps_eight
  simp [bipowerVariation, Finset.sum_range_succ, h0, h1, h2, h3, h4, h5, h6, h7]

/-! ### Boundary values of the definitions -/

-- With no increments past the first, bipower variation is the empty sum.
example (d : ℕ → ℝ) : bipowerVariation d 0 = 0 := by simp [bipowerVariation]

-- On the degenerate grid `n = 0` every cell is empty and every jump increment is `0`.
example {ι : Type*} (s : Finset ι) (τ ξ : ι → ℝ) (i : ℕ) : jumpIncrement s τ ξ 0 i = 0 := by
  simp [jumpIncrement]

-- Bipower variation of `(1, 2, 3)`: `|1| |2| + |2| |3| = 8`.
example : bipowerVariation (fun i => (i : ℝ) + 1) 2 = 8 := by
  norm_num [bipowerVariation, Finset.sum_range_succ]

/-! ### Non-vacuity: Brownian increments with a jump

On `ℝ^ℕ` with the product of standard Gaussians, the coordinates are i.i.d. `N(0,1)`, checked
from Mathlib's `iIndepFun_infinitePi` and `infinitePi_map_eval`, not through the theorem. Every
row of the array `Z n i ω = ω i` is that i.i.d. sequence. Adding one jump of size `5` at time
`1/2`, `tendstoInMeasure_bipowerVariation_add_jump_gaussian` gives `BPV → (2/π) σ²`. -/

example (σ : ℝ) :
    TendstoInMeasure (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (fun (n : ℕ) (ω : ℕ → ℝ) => bipowerVariation (fun i => σ / Real.sqrt n * ω i +
        jumpIncrement (Finset.range 1) (fun _ => (1 / 2 : ℝ)) (fun _ => (5 : ℝ)) n i) (n - 1))
      atTop (fun _ => 2 / Real.pi * σ ^ 2) :=
  tendstoInMeasure_bipowerVariation_add_jump_gaussian
    (μ := Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) (Z := fun _ i ω => ω i)
    (fun _ i => measurable_pi_apply i)
    (fun _ => iIndepFun_infinitePi (X := fun (_ : ℕ) (x : ℝ) => x) fun _ => measurable_id)
    (fun _ i => Measure.infinitePi_map_eval _ i) σ (K := fun _ => 1) (τ := fun _ _ => 1 / 2)
    (ξ := fun _ _ => 5) measurable_const (fun _ => measurable_const) (fun _ => measurable_const)
    (ae_of_all _ fun _ a ha b hb _ => by
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      omega)

end

end MathlibExtTest.Probability.Martingale.BipowerVariation
