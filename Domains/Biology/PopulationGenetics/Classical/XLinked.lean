/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecificLimits.Normed

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# X-linked allele frequency dynamics

For an X-linked biallelic locus with no selection, mutation, migration, or drift, write
`(p_f, p_m)` for the allele frequencies in females and males. One generation is

`p_f' = (p_f + p_m) / 2`, `p_m' = p_f`.

The weighted mean `p̄ = (2 p_f + p_m) / 3` is invariant, the sex difference
`p_f - p_m` is multiplied by `-1 / 2` each generation, and both frequencies converge
geometrically to `p̄`, with oscillation.

## Main results

* `XLinked.pbar_step`, `XLinked.pbar_iterate`: invariance of the weighted mean.
* `XLinked.sub_step`, `XLinked.sub_iterate`: the sex difference scales by `-1 / 2`.
* `XLinked.fst_iterate_sub_pbar`, `XLinked.snd_iterate_sub_pbar`: closed forms.
* `XLinked.tendsto_fst_iterate`, `XLinked.tendsto_snd_iterate`: convergence to `p̄`.

## References

* J. Felsenstein, *Theoretical Evolutionary Genetics*, §I.9, eqs. (I-36)–(I-40).
-/

@[expose] public section

open Filter Topology

namespace MathlibExt.Biology.PopulationGenetics.Classical.XLinked

/-- One generation of X-linked transmission: daughters receive one X from each parent, sons
receive their X from the mother. `x.1 = p_f`, `x.2 = p_m`. -/
noncomputable def step (x : ℝ × ℝ) : ℝ × ℝ := ((x.1 + x.2) / 2, x.1)

/-- The weighted mean `p̄ = (2 p_f + p_m) / 3`. With equal positive numbers of females and males it
is the allele frequency among all X chromosomes, each counted once; with `F` females and `M`
males, when `2F + M > 0`, that frequency is `(2F p_f + M p_m) / (2F + M)` instead. -/
noncomputable def pbar (x : ℝ × ℝ) : ℝ := (2 * x.1 + x.2) / 3

@[simp] theorem step_fst (x : ℝ × ℝ) : (step x).1 = (x.1 + x.2) / 2 := rfl
@[simp] theorem step_snd (x : ℝ × ℝ) : (step x).2 = x.1 := rfl

/-- `p̄` is invariant. -/
theorem pbar_step (x : ℝ × ℝ) : pbar (step x) = pbar x := by
  simp only [pbar, step_fst, step_snd]; ring

theorem pbar_iterate (x : ℝ × ℝ) (t : ℕ) : pbar (step^[t] x) = pbar x := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', pbar_step, ih]

/-- The sex difference `p_f - p_m` is multiplied by `-1/2` each generation. -/
theorem sub_step (x : ℝ × ℝ) : (step x).1 - (step x).2 = (-1 / 2) * (x.1 - x.2) := by
  simp only [step_fst, step_snd]; ring

theorem sub_iterate (x : ℝ × ℝ) (t : ℕ) :
    (step^[t] x).1 - (step^[t] x).2 = (-1 / 2) ^ t * (x.1 - x.2) := by
  induction t with
  | zero => simp
  | succ t ih => rw [Function.iterate_succ_apply', sub_step, ih, pow_succ]; ring

/-- Closed form, females: `p_f(t) - p̄ = (-1/2)^t (p_f(0) - p̄)`. -/
theorem fst_iterate_sub_pbar (x : ℝ × ℝ) (t : ℕ) :
    (step^[t] x).1 - pbar x = (-1 / 2) ^ t * (x.1 - pbar x) := by
  have h1 := pbar_iterate x t
  have h2 := sub_iterate x t
  simp only [pbar] at h1 ⊢
  have hlin : (step^[t] x).1 - (2 * x.1 + x.2) / 3 =
      ((step^[t] x).1 - (step^[t] x).2) / 3 := by linarith
  rw [hlin, h2]; ring

/-- Closed form, males: `p_m(t) - p̄ = (-1/2)^t (p_m(0) - p̄)`. -/
theorem snd_iterate_sub_pbar (x : ℝ × ℝ) (t : ℕ) :
    (step^[t] x).2 - pbar x = (-1 / 2) ^ t * (x.2 - pbar x) := by
  have h1 := pbar_iterate x t
  have h2 := sub_iterate x t
  simp only [pbar] at h1 ⊢
  have hlin : (step^[t] x).2 - (2 * x.1 + x.2) / 3 =
      -2 * ((step^[t] x).1 - (step^[t] x).2) / 3 := by linarith
  rw [hlin, h2]; ring

theorem tendsto_fst_iterate (x : ℝ × ℝ) :
    Tendsto (fun t : ℕ => (step^[t] x).1) atTop (𝓝 (pbar x)) := by
  have h : Tendsto (fun t : ℕ => (-1 / 2 : ℝ) ^ t * (x.1 - pbar x) + pbar x) atTop
      (𝓝 (0 * (x.1 - pbar x) + pbar x)) :=
    ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)).mul_const _).add_const _
  rw [zero_mul, zero_add] at h
  refine h.congr fun t => ?_
  linarith [fst_iterate_sub_pbar x t]

theorem tendsto_snd_iterate (x : ℝ × ℝ) :
    Tendsto (fun t : ℕ => (step^[t] x).2) atTop (𝓝 (pbar x)) := by
  have h : Tendsto (fun t : ℕ => (-1 / 2 : ℝ) ^ t * (x.2 - pbar x) + pbar x) atTop
      (𝓝 (0 * (x.2 - pbar x) + pbar x)) :=
    ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)).mul_const _).add_const _
  rw [zero_mul, zero_add] at h
  refine h.congr fun t => ?_
  linarith [snd_iterate_sub_pbar x t]

end MathlibExt.Biology.PopulationGenetics.Classical.XLinked
