/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PathSignature.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Algebra.BigOperators.Fin

import MathlibExt.Analysis.ODE.PicardIteration
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Linear controlled differential equations are solved by the signature

For linear maps `A_i : E → E` and a path `X` in `ℝ^ι` with velocity `v`, the linear controlled
differential equation `dy_t = ∑_i A_i y_t dXⁱ_t` has the Picard iterates

`y^{(n)}_t = ∑_{|w| ≤ n} S(X)^w_{s,t} · A_w y_s`, `A_{i₁…i_k} = A_{i_k} ∘ ⋯ ∘ A_{i₁}`,

so its solution is the signature series `∑_w S(X)^w_{s,t} A_w y_s` (T. Lyons, *Rough paths,
signatures and the modelling of functions on streams*, Proc. ICM 2014, arXiv:1405.4537, §4.2,
equation (1)): the signature is the universal object through which a path drives every linear
system. We prove the Picard recursion for the truncated signature series and, for a bounded
continuous velocity, its convergence to the solution, using the repository's Picard iteration
theorem.
-/

open MeasureTheory intervalIntegral

@[expose] public section

namespace MathlibExt.Analysis.PathSignature

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Composite linear map along a word.** For a family `A : ι → (E →L[ℝ] E)` and a word
`w = i₁…i_k`, `wordOp A w = A_{i_k} ∘ ⋯ ∘ A_{i₁}` (the identity for the empty word): the letters
act in the order in which the path visits them. -/
noncomputable def wordOp (A : ι → E →L[ℝ] E) (w : List ι) : E →L[ℝ] E :=
  w.foldl (fun L i => (A i).comp L) (ContinuousLinearMap.id ℝ E)

@[simp] theorem wordOp_nil (A : ι → E →L[ℝ] E) : wordOp A [] = ContinuousLinearMap.id ℝ E := rfl

theorem wordOp_concat (A : ι → E →L[ℝ] E) (w : List ι) (i : ι) :
    wordOp A (w ++ [i]) = (A i).comp (wordOp A w) := by
  simp [wordOp, List.foldl_append]

/-- **Truncated signature series of a linear controlled equation.** The degree-`n` truncation
`∑_{k ≤ n} ∑_{|w| = k} S(X)^w_{s,t} · A_w y₀` of the solution of `dy = ∑_i A_i y dXⁱ`,
`y_s = y₀` (T. Lyons, Proc. ICM 2014, arXiv:1405.4537, §4.2, equation (1)). -/
noncomputable def signatureSeries [Fintype ι] (A : ι → E →L[ℝ] E) (v : ι → ℝ → ℝ) (s : ℝ)
    (y₀ : E) (n : ℕ) (t : ℝ) : E :=
  ∑ k ∈ Finset.range (n + 1), ∑ g : Fin k → ι,
    signature v s t (List.ofFn g) • wordOp A (List.ofFn g) y₀

/-- **Picard recursion of the signature series.** For a path with continuous velocity, the
truncated signature series satisfy the Picard recursion of the linear controlled equation
`dy_t = ∑_i vⁱ(t) A_i y_t dt`: `y^{(0)} = y₀` and
`y^{(n+1)}_t = y₀ + ∫_s^t ∑_i vⁱ(r) A_i y^{(n)}_r dr`. Hence the Picard iterates of the equation
are exactly the truncated signature series (T. Lyons, *Rough paths, signatures and the modelling of
functions on streams*, Proc. ICM 2014, arXiv:1405.4537, §4.2: "By iterating using Picard iteration
one obtains" equation (1)). -/
theorem signatureSeries_succ [Fintype ι] [CompleteSpace E] (A : ι → E →L[ℝ] E) {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (s : ℝ) (y₀ : E) (n : ℕ) (t : ℝ) :
    signatureSeries A v s y₀ (n + 1) t =
      y₀ + ∫ r in s..t, ∑ i, v i r • A i (signatureSeries A v s y₀ n r) := by
  have hcont : ∀ w : List ι, Continuous fun t => signature v s t w :=
    continuous_signature (fun i a b => (hv i).intervalIntegrable a b) s
  -- Expand the right-hand side into a finite sum of integrals.
  have hrhs : ∫ r in s..t, ∑ i, v i r • A i (signatureSeries A v s y₀ n r) =
      ∑ k ∈ Finset.range (n + 1), ∑ i, ∑ g : Fin k → ι,
        (∫ r in s..t, signature v s r (List.ofFn g) * v i r) •
          A i (wordOp A (List.ofFn g) y₀) := by
    have hexp : ∀ r, ∑ i, v i r • A i (signatureSeries A v s y₀ n r) =
        ∑ k ∈ Finset.range (n + 1), ∑ i, ∑ g : Fin k → ι,
          (signature v s r (List.ofFn g) * v i r) • A i (wordOp A (List.ofFn g) y₀) := by
      intro r
      simp only [signatureSeries, map_sum, map_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun g _ => ?_
      rw [mul_comm]
    simp_rw [hexp]
    rw [intervalIntegral.integral_finsetSum fun k _ => ?_]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_finsetSum fun i _ => ?_]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [intervalIntegral.integral_finsetSum fun g _ => ?_]
        · exact Finset.sum_congr rfl fun g _ => intervalIntegral.integral_smul_const _ _
        · exact (((hcont _).mul (hv i)).smul continuous_const).intervalIntegrable _ _
      · exact (continuous_finsetSum _ fun g _ =>
          ((hcont _).mul (hv i)).smul continuous_const).intervalIntegrable _ _
    · exact (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun g _ =>
          ((hcont _).mul (hv i)).smul continuous_const).intervalIntegrable _ _
  rw [hrhs, signatureSeries, Finset.sum_range_succ']
  simp only [Finset.univ_unique, Finset.sum_singleton, List.ofFn_zero, signature_nil,
    wordOp_nil, ContinuousLinearMap.id_apply, one_smul]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_fin_succ_ofFn k (fun w => signature v s t w • wordOp A w y₀)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun g _ => ?_
  rw [signature_concat, wordOp_concat, ContinuousLinearMap.comp_apply]

/-- **Linear controlled equations are solved by the signature series.** Let `ι` be finite,
`A_i : E → E` continuous linear maps on a Banach space, and `v` a continuous, bounded velocity
(`|vⁱ(t)| ≤ M`). If `y` solves the linear controlled differential equation
`y'(t) = ∑_i vⁱ(t) A_i y(t)` with `y(s) = y₀`, then for every `t` the truncated signature series
`∑_{|w| ≤ n} S(X)^w_{s,t} · A_w y₀` converge to `y(t)` as `n → ∞`, i.e.
`y_t = ∑_w S(X)^w_{s,t} A_w y_s` (T. Lyons, *Rough paths, signatures and the modelling of functions
on streams*, Proc. ICM 2014, arXiv:1405.4537, §4.2, equation (1)). -/
theorem tendsto_signatureSeries [Fintype ι] [CompleteSpace E] (A : ι → E →L[ℝ] E)
    {v : ι → ℝ → ℝ} (hv : ∀ i, Continuous (v i)) {M : ℝ} (hM : ∀ i t, |v i t| ≤ M) (s : ℝ)
    (y₀ : E) (y : ℝ → E) (hy₀ : y s = y₀)
    (hy : ∀ t, HasDerivAt y (∑ i, v i t • A i (y t)) t) (t : ℝ) :
    Filter.Tendsto (fun n => signatureSeries A v s y₀ n t) Filter.atTop (nhds (y t)) := by
  set f : ℝ → E → E := fun r x => ∑ i, v i r • A i x
  have hfcont : Continuous (Function.uncurry f) := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((hv i).comp continuous_fst).smul ((A i).continuous.comp continuous_snd)
  set L : NNReal := ⟨∑ i, M * ‖A i‖, Finset.sum_nonneg fun i _ =>
    mul_nonneg ((abs_nonneg _).trans (hM i 0)) (norm_nonneg _)⟩
  have hlip : ∀ r, LipschitzWith L (f r) := by
    intro r
    refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have : f r x - f r x' = ∑ i, v i r • A i (x - x') := by
      simp [f, Finset.sum_sub_distrib, smul_sub, map_sub]
    rw [this]
    calc ‖∑ i, v i r • A i (x - x')‖ ≤ ∑ i, ‖v i r • A i (x - x')‖ := norm_sum_le _ _
      _ ≤ ∑ i, M * ‖A i‖ * ‖x - x'‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_smul, Real.norm_eq_abs, mul_assoc]
          exact mul_le_mul (hM i r) ((A i).le_opNorm _) (norm_nonneg _)
            ((abs_nonneg _).trans (hM i r))
      _ = L * ‖x - x'‖ := by
          rw [show (L : ℝ) = ∑ i, M * ‖A i‖ from rfl, Finset.sum_mul]
  refine MathlibExt.Analysis.ODE.PicardIterationWanted.picard_iterates_tendsto_of_hasDerivAt f s
    y₀ L hfcont hlip (signatureSeries A v s y₀) ?_ ?_ y hy₀ hy t
  · funext r
    simp [signatureSeries]
  · intro n r
    exact signatureSeries_succ A hv s y₀ n r

end MathlibExt.Analysis.PathSignature
