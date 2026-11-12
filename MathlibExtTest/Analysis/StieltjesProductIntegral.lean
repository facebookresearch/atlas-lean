/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.StieltjesProductIntegral
import Mathlib.Tactic

namespace MetaMathlibExt

open Filter Topology Finset MathlibExt.Analysis.StieltjesProductIntegral

/-- `prev` picks the left neighbour inside a finite set. -/
example : prev {0, 1, 2} 2 = 1 :=
  prev_eq_of (by simp) (by norm_num) (by simp)

/-- The minimum of a finite set is its own left neighbour. -/
example : prev {0, 1, 2} 0 = 0 :=
  prev_eq_self (by simp)

/-- The coarsest partition of `[0, 1]` is `{0, 1}`. -/
example : partitionPts 0 1 ∅ = {0, 1} :=
  partitionPts_empty

/-- Interior points of `s` are added to the partition; outside points are ignored. -/
example : (1 / 2 : ℝ) ∈ partitionPts 0 1 {1 / 2, 3} ∧ (3 : ℝ) ∉ partitionPts 0 1 {1 / 2, 3} := by
  constructor <;> simp [mem_partitionPts]; norm_num

/-- A grid product over a pair is one factor `1 + ΔA`. -/
example (A : ℝ → ℝ) : gridProd A {0, 1} = 1 + (A 1 - A 0) :=
  gridProd_pair A zero_le_one

/-- The partition product for the trivial partition. -/
example (A : ℝ → ℝ) : partitionProd A 0 1 ∅ = 1 + (A 1 - A 0) :=
  partitionProd_empty A zero_le_one

/-- The identity is its own monotone control. -/
example : IsControl id id 0 1 :=
  isControl_self_of_monotoneOn (monotone_id.monotoneOn _)

/-- Every function of bounded variation has a control, hence a product integral. -/
example (A : ℝ → ℝ) (h : BoundedVariationOn A (Set.Icc 0 1)) :
    Tendsto (partitionProd A 0 1) atTop (𝓝 (productIntegral A 0 1)) :=
  tendsto_partitionProd_of_boundedVariationOn zero_le_one h

/-- Non-vacuity: `∏_{(0,1]} (1 + dt)` lies in `[2, e]` (its value is `e`). -/
example : 2 ≤ productIntegral id 0 1 ∧ productIntegral id 0 1 ≤ Real.exp 1 := by
  have hc : IsControl id id 0 1 := isControl_self_of_monotoneOn (monotone_id.monotoneOn _)
  constructor
  · have := one_add_sub_le_productIntegral zero_le_one (monotone_id.monotoneOn (s := Set.Icc 0 1))
    simpa [one_add_one_eq_two] using this
  · simpa using productIntegral_le_exp zero_le_one hc

/-- A single Kaplan–Meier-style jump of `-1/2` at `t = 1/2` gives survival `1/2`. -/
example : productIntegral (fun t => if (1 / 2 : ℝ) ≤ t then (-1 / 2 : ℝ) else 0) 0 1 = 1 / 2 := by
  rw [productIntegral_step (by norm_num) (by norm_num)]
  norm_num

/-- A constant integrator has product integral `1`, also on a degenerate interval. -/
example (c : ℝ) : productIntegral (fun _ => c) 0 1 = 1 ∧ productIntegral id 3 3 = 1 :=
  ⟨productIntegral_const c 0 1, productIntegral_self id 3⟩

/-- Multiplicativity on `[0, 1/2] ∪ [1/2, 1]`. -/
example (A V : ℝ → ℝ) (hc : IsControl A V 0 1) :
    productIntegral A 0 1 = productIntegral A 0 (1 / 2) * productIntegral A (1 / 2) 1 :=
  productIntegral_mul (by norm_num) (by norm_num) hc

/-- The majorant inequality for a refinement. -/
example (A V : ℝ → ℝ) (hc : IsControl A V 0 1) :
    |partitionProd A 0 1 {1 / 2} - partitionProd A 0 1 ∅| ≤
      partitionProd V 0 1 {1 / 2} - partitionProd V 0 1 ∅ :=
  abs_partitionProd_sub_le_of_subset zero_le_one hc (empty_subset _)

/-- The Duhamel sums converge to the difference of product integrals. -/
example (A B V W : ℝ → ℝ) (hA : IsControl A V 0 1) (hB : IsControl B W 0 1) :
    Tendsto (duhamelSum A B 0 1) atTop (𝓝 (productIntegral B 0 1 - productIntegral A 0 1)) :=
  tendsto_duhamelSum zero_le_one hA hB

/-- The exact Duhamel identity on the trivial partition `{0, 1}`. -/
example (A B V W : ℝ → ℝ) (hA : IsControl A V 0 1) (hB : IsControl B W 0 1) :
    productIntegral B 0 1 - productIntegral A 0 1 =
      ∑ x ∈ partitionPts 0 1 ∅,
        productIntegral A 0 (prev (partitionPts 0 1 ∅) x) *
          (productIntegral B (prev (partitionPts 0 1 ∅) x) x -
            productIntegral A (prev (partitionPts 0 1 ∅) x) x) *
          productIntegral B x 1 :=
  productIntegral_sub_eq_sum zero_le_one hA hB ∅

/-- The forward Volterra equation for the identity integrator. -/
example : Tendsto (fun s => ∑ x ∈ partitionPts 0 1 s,
      productIntegral id 0 (prev (partitionPts 0 1 s) x) * (x - prev (partitionPts 0 1 s) x))
      atTop (𝓝 (productIntegral id 0 1 - 1)) :=
  tendsto_volterra_forward zero_le_one (isControl_self_of_monotoneOn (monotone_id.monotoneOn _))

end MetaMathlibExt
