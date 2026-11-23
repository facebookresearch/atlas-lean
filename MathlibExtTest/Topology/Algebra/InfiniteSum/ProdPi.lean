/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Algebra.InfiniteSum.ProdPi
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Tests for `MetaMathlibExt.hasSum_prod_pi`. -/

@[expose] public section

open MetaMathlibExt

namespace MathlibExtTest.Topology.Algebra.InfiniteSum.ProdPi

/-- The geometric law `k ↦ 2^{-(k + 1)}` on `ℕ` sums to `1`. -/
theorem hasSum_half_pow_succ : HasSum (fun k : ℕ => ((1 : ℝ) / 2) ^ (k + 1)) 1 := by
  have h := hasSum_geometric_two.mul_left ((1 : ℝ) / 2)
  rw [show (1 : ℝ) / 2 * 2 = 1 by norm_num] at h
  exact h.congr_fun fun k => by ring

/-- Two independent geometric coordinates: `∑_{x : Fin 2 → ℕ} ∏ i, 2^{-(x i + 1)} = 1`. -/
example : HasSum (fun x : Fin 2 → ℕ => ∏ i, ((1 : ℝ) / 2) ^ (x i + 1)) 1 := by
  simpa using hasSum_prod_pi (f := fun (_ : Fin 2) (k : ℕ) => ((1 : ℝ) / 2) ^ (k + 1))
    (a := fun _ => 1) (fun _ _ => by positivity) fun _ => hasSum_half_pow_succ

/-- Different factors: the sums `2` (of `2^{-k}`) and `1` (of `2^{-(k + 1)}`) multiply. -/
example : HasSum (fun x : Bool → ℕ =>
    ((1 : ℝ) / 2) ^ x true * ((1 : ℝ) / 2) ^ (x false + 1)) 2 := by
  have h := hasSum_prod_pi
    (f := fun (b : Bool) (k : ℕ) => if b then ((1 : ℝ) / 2) ^ k else ((1 : ℝ) / 2) ^ (k + 1))
    (a := fun b => if b then 2 else 1) (fun b k => by cases b <;> positivity)
    fun b => by cases b
                · exact hasSum_half_pow_succ
                · exact hasSum_geometric_two
  simpa [Fintype.prod_bool, mul_comm] using h

/-- An empty index type: the function space has one point and the product is `1`. -/
example (f : Empty → ℕ → ℝ) : HasSum (fun x : Empty → ℕ => ∏ i, f i (x i)) 1 := by
  have h := hasSum_prod_pi (f := f) (a := fun _ => 0) (fun i => i.elim) (fun i => i.elim)
  rwa [Fintype.prod_empty] at h

end MathlibExtTest.Topology.Algebra.InfiniteSum.ProdPi
