/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.FDivergence
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open MathlibExt.InformationTheory.FDivergence Finset Real

/-- Nonnegativity for `f(t) = t log t` (Gibbs' inequality): `P = (1/4, 3/4)` against the uniform
law on `Bool`. -/
example : 0 ≤ fDiv (fun t : ℝ => t * log t) (fun b : Bool => if b then 3 / 4 else 1 / 4)
    (fun _ => 1 / 2) :=
  fDiv_nonneg Real.convexOn_mul_log (by simp) (fun b => by cases b <;> norm_num)
    (fun _ => by norm_num) (by simp; norm_num) (by norm_num)

/-- Lumping `Bool` to a point never increases an f-divergence. -/
example : fDiv (fun t : ℝ => t * log t)
      (lump (fun _ : Bool => ()) fun b : Bool => if b then 3 / 4 else 1 / 4)
      (lump (fun _ : Bool => ()) fun _ => 1 / 2) ≤
    fDiv (fun t : ℝ => t * log t) (fun b : Bool => if b then 3 / 4 else 1 / 4)
      (fun _ => 1 / 2) :=
  fDiv_map_le Real.convexOn_mul_log (fun b => by cases b <;> norm_num) (fun _ => by norm_num) _

/-- The I-divergence as the f-divergence of `t log t`. -/
example (P : Bool → ℝ) :
    fDiv (fun t => t * log t) P (fun _ => 1 / 2) = ∑ a, P a * log (P a / (1 / 2)) :=
  fDiv_mul_log fun _ => by norm_num
