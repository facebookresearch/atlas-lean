/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Polynomial_aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero.lean`
and
`P2M/Sol/S_Polynomial_aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Instances.Complex
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Filter Topology

namespace Polynomial

/-- A polynomial that annihilates the matrix polynomial
`∑ a, y ^ a • N a` at every positive real parameter `y` also annihilates
its constant term `N 0`.

The matrix polynomial is continuous in `y` and agrees with `N 0` at
`y = 0`, so the conclusion follows by continuity of `Polynomial.aeval`
and uniqueness of limits along `𝓝[>] 0`. -/
public theorem aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero
    (R D : ℕ) (N : Fin (D + 1) → Matrix (Fin R) (Fin R) ℂ) (q : Polynomial ℂ)
    (h : ∀ y : ℝ, 0 < y →
      Polynomial.aeval (∑ a : Fin (D + 1), ((y : ℂ) ^ (a : ℕ)) • N a) q = 0) :
    Polynomial.aeval (N 0) q = 0 := by
  let S : ℝ → Matrix (Fin R) (Fin R) ℂ :=
    fun y => ∑ a : Fin (D + 1), ((y : ℂ) ^ (a : ℕ)) • N a
  have hS : Continuous S := by
    apply continuous_finsetSum
    intro a _
    exact ((Complex.continuous_ofReal.pow _).smul continuous_const)
  let f : ℝ → Matrix (Fin R) (Fin R) ℂ := fun y => Polynomial.aeval (S y) q
  have hf : Continuous f := (Polynomial.continuous_aeval q).comp hS
  have hS0 : S 0 = N 0 := by
    change ∑ a : Fin (D + 1), (((0 : ℝ) : ℂ) ^ (a : ℕ)) • N a = N 0
    rw [Fin.sum_univ_succ]
    simp
  have h1 : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
    hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (h y hy).symm
  have h3 : f 0 = 0 := tendsto_nhds_unique h1 h2
  have hf0 : f 0 = Polynomial.aeval (N 0) q := by
    change Polynomial.aeval (S 0) q = _
    rw [hS0]
  rw [← hf0, h3]

end Polynomial
