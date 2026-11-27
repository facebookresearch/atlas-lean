/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.WeakSolutions

import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Tests for weak solutions from the Lax–Milgram theorem

* With `D` the identity of `ℝ²` and `β = 1`, every bounded linear functional has a unique weak
  solution, and the weak solution for `L = 0` is `0`.
* Dirichlet's principle on `ℝ` for `B[u, v] = u v` and `L v = 3 v`: `u = 3` minimizes the energy.
-/

open MathlibExt.Analysis.PDE.WeakSolutions
open scoped RealInnerProductSpace

example (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) :
    ∃! u : EuclideanSpace ℝ (Fin 2),
      ∀ v, ⟪ContinuousLinearMap.id ℝ _ u, ContinuousLinearMap.id ℝ _ v⟫ = L v :=
  existsUnique_weakSolution one_pos (fun u => by simp) L

example : ‖(0 : EuclideanSpace ℝ (Fin 2))‖ ≤ ‖(0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ / 1 :=
  norm_le_of_weakSolution (D := ContinuousLinearMap.id ℝ _) one_pos (fun u => by simp)
    (fun v => by simp)

example (w : ℝ) :
    energy (ContinuousLinearMap.mul ℝ ℝ) (3 • ContinuousLinearMap.id ℝ ℝ) 3 ≤
      energy (ContinuousLinearMap.mul ℝ ℝ) (3 • ContinuousLinearMap.id ℝ ℝ) w :=
  (isMinOn_energy_iff (fun u v => mul_comm u v) (fun v => mul_self_nonneg v) _ 3).mpr
    (fun v => by simp) w
