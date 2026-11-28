/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.LanderGreenTransitionKroneckerStochastic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-! # Tests for the Kronecker form and stochasticity of the transition

Each conjunct of `transition_kronecker_stochastic` is exercised: the Kronecker form on a
one-meiosis instance and in the no-change corollary `transition θ v v = (1 - θ) ^ n`, and
row stochasticity, symmetry and uniform stationarity on concrete instances. -/

@[expose] public section

namespace DomainsTest.Biology.StatisticalGenetics.LanderGreenTransitionKroneckerStochastic

open Finset WantedExt.Biology.StatisticalGenetics.LanderGreenWanted

/-- One meiosis, `θ = 1/4`: a certain flip has probability `1/4`. -/
example : transition (1 / 4 : ℝ) (fun _ : Fin 1 => false) (fun _ : Fin 1 => true) = 1 / 4 := by
  have h := (transition_kronecker_stochastic 1 (1 / 4) (by norm_num) (by norm_num)).1
    (fun _ : Fin 1 => false) (fun _ : Fin 1 => true)
  rw [h, Fin.prod_univ_one]
  norm_num

/-- No changes anywhere: the transition is `(1 - θ) ^ n`. -/
example (n : ℕ) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1 / 2) (v : InheritanceVector n) :
    transition θ v v = (1 - θ) ^ n := by
  have h := (transition_kronecker_stochastic n θ hθ₀ hθ₁).1 v v
  rw [h]
  simp

/-- Rows sum to `1`: two-meiosis instance. -/
example (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1 / 2) (v : InheritanceVector 2) :
    ∑ w, transition θ v w = 1 :=
  (transition_kronecker_stochastic 2 θ hθ₀ hθ₁).2.1 v

/-- Symmetry on a concrete pair. -/
example (v w : InheritanceVector 2) :
    transition (1 / 3 : ℝ) v w = transition (1 / 3) w v :=
  (transition_kronecker_stochastic 2 (1 / 3) (by norm_num) (by norm_num)).2.2.1 v w

/-- Uniform stationarity: three-meiosis instance at `θ = 1/3`. -/
example (w : InheritanceVector 3) :
    ∑ v, uniformPrior 3 * transition (1 / 3 : ℝ) v w = uniformPrior 3 :=
  (transition_kronecker_stochastic 3 (1 / 3) (by norm_num) (by norm_num)).2.2.2 w

end DomainsTest.Biology.StatisticalGenetics.LanderGreenTransitionKroneckerStochastic
