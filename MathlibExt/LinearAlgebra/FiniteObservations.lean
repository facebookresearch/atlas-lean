/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

arnovich/forseti-lean, commit
0a81edc7fe82748af7c9b1139229c4d898f50c28,
`Gimle/Forseti/FiniteLinearEquivalence.lean`. Authors: arnovich.

MIT License

Copyright (c) 2025 Gimle Labs

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite determination of linear observations

Cayley–Hamilton bounds the prefix needed to determine a scalar observation.
Unlike `LinearRecurrence.eq_iff_eqOn_range_order`, callers need not first
construct a scalar recurrence and prove that their observations satisfy it.
For two systems, the bound is the sum of their state-space dimensions.

Mathematical reference: the Cayley–Hamilton power-span argument, as in
Hank Yang, Optimal Control and Reinforcement Learning, Appendix B.2.1,
Corollary B.2 (appendix by Shucheng Kang):
https://hankyang.seas.harvard.edu/OptimalControlReinforcementLearning/app-lti-system-theory.html.
The two-system statement applies this argument to the product endomorphism
and the difference of the observations. The algebraic proof works over any field.
-/

@[expose] public section

namespace Module.End

open Polynomial

/-- Vanishing through the dimension bound forces every later observation to vanish. -/
theorem observation_zero_of_prefix
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (z : V) (ell : V →ₗ[K] K)
    (h : ∀ j < Module.finrank K V, ell ((T ^ j) z) = 0) :
    ∀ n : ℕ, ell ((T ^ n) z) = 0 := by
  classical
  by_cases hd : Module.finrank K V = 0
  · let : Subsingleton V := Module.finrank_zero_iff.mp hd
    intro n
    rw [Subsingleton.elim ((T ^ n) z) 0, map_zero]
  · have hp : T.charpoly ≠ 1 := by
      intro he
      apply hd
      rw [← T.charpoly_natDegree, he, natDegree_one]
    intro n
    have hb : (X ^ n %ₘ T.charpoly).natDegree < Module.finrank K V := by
      rw [← T.charpoly_natDegree]
      exact natDegree_modByMonic_lt _ T.charpoly_monic hp
    rw [T.pow_eq_aeval_mod_charpoly n, aeval_eq_sum_range' hb]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    apply Finset.sum_eq_zero
    intro j hj
    rw [h j (Finset.mem_range.mp hj), smul_zero]

end Module.End

namespace Matrix

variable {K : Type*} [Field K]

/-- Exact output at a natural time, with a column-state convention. -/
def observation {d : ℕ} (A : Matrix (Fin d) (Fin d) K)
    (x c : Fin d → K) (n : ℕ) : K :=
  dotProduct c ((A ^ n).mulVec x)

/-- Matrix powers act by the same iterates as their induced linear endomorphism. -/
private theorem matrix_power_action {d : ℕ} (A : Matrix (Fin d) (Fin d) K)
    (x : Fin d → K) (n : ℕ) :
    (A.mulVecLin ^ n) x = (A ^ n).mulVec x := by
  exact congrArg (fun f : Module.End K (Fin d → K) => f x)
    (Matrix.toLin'_pow A n).symm

/-- The product transition evolves both component systems at the same time. -/
private theorem product_power_action {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (T : Module.End K V) (S : Module.End K W) (x : V) (y : W) (n : ℕ) :
    (T.prodMap S ^ n) (x, y) = ((T ^ n) x, (S ^ n) y) := by
  exact congrArg (fun f : Module.End K (V × W) => f (x, y))
    (map_pow (LinearMap.prodMapAlgHom K V W) (T, S) n).symm

/-- Two fixed linear outputs agree forever exactly when their first `d₁ + d₂`
observations agree. Both dimensions may be zero. -/
theorem observation_prefix_iff_all {d₁ d₂ : ℕ}
    (A₁ : Matrix (Fin d₁) (Fin d₁) K) (x₁ c₁ : Fin d₁ → K)
    (A₂ : Matrix (Fin d₂) (Fin d₂) K) (x₂ c₂ : Fin d₂ → K) :
    (∀ n < d₁ + d₂, observation A₁ x₁ c₁ n = observation A₂ x₂ c₂ n) ↔
    ∀ n : ℕ, observation A₁ x₁ c₁ n = observation A₂ x₂ c₂ n := by
  constructor
  · intro h
    let T := A₁.mulVecLin.prodMap A₂.mulVecLin
    let ell : ((Fin d₁ → K) × (Fin d₂ → K)) →ₗ[K] K :=
      (dotProductBilin K K c₁).comp (LinearMap.fst K _ _) -
        (dotProductBilin K K c₂).comp (LinearMap.snd K _ _)
    have ho (n : ℕ) : ell ((T ^ n) (x₁, x₂)) =
        observation A₁ x₁ c₁ n - observation A₂ x₂ c₂ n := by
      simp [T, ell, product_power_action, matrix_power_action, observation]
    have hz := Module.End.observation_zero_of_prefix T (x₁, x₂) ell (by
      intro n hn
      rw [ho, sub_eq_zero]
      apply h n
      simpa using hn)
    intro n
    exact sub_eq_zero.mp ((ho n).symm.trans (hz n))
  · intro h n _
    exact h n

end Matrix
