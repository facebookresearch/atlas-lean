/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.MatrixFactorization.SuccessiveProjection
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
# Successive projection algorithm tests

Non-vacuity of `Separable`: in `ℝ³` (`EuclideanSpace ℝ (Fin 3)`), the two standard basis
vectors `e₀, e₁` as archetypes and the columns `e₀, e₁, (e₀ + e₁)/2, 0` (a mixture and a zero
"background" column, both allowed by the sub-convex assumption). Then SPA runs of length `2`
exist and find exactly `{e₀, e₁}`. The bound of Lemma 1 is checked on the mixture.
-/

namespace Cslib.MachineLearning.MatrixFactorization.SuccessiveProjection

open Finset

private noncomputable abbrev e (k : Fin 3) : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single k 1

private noncomputable def wEx : Fin 2 → EuclideanSpace ℝ (Fin 3) := fun k => e (Fin.castSucc k)

private noncomputable def hEx : Fin 2 → Fin 4 → ℝ :=
  fun k j => if j = 2 then 1 / 2 else if j = 3 then 0 else if (k : ℕ) = j then 1 else 0

private noncomputable def mEx (j : Fin 4) : EuclideanSpace ℝ (Fin 3) := ∑ k, hEx k j • wEx k

private theorem wEx_li : LinearIndependent ℝ wEx := by
  have := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.linearIndependent.comp Fin.castSucc
    (Fin.castSucc_injective 2)
  convert this using 1
  funext k
  simp [wEx, e]

private noncomputable def sepEx : Separable mEx 2 where
  w := wEx
  h := hEx
  linearIndependent := wEx_li
  nonneg := fun k j => by fin_cases k <;> fin_cases j <;> norm_num [hEx]
  sum_le_one := fun j => by fin_cases j <;> simp only [Fin.sum_univ_two, hEx] <;> norm_num
  eq_sum := fun _ => rfl
  pure := fun k => ⟨Fin.castLE (by norm_num) k, by
    fin_cases k <;> simp [mEx, hEx, Fin.sum_univ_two]⟩

/-- SPA runs of length `2` exist and recover both archetypes. -/
example : ∃ S : List (Fin 4), S.length = 2 ∧
    {x | ∃ j ∈ S, mEx j = x} = Set.range wEx := by
  obtain ⟨S, hlen, hS⟩ := exists_isSPARun mEx 2
  exact ⟨S, hlen, hS.range_eq sepEx hlen⟩

/-- Lemma 1 bound on the mixture column: norm at most `1`. -/
example : ‖∑ k, hEx k 2 • wEx k‖ ≤ 1 :=
  norm_sum_smul_le wEx (fun k => hEx k 2) zero_le_one
    (fun k => by simp [wEx, e]) (fun k => by norm_num [hEx]) (by norm_num [hEx, Fin.sum_univ_two])

example : IsSPARun mEx [] := trivial

end Cslib.MachineLearning.MatrixFactorization.SuccessiveProjection
