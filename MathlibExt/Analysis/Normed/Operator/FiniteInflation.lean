/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Tactic.Positivity

/-!
# Finite diagonal inflation of bounded operators

The same bounded operator acts on each original coordinate of the stock
finite l² carrier. The canonical piMap and PiLp coordinate equivalence
construct the operator. Its algebraic laws, unconditional norm bound and
nonempty-index norm identity require only a complex normed space. Zero
coordinate counts and zero ambient spaces are retained.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace ContinuousLinearMap

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H]

section OperatorAlgebra

variable [NormedSpace ℂ H]

/-- Let `H` be a normed complex vector space and let `n` be a natural number. The amplified operator
acts coordinatewise on the Euclidean product of `n` copies of `H`.

Finite diagonal inflation on the finite l² carrier of a complex normed space. -/
noncomputable def finiteInflation (n : ℕ) (T : H →L[ℂ] H) :
    PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm :
      (Fin n → H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) ∘L
    ((ContinuousLinearMap.piMap (fun _ : Fin n => T)) ∘L
      ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)) :
        PiLp 2 (fun _ : Fin n => H) →L[ℂ] (Fin n → H)))

/-- Let `H` be a normed complex vector space and let `n` be a natural number. The amplified operator
acts coordinatewise on the Euclidean product of `n` copies of `H`.

Coordinate formula for finite operator inflation: `(A⁽ⁿ⁾ x) i = A (x i)`. -/
@[simp]
theorem finiteInflation_apply (n : ℕ) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin n => H)) (i : Fin n) :
    finiteInflation n T x i = T (x i) := by
  simp [finiteInflation]

/-- Let `H` be a normed complex vector space and let `n` be a natural number. The amplified operator
acts coordinatewise on the Euclidean product of `n` copies of `H`.

Finite inflation preserves `0`. -/
theorem finiteInflation_zero (n : ℕ) : finiteInflation (H := H) n 0 = 0 := by
  ext x i
  simp

/-- Let `H` be a normed complex vector space and let `n` be a natural number. The amplified operator
acts coordinatewise on the Euclidean product of `n` copies of `H`.

Finite inflation preserves addition. -/
theorem finiteInflation_add (n : ℕ) (S T : H →L[ℂ] H) :
    finiteInflation n (S + T) = finiteInflation n S + finiteInflation n T := by
  ext x i
  simp [finiteInflation_apply]

/-- Let `H` be a normed complex vector space and let `n` be a natural number. The amplified operator
acts coordinatewise on the Euclidean product of `n` copies of `H`.

Finite inflation preserves scalar multiplication. -/
theorem finiteInflation_smul (n : ℕ) (c : ℂ) (T : H →L[ℂ] H) :
    finiteInflation n (c • T) = c • finiteInflation n T := by
  ext x i
  simp

/-- Let `H` be a normed complex vector space and let `n` be a natural number. The amplified operator
acts coordinatewise on the Euclidean product of `n` copies of `H`.

Finite inflation preserves `1`. -/
theorem finiteInflation_one (n : ℕ) : finiteInflation (H := H) n 1 = 1 := by
  ext x i
  simp

/-- Let `H` be a normed complex vector space and let `n` be a natural number. The amplified operator
acts coordinatewise on the Euclidean product of `n` copies of `H`.

Finite inflation preserves multiplication. -/
theorem finiteInflation_mul (n : ℕ) (S T : H →L[ℂ] H) :
    finiteInflation n (S * T) = finiteInflation n S * finiteInflation n T := by
  ext x i
  simp [finiteInflation_apply, ContinuousLinearMap.mul_def]


end OperatorAlgebra

section OperatorNorm

variable [NormedSpace ℂ H]

/-- Helper: finite inflation acts on `PiLp.single` coordinatewise (proof-only). -/
private theorem finiteInflation_single (n : ℕ) (T : H →L[ℂ] H) (i₀ : Fin n) (y : H) :
    finiteInflation n T (PiLp.single 2 i₀ y) = PiLp.single 2 i₀ (T y) := by
  apply PiLp.ext
  intro j
  by_cases h : j = i₀
  · subst h
    simp
  · simp [h]

/-- Let `H` be a normed complex vector space and let `n` be a natural number. The amplified operator
acts coordinatewise on the Euclidean product of `n` copies of `H`.

The operator-norm bound holds for every finite index, including zero. -/
theorem finiteInflation_norm_le (n : ℕ) (T : H →L[ℂ] H) :
    ‖finiteInflation n T‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have h_norm : ‖finiteInflation n T x‖ ^ 2 = ∑ i : Fin n, ‖T (x i)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2 _]
    apply Finset.sum_congr rfl
    intro i _
    rw [finiteInflation_apply]
  have h_x : ‖x‖ ^ 2 = ∑ i : Fin n, ‖x i‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ x
  have h_comp : ∀ i : Fin n, ‖T (x i)‖ ≤ ‖T‖ * ‖x i‖ :=
    fun i => ContinuousLinearMap.le_opNorm T (x i)
  have h_sq : ∀ i : Fin n, ‖T (x i)‖ ^ 2 ≤ (‖T‖ * ‖x i‖) ^ 2 :=
    fun i => pow_le_pow_left₀ (norm_nonneg _) (h_comp i) 2
  have h_sum : ∑ i : Fin n, ‖T (x i)‖ ^ 2 ≤ ‖T‖ ^ 2 * ∑ i : Fin n, ‖x i‖ ^ 2 := by
    calc ∑ i : Fin n, ‖T (x i)‖ ^ 2
        ≤ ∑ i : Fin n, (‖T‖ * ‖x i‖) ^ 2 :=
          Finset.sum_le_sum fun i _ => h_sq i
      _ = ‖T‖ ^ 2 * ∑ i : Fin n, ‖x i‖ ^ 2 := by
          simp_rw [mul_pow]
          rw [Finset.mul_sum]
  have h_sq_le : ‖finiteInflation n T x‖ ^ 2 ≤ (‖T‖ * ‖x‖) ^ 2 := by
    rw [h_norm, mul_pow, h_x]
    exact h_sum
  have h_nonneg1 : 0 ≤ ‖finiteInflation n T x‖ := norm_nonneg _
  have h_nonneg2 : 0 ≤ ‖T‖ * ‖x‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h_sqrt := Real.sqrt_le_sqrt h_sq_le
  rw [Real.sqrt_sq h_nonneg1, Real.sqrt_sq h_nonneg2] at h_sqrt
  exact h_sqrt

/-- Lower bound under a nonempty index, helper for the norm identity (proof-only). -/
private theorem finiteInflation_norm_ge_of_nonempty (n : ℕ) [Nonempty (Fin n)]
    (T : H →L[ℂ] H) : ‖T‖ ≤ ‖finiteInflation n T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  obtain ⟨i₀⟩ := (inferInstance : Nonempty (Fin n))
  have h_single : finiteInflation n T (PiLp.single (β := fun _ : Fin n => H) 2 i₀ y) =
      PiLp.single (β := fun _ : Fin n => H) 2 i₀ (T y) :=
    finiteInflation_single n T i₀ y
  calc ‖T y‖
      = ‖finiteInflation n T (PiLp.single (β := fun _ : Fin n => H) 2 i₀ y)‖ := by
          rw [h_single]
          simp
    _ ≤ ‖finiteInflation n T‖ * ‖PiLp.single (β := fun _ : Fin n => H) 2 i₀ y‖ :=
          ContinuousLinearMap.le_opNorm (finiteInflation n T)
            (PiLp.single (β := fun _ : Fin n => H) 2 i₀ y)
    _ = ‖finiteInflation n T‖ * ‖y‖ := by
          rw [PiLp.norm_single 2 (fun _ : Fin n => H) i₀ y]

/-- Let `H` be a normed complex vector space and let `n` be a natural number. The amplified operator
acts coordinatewise on the Euclidean product of `n` copies of `H`. For the exact norm equality
assume `n>0`.

A nonempty finite index preserves the operator norm. -/
theorem finiteInflation_norm_eq (n : ℕ) [Nonempty (Fin n)] (T : H →L[ℂ] H) :
    ‖finiteInflation n T‖ = ‖T‖ :=
  le_antisymm (finiteInflation_norm_le n T) (finiteInflation_norm_ge_of_nonempty n T)

/-- Let `H` be a normed complex vector space and let `n` be a natural number. The amplified operator
acts coordinatewise on the Euclidean product of `n` copies of `H`. For the exact norm equality
assume `n>0`.

A positive coordinate count preserves the operator norm. -/
theorem finiteInflation_norm_eq_of_pos (n : ℕ) (hn : 0 < n) (T : H →L[ℂ] H) :
    ‖finiteInflation n T‖ = ‖T‖ := by
  have hn' : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact @finiteInflation_norm_eq H _ _ n hn' T


end OperatorNorm

end

end ContinuousLinearMap
