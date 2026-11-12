/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Isotropic elastic energy: stress, strain, and elastic response

For isotropic infinitesimal strain `epsilon`, symmetric, the elastic
energy density `W = (K / 2) * (tr epsilon)^2 + mu * ||dev epsilon||^2`
is nonnegative for `K, mu >= 0`, and positive on nonzero strain for
`K, mu > 0`. Here `dev epsilon = epsilon - (tr epsilon / 3) * I` and the
norm is the Euclidean/Frobenius norm, written as a sum of squares.

## i. Overview

Nonnegativity is a sum of squares: both terms are nonnegative when the
moduli are. Positivity splits on the trace: if `tr epsilon != 0`, the
bulk term is positive; if `tr epsilon = 0`, the deviator equals the
strain itself, and some entry is nonzero, so the sum of squares is
positive. Tensile-positive stress; `K, mu` are pressures; `W` is
energy per volume; this is not finite-strain elasticity. A rigid
infinitesimal rotation has zero strain, hence zero energy.

## ii. Key results

- `EarthScience.elastic_energy_nonneg`: energy nonnegative for `K, mu >= 0`.
- `EarthScience.elastic_energy_pos`: energy positive for `K, mu > 0`
  and nonzero strain.

## iii. Table of contents

- A. Nonnegativity
- B. Positivity on nonzero strain

## iv. References

- `Finset.sum_nonneg`, `Finset.sum_pos'` in Mathlib (sums of squares).
-/

@[expose] public section

namespace EarthScience

/-- Isotropic elastic energy `W = (K/2) * (tr ε)^2 + μ * ∑ᵢⱼ (dev εᵢⱼ)^2`
with `dev εᵢⱼ = εᵢⱼ - (tr ε / 3) * (if i = j then 1 else 0)` is nonnegative
for `K, μ ≥ 0`. -/
theorem elastic_energy_nonneg (ε : Fin 3 → Fin 3 → ℝ) (K μ : ℝ)
    (hK : 0 ≤ K) (hμ : 0 ≤ μ) :
    0 ≤ (K / 2) * (∑ i, ε i i) ^ 2 +
      μ * ∑ i, ∑ j, (ε i j - (∑ k, ε k k) / 3 * (if i = j then (1 : ℝ) else 0)) ^ 2 := by
  apply add_nonneg
  · exact mul_nonneg (div_nonneg hK (by norm_num)) (sq_nonneg _)
  · exact mul_nonneg hμ
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

set_option linter.flexible false in

/-- For `K, μ > 0` and nonzero strain `ε`, the elastic energy is positive. -/
theorem elastic_energy_pos (ε : Fin 3 → Fin 3 → ℝ) (K μ : ℝ)
    (hK : 0 < K) (hμ : 0 < μ) (hε : ∃ i j, ε i j ≠ 0) :
    0 < (K / 2) * (∑ i, ε i i) ^ 2 +
      μ * ∑ i, ∑ j, (ε i j - (∑ k, ε k k) / 3 * (if i = j then (1 : ℝ) else 0)) ^ 2 := by
  have hK2 : 0 < K / 2 := div_pos hK (by norm_num)
  have hμS_nonneg : 0 ≤ μ * ∑ i, ∑ j,
      (ε i j - (∑ k, ε k k) / 3 * (if i = j then (1 : ℝ) else 0)) ^ 2 :=
    mul_nonneg (le_of_lt hμ)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  by_cases hT : (∑ i, ε i i) = 0
  · obtain ⟨a, b, hab⟩ := hε
    have hinner_pos : 0 < ∑ j, (ε a j) ^ 2 :=
      Finset.sum_pos' (fun j _ => sq_nonneg _)
        ⟨b, Finset.mem_univ b, sq_pos_of_ne_zero hab⟩
    have hS_pos : 0 < ∑ i, ∑ j, (ε i j) ^ 2 :=
      Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
        ⟨a, Finset.mem_univ a, hinner_pos⟩
    simp [hT]
    exact mul_pos hμ hS_pos
  · have hT2 : 0 < (∑ i, ε i i) ^ 2 := sq_pos_of_ne_zero hT
    have hfirst : 0 < (K / 2) * (∑ i, ε i i) ^ 2 := mul_pos hK2 hT2
    exact add_pos_of_pos_of_nonneg hfirst hμS_nonneg

end EarthScience
