/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.Elasticity.StressStrain
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum.Basic

/-!
# Isotropic elastic energy: stress, strain, and elastic response

For a displacement gradient `H` with small (infinitesimal) strain
`ε = Elasticity.smallStrain H = (H + Hᵀ) / 2`, which is symmetric, the isotropic
elastic energy density `W = (K / 2) * (tr ε)^2 + μ * ‖dev ε‖^2` is nonnegative
for `K, μ ≥ 0` and positive on nonzero strain for `K, μ > 0`. Here
`dev ε = ε - (tr ε / 3) * I` and the norm is the Frobenius norm, written as a sum
of squares.

## i. Overview

The physical statements are about the small strain of a displacement gradient,
so the skew (rotational) part of the gradient is removed before the energy is
evaluated: an infinitesimal rigid rotation has a skew gradient, zero small strain
(`Elasticity.smallStrain_rigid`), and hence zero energy (`elastic_energy_of_skew`).

They are instances of two algebraic lemmas about the quadratic form
`(K / 2) * (tr ε)^2 + μ * ‖dev ε‖^2` on an arbitrary `3 × 3` array `ε`.
Nonnegativity is a sum of squares: both terms are nonnegative when the moduli
are. Positivity splits on the trace: if `tr ε ≠ 0`, the bulk term is positive;
if `tr ε = 0`, the deviator equals `ε` itself, and some entry is nonzero, so the
sum of squares is positive. The lemmas do not ask for symmetry, so on a
nonsymmetric array the form is not an elastic energy: by the positivity lemma it
is positive on every nonzero skew array, although a skew displacement gradient has
zero small strain.

Tensile-positive stress; `K, μ` are pressures; `W` is energy per volume; this is
not finite-strain elasticity.

## ii. Key results

- `EarthScience.elastic_energy_nonneg`: the energy of a small strain is
  nonnegative for `K, μ ≥ 0`.
- `EarthScience.elastic_energy_pos`: the energy of a nonzero small strain is
  positive for `K, μ > 0`.
- `EarthScience.elastic_energy_of_skew`: a skew displacement gradient
  (infinitesimal rigid rotation) has zero energy.
- `EarthScience.trace_sq_add_deviator_sq_nonneg`,
  `EarthScience.trace_sq_add_deviator_sq_pos`: the underlying algebraic lemmas
  for an arbitrary `3 × 3` array.

## iii. Table of contents

- A. The quadratic form on arbitrary arrays
- B. Elastic energy of a small strain

## iv. References

- `Finset.sum_nonneg`, `Finset.sum_pos'` in Mathlib (sums of squares).
- `Elasticity.smallStrain` and `Elasticity.smallStrain_rigid` in
  `PhyslibExt.CondensedMatter.Elasticity.StressStrain`.
-/

@[expose] public section

open scoped Matrix
open Elasticity

namespace EarthScience

/-! ## A. The quadratic form on arbitrary arrays -/

/-- Algebraic lemma: `(K/2) * (tr ε)^2 + μ * ∑ᵢⱼ (dev εᵢⱼ)^2` with
`dev εᵢⱼ = εᵢⱼ - (tr ε / 3) * (if i = j then 1 else 0)` is nonnegative for `K, μ ≥ 0`,
for every `3 × 3` array `ε`. For the elastic energy of a strain, see
`elastic_energy_nonneg`. -/
lemma trace_sq_add_deviator_sq_nonneg (ε : Fin 3 → Fin 3 → ℝ) (K μ : ℝ)
    (hK : 0 ≤ K) (hμ : 0 ≤ μ) :
    0 ≤ (K / 2) * (∑ i, ε i i) ^ 2 +
      μ * ∑ i, ∑ j, (ε i j - (∑ k, ε k k) / 3 * (if i = j then (1 : ℝ) else 0)) ^ 2 := by
  apply add_nonneg
  · exact mul_nonneg (div_nonneg hK (by norm_num)) (sq_nonneg _)
  · exact mul_nonneg hμ
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

set_option linter.flexible false in
/-- Algebraic lemma: for `K, μ > 0` and a nonzero `3 × 3` array `ε`, symmetric or
not, `(K/2) * (tr ε)^2 + μ * ∑ᵢⱼ (dev εᵢⱼ)^2` is positive. For the elastic energy of
a strain, see `elastic_energy_pos`. -/
lemma trace_sq_add_deviator_sq_pos (ε : Fin 3 → Fin 3 → ℝ) (K μ : ℝ)
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

/-! ## B. Elastic energy of a small strain -/

/-- Isotropic elastic energy is nonnegative: for a displacement gradient `H` with
small strain `ε = smallStrain H` and moduli `K, μ ≥ 0`, the energy density
`W = (K/2) * (tr ε)^2 + μ * ∑ᵢⱼ (dev εᵢⱼ)^2` is nonnegative. -/
theorem elastic_energy_nonneg (H : Matrix (Fin 3) (Fin 3) ℝ) (K μ : ℝ)
    (hK : 0 ≤ K) (hμ : 0 ≤ μ) :
    0 ≤ (K / 2) * (∑ i, smallStrain H i i) ^ 2 +
      μ * ∑ i, ∑ j, (smallStrain H i j - (∑ k, smallStrain H k k) / 3 *
        (if i = j then (1 : ℝ) else 0)) ^ 2 :=
  trace_sq_add_deviator_sq_nonneg (smallStrain H) K μ hK hμ

/-- Isotropic elastic energy is positive on nonzero strain: for moduli `K, μ > 0` and a
displacement gradient `H` whose small strain `ε = smallStrain H` is nonzero, the energy
density `W = (K/2) * (tr ε)^2 + μ * ∑ᵢⱼ (dev εᵢⱼ)^2` is positive. -/
theorem elastic_energy_pos (H : Matrix (Fin 3) (Fin 3) ℝ) (K μ : ℝ)
    (hK : 0 < K) (hμ : 0 < μ) (hε : smallStrain H ≠ 0) :
    0 < (K / 2) * (∑ i, smallStrain H i i) ^ 2 +
      μ * ∑ i, ∑ j, (smallStrain H i j - (∑ k, smallStrain H k k) / 3 *
        (if i = j then (1 : ℝ) else 0)) ^ 2 := by
  refine trace_sq_add_deviator_sq_pos (smallStrain H) K μ hK hμ ?_
  by_contra h
  apply hε
  ext i j
  by_contra hij
  exact h ⟨i, j, hij⟩

/-- An infinitesimal rigid rotation stores no elastic energy: a skew displacement
gradient `W` (`Wᵀ = -W`) has zero small strain, so its energy density vanishes for all
moduli `K, μ`. -/
lemma elastic_energy_of_skew (W : Matrix (Fin 3) (Fin 3) ℝ) (hW : Wᵀ = -W) (K μ : ℝ) :
    (K / 2) * (∑ i, smallStrain W i i) ^ 2 +
      μ * ∑ i, ∑ j, (smallStrain W i j - (∑ k, smallStrain W k k) / 3 *
        (if i = j then (1 : ℝ) else 0)) ^ 2 = 0 := by
  have h0 : smallStrain W = 0 := by
    unfold smallStrain
    rw [hW, add_neg_cancel, smul_zero]
  simp [h0]

end EarthScience
