/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.IsingBoxEncoding
public import PhyslibExt.CondensedMatter.IsingModel.GKS

/-!
# Nonnegativity of the plus-boundary magnetization

For `β ≥ 0` the magnetization at the origin under the plus-boundary finite-volume Ising measure
is nonnegative, hence so is the spontaneous magnetization.

## i. Overview

With plus boundary condition and zero field, the finite-volume Boltzmann weight factors as
`∏_e (cosh β + σ_x σ_y sinh β)`. Expanding the product, every term is a nonnegative multiple of a
spin monomial, and the sum of a spin monomial over configurations is nonnegative because the
boundary spins are `+`. Hence `∑_τ w(τ) σ_0 ≥ 0`: this is the first Griffiths inequality
`⟨σ_0⟩⁺ ≥ 0`. Passing to the limit gives `m*(β) ≥ 0`.

## ii. Key results

- `fvWeight_plus_factor` : the high-temperature factorization of the plus-boundary weight.
- `sum_fvWeight_spin_origin_nonneg` : `∑_τ w(τ) σ_0(τ) ≥ 0`.
- `magnetization_nonneg` : the spontaneous magnetization is nonnegative for `β ≥ 0`.

## iii. Table of contents

- A. The high-temperature expansion of the plus-boundary weight
- B. Nonnegativity of the magnetization

## iv. References

- R. B. Griffiths, *Correlations in Ising ferromagnets. I*, J. Math. Phys. 8 (1967) 478–483.
- S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems*, Cambridge University
  Press (2017), Section 3.8.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}

/-! ## A. The high-temperature expansion of the plus-boundary weight -/

lemma isSpinMonomial_spin_glue (n : ℕ) (z : Site d) :
    IsSpinMonomial (fun τ : {x // x ∈ box d n} → Bool => spin (glue (plusField d) τ) z) := by
  classical
  by_cases hz : z ∈ box d n
  · have hcongr : (fun τ : {x // x ∈ box d n} → Bool => spin (glue (plusField d) τ) z)
        = (fun τ => spin τ ⟨z, hz⟩) := by
      funext τ; unfold spin; rw [glue_mem (plusField d) τ hz]
    rw [hcongr]; exact isSpinMonomial_spin _
  · have hcongr : (fun τ : {x // x ∈ box d n} → Bool => spin (glue (plusField d) τ) z)
        = (fun _ => (1 : ℝ)) := by
      funext τ; unfold spin; rw [glue_not_mem (plusField d) τ hz]; simp [plusField]
    rw [hcongr]; exact IsSpinMonomial.const_one

lemma isSpinMonomial_bond_glue (n : ℕ) (e : Sym2 (Site d)) :
    IsSpinMonomial (fun τ : {x // x ∈ box d n} → Bool => bond (glue (plusField d) τ) e) := by
  classical
  induction e with
  | h a b =>
    have heq : (fun τ : {x // x ∈ box d n} → Bool => bond (glue (plusField d) τ) s(a, b))
        = (fun τ => (fun τ => spin (glue (plusField d) τ) a) τ
                    * (fun τ => spin (glue (plusField d) τ) b) τ) := by
      funext τ; rw [bond_mk]
    rw [heq]
    exact (isSpinMonomial_spin_glue n a).mul (isSpinMonomial_spin_glue n b)

lemma fvWeight_plus_factor (n : ℕ) (B : Finset (Sym2 (Site d))) (β : ℝ)
    (τ : {x // x ∈ box d n} → Bool) :
    fvWeight (plusField d) n B β 0 τ
      = ∏ e ∈ B, (Real.cosh β + bond (glue (plusField d) τ) e * Real.sinh β) := by
  unfold fvWeight fvEnergy
  rw [show -β * (-(∑ e ∈ B, bond (glue (plusField d) τ) e)
        - 0 * ∑ x ∈ boxFinset d n, spin (glue (plusField d) τ) x)
        = ∑ e ∈ B, β * bond (glue (plusField d) τ) e by
      rw [zero_mul, sub_zero, neg_mul_neg, Finset.mul_sum]]
  rw [Real.exp_sum]
  exact Finset.prod_congr rfl (fun e _ => exp_mul_pm β _ (bond_eq_pm _ e))

lemma sum_fvWeight_spin_origin_nonneg (n : ℕ) (B : Finset (Sym2 (Site d)))
    {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ ∑ τ : {x // x ∈ box d n} → Bool,
        fvWeight (plusField d) n B β 0 τ * spin (glue (plusField d) τ) (origin d) := by
  classical
  have hrw : ∀ τ : {x // x ∈ box d n} → Bool,
      fvWeight (plusField d) n B β 0 τ * spin (glue (plusField d) τ) (origin d)
        = spin (glue (plusField d) τ) (origin d)
          * ∏ e ∈ B, (Real.cosh β + Real.sinh β * bond (glue (plusField d) τ) e) := by
    intro τ; rw [fvWeight_plus_factor, mul_comm]
    congr 1
    exact Finset.prod_congr rfl (fun e _ => by ring)
  simp_rw [hrw]
  exact gks_kernel B (fun _ => Real.cosh β) (fun _ => Real.sinh β)
    (fun _ _ => (Real.cosh_pos β).le) (fun _ _ => Real.sinh_nonneg_iff.mpr hβ)
    (fun e => fun τ => bond (glue (plusField d) τ) e)
    (fun e _ => isSpinMonomial_bond_glue n e)
    (fun τ => spin (glue (plusField d) τ) (origin d)) (isSpinMonomial_spin_glue n (origin d))

end Ising

namespace IsingFK

open StatMech.Ising StatMech.Lattice StatMech.Percolation

variable {d : ℕ}

/-! ## B. Nonnegativity of the magnetization -/

lemma fv_integral_origin_nonneg (d : ℕ) {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    0 ≤ ∫ ω, spin ω (origin d)
        ∂(plusMeasure d n β 0 : Measure (ConfigSpace (Site d))) := by
  classical
  have heq : (∫ ω, spin ω (origin d)
      ∂(plusMeasure d n β 0 : Measure (ConfigSpace (Site d))))
      = fvMagnetization d β n := rfl
  rw [heq, fvMagnetization_eq_fvProb_sum]
  unfold fvProb
  have hZ : 0 < fvZ (plusField d) n (bondFinsetTouch d n) β 0 := fvZ_pos _ _ _ _ _
  have hrw : ∀ τ : {x // x ∈ box d n} → Bool,
      fvWeight (plusField d) n (bondFinsetTouch d n) β 0 τ
          / fvZ (plusField d) n (bondFinsetTouch d n) β 0
        * spin (glue (plusField d) τ) (origin d)
      = (fvZ (plusField d) n (bondFinsetTouch d n) β 0)⁻¹
          * (fvWeight (plusField d) n (bondFinsetTouch d n) β 0 τ
              * spin (glue (plusField d) τ) (origin d)) := by
    intro τ; rw [div_eq_mul_inv]; ring
  simp_rw [hrw]
  rw [← Finset.mul_sum]
  exact mul_nonneg (inv_nonneg.mpr hZ.le)
    (StatMech.Ising.sum_fvWeight_spin_origin_nonneg n (bondFinsetTouch d n) hβ)

lemma magnetization_nonneg (d : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ Ising.magnetization d β :=
  Ising.magnetization_nonneg_of_fv d β (fun n => fv_integral_origin_nonneg d hβ n)

end IsingFK

end StatMech
