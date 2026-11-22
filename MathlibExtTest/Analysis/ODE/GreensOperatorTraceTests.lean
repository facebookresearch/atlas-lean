/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.GreensOperatorTrace
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Tests for Green coefficients and the actual squared Hilbert–Schmidt norm

* The first two Green's eigenvalues, and the square of the first.
* The two-term partial sum is already below the eigenvalue sum `1 / 6`.
* The Green's kernel on the diagonal: `G(x, x) = x * (1 - x)`,
  with `G(1 / 2, 1 / 2) = 1 / 4`.
* The eigenvalue-sum/diagonal-integral identity, restated.
-/

open MathlibExt.Analysis.ODE.GreensOperatorTrace
open MathlibExt.Analysis.ODE.GreensOperator
open MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm
open MeasureTheory

namespace MathlibExtTest.Analysis.ODE.GreensOperatorTraceTests

/-- The first Green's eigenvalue is `1 / π²`. -/
example : (1 : ℝ) / (((1 : ℕ+) : ℝ) ^ 2 * Real.pi ^ 2) = 1 / Real.pi ^ 2 := by
  simp

/-- The second Green's eigenvalue is `1 / (4π²)`. -/
example : (1 : ℝ) / (((2 : ℕ+) : ℝ) ^ 2 * Real.pi ^ 2) = 1 / (4 * Real.pi ^ 2) := by
  have h2 : ((2 : ℕ+) : ℝ) = 2 := by norm_cast
  rw [h2]
  field_simp
  ring

/-- The square of the first Green's eigenvalue is `1 / π⁴`. -/
example : ((1 : ℝ) / (((1 : ℕ+) : ℝ) ^ 2 * Real.pi ^ 2)) ^ 2 = 1 / Real.pi ^ 4 := by
  simp
  field_simp

/-- Every Green's eigenvalue is positive. -/
example (k : ℕ+) : 0 < (1 : ℝ) / ((k : ℝ) ^ 2 * Real.pi ^ 2) := by
  positivity

/-- The two-term partial sum of the eigenvalue series is below the eigenvalue sum. -/
example : (1 : ℝ) / Real.pi ^ 2 + 1 / (4 * Real.pi ^ 2) < 1 / 6 := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi2 : (7.5 : ℝ) < Real.pi ^ 2 := by nlinarith [hpi, Real.pi_pos]
  have hpos : (0 : ℝ) < Real.pi ^ 2 := by positivity
  field_simp
  nlinarith [hpi2]

/-- The Green's kernel on the diagonal is `x * (1 - x)`. -/
example (x : ℝ) : min x x * (1 - max x x) = x * (1 - x) := by
  rw [min_self, max_self]

/-- The Green's kernel on the diagonal attains `1 / 4` at `x = 1 / 2`. -/
example : min (1 / 2 : ℝ) (1 / 2) * (1 - max (1 / 2 : ℝ) (1 / 2)) = 1 / 4 := by
  norm_num [min_self, max_self]

/-- The eigenvalue-sum/diagonal-integral identity, restated. -/
example :
    (∑' k : ℕ+, (1 : ℝ) / ((k : ℝ) ^ 2 * Real.pi ^ 2)) =
      ∫ x in (0 : ℝ)..1, min x x * (1 - max x x) :=
  by simpa only [greensEigenvalue, greensKernel] using greens_eigenvalue_sum_eq_kernel_diagonal_integral

/-- The eigenvalue series sums to `1 / 6`, restated. -/
example :
    (∑' k : ℕ+, (1 : ℝ) / ((k : ℝ) ^ 2 * Real.pi ^ 2)) = 1 / 6 :=
  by simpa only [greensEigenvalue] using tsum_greensEigenvalues

/-- The squared eigenvalue series sums to `1 / 90`, restated. -/
example :
    (∑' k : ℕ+, ((1 : ℝ) / ((k : ℝ) ^ 2 * Real.pi ^ 2)) ^ 2) = 1 / 90 :=
  by simpa only [greensEigenvalue] using tsum_greensEigenvalues_sq

/-- The squared-norm theorem is consumable for a certified continuous Green operator. -/
example (A : L2UnitInterval →L[ℝ] L2UnitInterval)
    (hA_sa : ∀ f g : L2UnitInterval,
      inner (𝕜 := ℝ) (A f) g = inner (𝕜 := ℝ) f (A g))
    (hA_greens : ∀ f : L2UnitInterval,
      (A f : L2UnitInterval) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun x => ∫ t in Set.Icc (0 : ℝ) 1, greensKernel x t * (f : ℝ → ℝ) t)) :
    hsNormSq A (fun n : ℕ => sineHilbertBasis ⟨n + 1, Nat.succ_pos n⟩) =
      ENNReal.ofReal (1 / 90 : ℝ) :=
  hsNormSq_greensOperator A hA_sa hA_greens

/-- The certified Green operator's first sine mode has the canonical squared norm. -/
example (A : L2UnitInterval →L[ℝ] L2UnitInterval)
    (hA_sa : ∀ f g : L2UnitInterval,
      inner (𝕜 := ℝ) (A f) g = inner (𝕜 := ℝ) f (A g))
    (hA_greens : ∀ f : L2UnitInterval,
      (A f : L2UnitInterval) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun x => ∫ t in Set.Icc (0 : ℝ) 1, greensKernel x t * (f : ℝ → ℝ) t)) :
    ‖A (sineHilbertBasis 1)‖ ^ 2 = (greensEigenvalue 1) ^ 2 := by
  have hdec := greens_operator_eigendecomposition A.toLinearMap sineHilbertBasis
    hA_sa sineHilbertBasis_coe hA_greens
  have heig : A (sineHilbertBasis 1) = greensEigenvalue 1 • sineHilbertBasis 1 :=
    Module.End.mem_eigenspace_iff.mp
      ((Module.End.hasEigenvector_iff.mp (hdec.2.1 1)).1)
  rw [heig, norm_smul, sineHilbertBasis.orthonormal.norm_eq_one 1,
    mul_one, Real.norm_eq_abs, sq_abs]

/-- The zero continuous map cannot satisfy the actual Green kernel certificate. -/
example : ¬ ∀ f : L2UnitInterval,
    (((0 : L2UnitInterval →L[ℝ] L2UnitInterval) f) : L2UnitInterval) =ᵐ[
      volume.restrict (Set.Icc (0 : ℝ) 1)]
    (fun x => ∫ t in Set.Icc (0 : ℝ) 1, greensKernel x t * (f : ℝ → ℝ) t) := by
  intro hzero
  have hsa : ∀ f g : L2UnitInterval,
      inner (𝕜 := ℝ) ((0 : Module.End ℝ L2UnitInterval) f) g =
        inner (𝕜 := ℝ) f ((0 : Module.End ℝ L2UnitInterval) g) := by
    intro f g
    simp
  have hdec := greens_operator_eigendecomposition (0 : Module.End ℝ L2UnitInterval)
    sineHilbertBasis hsa sineHilbertBasis_coe hzero
  have heig : (0 : L2UnitInterval) = greensEigenvalue 1 • sineHilbertBasis 1 :=
    Module.End.mem_eigenspace_iff.mp
      ((Module.End.hasEigenvector_iff.mp (hdec.2.1 1)).1)
  have hnorm := congrArg norm heig
  have hpos : 0 < greensEigenvalue 1 := by
    unfold greensEigenvalue
    positivity
  rw [norm_zero, norm_smul, sineHilbertBasis.orthonormal.norm_eq_one 1,
    mul_one, Real.norm_eq_abs, abs_of_pos hpos] at hnorm
  linarith

#print axioms summable_greensEigenvalues
#print axioms tendsto_cofinite_greensEigenvalues
#print axioms tsum_greensEigenvalues
#print axioms tsum_greensEigenvalues_sq
#print axioms integral_greensKernel_diag
#print axioms greens_eigenvalue_sum_eq_kernel_diagonal_integral
#print axioms hsNormSq_greensOperator

end MathlibExtTest.Analysis.ODE.GreensOperatorTraceTests
