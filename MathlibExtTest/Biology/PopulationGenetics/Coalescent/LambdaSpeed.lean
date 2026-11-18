/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaSpeed

/-!
# Tests for the Laplace exponent and speed of a Λ-coalescent

The examples restate the atom-at-zero formula and Grey's condition, and
evaluate the Kingman case `Λ = δ₀`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology unitInterval Real ProbabilityTheory
open MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.LambdaSpeed

example (Λ : Measure I) [IsFiniteMeasure Λ] (q : ℝ) :
    psi Λ q = Λ.real {0} * (q ^ 2 / 2) +
      ∫ x in ({0}ᶜ : Set I), (exp (-(q * x)) - 1 + q * x) / (x : ℝ) ^ 2 ∂Λ :=
  psi_eq Λ q

example (Λ : Measure I) [IsFiniteMeasure Λ] :
    GreyCondition Λ ↔ Λ ≠ 0 ∧ ∀ a, 0 < a → IntegrableOn (fun q => (psi Λ q)⁻¹) (Ioi a) :=
  greyCondition_iff Λ

-- Nonzero-support branch of the kernel: a unit atom at `1`, not the special value at `0`.
example (q : ℝ) : psi (Measure.dirac (1 : I)) q = exp (-q) - 1 + q := by
  simp [psi, psiKernel]

example : psi (Measure.dirac (0 : I)) 2 = 2 := psi_dirac_zero_two

example : psiTail (Measure.dirac (0 : I)) 2 = 1 := by
  rw [psiTail_dirac_zero (by norm_num : (0 : ℝ) < 2)]
  norm_num

example : speed (Measure.dirac (0 : I)) 2 = 1 := by
  rw [speed_dirac_zero (by norm_num : (0 : ℝ) < 2)]
  norm_num

example {t : ℝ} (ht : 0 < t) :
    psiTail (Measure.dirac (0 : I)) (speed (Measure.dirac (0 : I)) t) = t :=
  (psiTail_speed (Measure.dirac (0 : I)) greyCondition_dirac_zero ht).2

#print axioms MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent.psi_eq
#print axioms MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent.greyCondition_iff
#print axioms MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent.speed_dirac_zero

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.LambdaSpeed
