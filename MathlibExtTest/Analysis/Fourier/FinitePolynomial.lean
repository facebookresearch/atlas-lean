/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Fourier.FinitePolynomial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

noncomputable section

open TorusFourier TorusSobolev

-- Independent coefficient recovery for a nonzero complex Fourier mode.
example (k : Frequency) :
    UnitAddTorus.mFourierCoeff (realize (AddMonoidAlgebra.single k (2 + 3 * Complex.I))) k =
      2 + 3 * Complex.I := by
  rw [coefficient_realize]
  simp

-- Physical differentiation has multiplier i*k, with no residual 2pi factor.
example :
    (derivative 0 (AddMonoidAlgebra.single (![2, -3] : Frequency) 1)).coeff ![2, -3] =
      2 * Complex.I := by
  simp [derivative_coeff]
  ring

open MeasureTheory
open scoped ComplexConjugate

private def wave : TorusFourier.Polynomial :=
  let p := AddMonoidAlgebra.single (![1, 0] : Frequency) (1 + 2 * Complex.I)
  p + conjugate p

private theorem wave_real : IsReal wave := by
  rw [isReal_iff_conjugate_eq]
  simp only [wave, map_add, conjugate_conjugate]
  exact add_comm _ _

-- The nonzero imaginary coefficients nevertheless give a real physical wave.
example : IsReal (derivative 0 wave * derivative 0 wave) :=
  wave_real.derivative 0 |>.mul (wave_real.derivative 0)

-- This Hermitian product is nonzero and generates the second harmonic.
example : (derivative 0 wave * derivative 0 wave).coeff ![2, 0] =
    3 - 4 * Complex.I := by
  norm_num [wave, derivative, map_add, mul_add, add_mul,
    AddMonoidAlgebra.single_mul_single, Finsupp.single_apply,
    funext_iff, Fin.forall_fin_two, Complex.ext_iff]

-- Check the actual real function against Atlas's distinct coefficient normalization.
example : TorusSobolev.fourierCoefficient (realPhysical wave) ![1, 0] =
    (2 * Real.pi : ℂ) * (1 + 2 * Complex.I) := by
  rw [wave_real.fourierCoefficient]
  norm_num [wave, conjugate_coeff, Finsupp.single_apply, funext_iff, Fin.forall_fin_two]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

-- Normalized Haar Parseval gives 2*(1^2+2^2)=10, without an area factor.
example : (∫ x, ‖realize wave x‖ ^ 2) = 10 := by
  have hs : wave.coeff.support = {![1, 0], ![-1, 0]} := by
    ext k
    simp only [Finsupp.mem_support_iff, Finset.mem_insert, Finset.mem_singleton]
    by_cases h : k = ![1, 0]
    · subst k; norm_num [wave, conjugate_coeff, Finsupp.single_apply, funext_iff,
        Fin.forall_fin_two, Complex.ext_iff]
    by_cases h' : k = ![-1, 0]
    · subst k; norm_num [wave, conjugate_coeff, Finsupp.single_apply, funext_iff,
        Fin.forall_fin_two, Complex.ext_iff]
    simp [wave, h, h']
  rw [parseval, hs]
  norm_num [wave, conjugate_coeff, Finsupp.single_apply, funext_iff, Fin.forall_fin_two,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

-- An actual coordinate derivative at zero independently checks i*k scaling.
example : HasDerivAt
    (fun t ↦ physicalLift (AddMonoidAlgebra.single (![2, -3] : Frequency) 1)
      (Function.update (fun _ ↦ 0) 0 t)) (2 * Complex.I) 0 := by
  have h := hasDerivAt_physicalLift 0
    (AddMonoidAlgebra.single (![2, -3] : Frequency) 1) (fun _ ↦ 0)
  simpa [derivative, physicalLift_single, Fin.prod_univ_two, mul_comm] using h

-- Exact convolution creates the summed frequency, rather than wrapping a sampled grid.
example :
    ((AddMonoidAlgebra.single (![2, 0] : Frequency) (3 : ℂ)) *
      AddMonoidAlgebra.single ![1, 0] (2 : ℂ)).coeff ![3, 0] = 6 := by
  norm_num [AddMonoidAlgebra.single_mul_single, Finsupp.single_apply,
    funext_iff, Fin.forall_fin_two]

-- Zero mode and zero polynomial are legitimate, including their derivative and mean.
example : (∫ x, realize (AddMonoidAlgebra.single (0 : Frequency) (7 : ℂ)) x) = 7 ∧
    derivative 0 (AddMonoidAlgebra.single (0 : Frequency) (7 : ℂ)) = 0 := by
  rw [integral_realize]
  simp [derivative]

-- Integration by parts applies to complex polynomials without a reality hypothesis.
example (p q : TorusFourier.Polynomial) :
    (derivative 0 p * q + p * derivative 0 q).coeff 0 = 0 := by
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, integration_by_parts]
  exact neg_add_cancel _
