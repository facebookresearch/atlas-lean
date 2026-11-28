/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Homology.Hochschild.DifferentialFormProjection
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# A polynomial one-form over a zero-divisor coefficient ring

For A = (ZMod 6)[X,Y], the actual coefficient projection sends X ⊗ Y to X dY.
The Y-derivation followed by evaluation X=Y=1 reads this form as one. It also
detects that twice the form is nonzero, although multiplication by three kills it.
-/

noncomputable section

open scoped TensorProduct

namespace PolynomialFormZeroDivisorTests

private abbrev k := ZMod 6
private abbrev A := MvPolynomial (Fin 2) k
private abbrev Ω := KaehlerDifferential k A

private def form :=
  ModuleCat.Algebra.Hochschild.Symmetric.coefficientFormProjection k A A 1
    (MvPolynomial.X (0 : Fin 2) ⊗ₜ[k]
      PiTensorProduct.tprod k (fun _ : Fin 1 => MvPolynomial.X (1 : Fin 2)))

private def readForm : (A ⊗[A] (⋀[A]^1 Ω)) →ₗ[k] k :=
  (MvPolynomial.aeval (fun _ : Fin 2 => (1 : k))).toLinearMap.comp
    (((MvPolynomial.pderiv (1 : Fin 2)).liftKaehlerDifferential.restrictScalars k).comp
      (((exteriorPower.oneEquiv A Ω).toLinearMap.restrictScalars k).comp
        ((TensorProduct.lid A (⋀[A]^1 Ω)).toLinearMap.restrictScalars k)))

private theorem read_form : readForm form = 1 := by
  unfold form
  rw [ModuleCat.Algebra.Hochschild.Symmetric.coefficientFormProjection_tprod]
  change (MvPolynomial.aeval (fun _ : Fin 2 => (1 : k)))
    ((MvPolynomial.pderiv (1 : Fin 2)).liftKaehlerDifferential
      (exteriorPower.oneEquiv A Ω
        (TensorProduct.lid A (⋀[A]^1 Ω)
          (MvPolynomial.X (0 : Fin 2) ⊗ₜ[A] exteriorPower.ιMulti A 1
            (fun _ : Fin 1 => KaehlerDifferential.D k A
              (MvPolynomial.X (1 : Fin 2))))))) = 1
  rw [TensorProduct.lid_tmul, (exteriorPower.oneEquiv A Ω).map_smul,
    exteriorPower.oneEquiv_ιMulti,
    (MvPolynomial.pderiv (1 : Fin 2)).liftKaehlerDifferential.map_smul,
    Derivation.liftKaehlerDifferential_comp_D]
  change (MvPolynomial.aeval (fun _ : Fin 2 => (1 : k)))
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.pderiv (1 : Fin 2)
      (MvPolynomial.X (1 : Fin 2))) = 1
  rw [MvPolynomial.pderiv_X_self, map_mul, MvPolynomial.aeval_X, map_one, mul_one]

example : form ≠ 0 := by
  intro h
  have e := congrArg readForm h
  rw [read_form, map_zero] at e
  exact one_ne_zero e

example : (2 : k) • form ≠ 0 ∧ (3 : k) • ((2 : k) • form) = 0 := by
  constructor
  · intro h
    have e := congrArg readForm h
    rw [map_smul, read_form, map_zero] at e
    norm_num at e
  · rw [smul_smul]
    norm_num

end PolynomialFormZeroDivisorTests
