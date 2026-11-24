/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.EichlerIntegral

@[expose] public section

open scoped UpperHalfPlane

-- `exactSource` consumer with the original binders.
example {n : ℕ} {f g : ℍ → ℂ} {F G : ℍ → EichlerIntegral.BinaryForm n}
    (hF : EichlerIntegral.IsEichlerIntegral n f F)
    (hG : EichlerIntegral.IsEichlerIntegral n g G) :
    EichlerIntegral.IsEichlerIntegral n (f + g) (F + G) :=
  EichlerIntegral.IsEichlerIntegral.add hF hG

-- Boundary example: the zero pair is an Eichler integral at every degree,
-- so the derivative condition is not vacuous at the zero function.
example (n : ℕ) : EichlerIntegral.IsEichlerIntegral n 0 0 :=
  EichlerIntegral.IsEichlerIntegral.zero n

-- Boundary example at degree zero: `linePow 0 τ` is the constant form `1`,
-- independently of `τ`.
example (τ : ℂ) :
    ((EichlerIntegral.linePow 0 τ : EichlerIntegral.BinaryForm 0) :
      MvPolynomial (Fin 2) ℂ) = 1 := by
  simp
