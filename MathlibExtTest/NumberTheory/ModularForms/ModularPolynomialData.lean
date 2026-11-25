/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.ModularPolynomialData

@[expose] public section

open ModularCurve

/-- Source-shaped consumer: the level-one exemplar inhabits the carrier. -/
example : Nonempty (ModularPolynomialData 1) :=
  ModularCurve.nonempty_modularPolynomialData_one

/-- The exemplar polynomial is `X - Y`, monic of degree one in the outer
variable, and vanishes on the diagonal. -/
example : modularPolynomialDataOne.Φ = Polynomial.X - Polynomial.C Polynomial.X :=
  rfl

example : modularPolynomialDataOne.Φ.Monic := modularPolynomialDataOne.monic

example : modularPolynomialDataOne.Φ.natDegree = ArithmeticFunction.dedekindPsi 1 :=
  modularPolynomialDataOne.natDegree_eq

/-- Boundary check: the degree function records level one correctly. -/
example : ArithmeticFunction.dedekindPsi 1 = 1 := ArithmeticFunction.dedekindPsi_one
