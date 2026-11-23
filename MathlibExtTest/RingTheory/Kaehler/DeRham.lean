/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.Kaehler.DeRham
import Mathlib.RingTheory.Kaehler.Polynomial

/-! # Tests for the algebraic de Rham differential

Checks the defining values, the graded Leibniz rule (with its sign on odd elements), the generator
formula in low degrees, degrees, `d ∘ d = 0`, linearity over `p`-th powers, and that `d` is not
the zero map: on `ℚ[X]`, `d X = D X ≠ 0`.
-/

open ExteriorAlgebra KaehlerDifferential Polynomial

namespace MathlibExtTest.RingTheory.Kaehler.DeRham

section General

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

example (a : A) : deRham R A (algebraMap A _ a) = ι A (D R A a) := deRham_algebraMap a

example (b : A) : deRham R A (ι A (D R A b)) = 0 := deRham_ι_D b

/-- The Leibniz rule carries a sign on one-forms. -/
example (ω : Ω[A⁄R]) (x : ExteriorAlgebra A Ω[A⁄R]) :
    deRham R A (ι A ω * x) = deRham R A (ι A ω) * x - ι A ω * deRham R A x := by
  rw [deRham_mul, involute_ι, neg_mul, sub_eq_add_neg]

/-- In degree zero the Leibniz rule is the derivation rule. -/
example (a b : A) :
    deRham R A (algebraMap A _ (a * b)) =
      a • deRham R A (algebraMap A _ b) + b • deRham R A (algebraMap A _ a) := by
  simp only [deRham_algebraMap, Derivation.leibniz, map_add, map_smul]

/-- The generator formula in degree one: `d (a • D b) = D a ∧ D b`. -/
example (a b : A) : deRham R A (a • ι A (D R A b)) = ι A (D R A a) * ι A (D R A b) := by
  rw [deRham_smul, deRham_ι_D, smul_zero, add_zero]

/-- `d (a • D a) = D a ∧ D a = 0`. -/
example (a : A) : deRham R A (a • ι A (D R A a)) = 0 := by
  rw [deRham_smul, deRham_ι_D, smul_zero, add_zero, ι_sq_zero]

/-- The generator formula in degree two. -/
example (a b₀ b₁ : A) :
    deRham R A (a • ιMulti A 2 ![D R A b₀, D R A b₁]) =
      ιMulti A 3 ![D R A a, D R A b₀, D R A b₁] := by
  have h₂ : ![D R A b₀, D R A b₁] = fun i => D R A (![b₀, b₁] i) := by
    funext i; fin_cases i <;> rfl
  have h₃ : ![D R A a, D R A b₀, D R A b₁] =
      fun i => D R A ((Fin.cons a ![b₀, b₁] : Fin 3 → A) i) := by
    funext i; fin_cases i <;> rfl
  rw [h₃, h₂]
  exact deRham_smul_ιMulti 2 a ![b₀, b₁]

example (x : ExteriorAlgebra A Ω[A⁄R]) : deRham R A (deRham R A x) = 0 := deRham_deRham x

example (x : ⋀[A]^2 Ω[A⁄R]) :
    ((deRhamPow 2 x : ⋀[A]^3 Ω[A⁄R]) : ExteriorAlgebra A Ω[A⁄R]) = deRham R A x := rfl

example (r : R) (x : ExteriorAlgebra A Ω[A⁄R]) :
    deRham R A (algebraMap R A r • x) = algebraMap R A r • deRham R A x :=
  deRham_algebraMap_smul r x

example (p : ℕ) (hp : (p : A) = 0) (a : A) (x : ExteriorAlgebra A Ω[A⁄R]) :
    deRham R A (a ^ p • x) = a ^ p • deRham R A x := deRham_pow_smul p hp a x

/-- The de Rham differential is odd for the grade involution. -/
example (x : ExteriorAlgebra A Ω[A⁄R]) :
    CliffordAlgebra.involute (deRham R A x) = -deRham R A (CliffordAlgebra.involute x) :=
  involute_deRham x

end General

/-- The de Rham differential is not zero: on `ℚ[X]`, `d X = D X ≠ 0`. -/
example : deRham ℚ ℚ[X] (algebraMap ℚ[X] _ X) ≠ 0 := by
  rw [deRham_algebraMap, Ne, ι_eq_zero_iff]
  intro h
  have := congrArg (KaehlerDifferential.polynomialEquiv ℚ) h
  rw [KaehlerDifferential.polynomialEquiv_D, derivative_X, map_zero] at this
  exact one_ne_zero this

end MathlibExtTest.RingTheory.Kaehler.DeRham
