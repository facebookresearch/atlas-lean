/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.HyperkahlerPeriods

@[expose] public section

/-!
# Tests for the Beauville–Bogomolov normalization and period points

A complex structure is determined by its operator. The Beauville quadratic
expression is `n/2 · ∫ η² (σσ̄)^(n-1)` minus `(n-1)` times the product of the
two mixed integrals divided by the symplectic volume: for `n = 1` the mixed
term vanishes and for `n = 2` it enters with coefficient `-1`. A period point
needs `q(z, z̄) > 0` on its line, so the zero form has none.
-/

noncomputable section

open scoped Manifold ContDiff TensorProduct
open MathlibExt.AlgebraicGeometry
open ManifoldDifferentialForms CoordinateFormIntegrals HyperkahlerComplexStructures
open BeauvilleBogomolovForms HyperkahlerPeriods

namespace MathlibExtTest.AlgebraicGeometry.HyperkahlerPeriods

variable (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Ambient n) M]
  [IsManifold 𝓘(ℝ, Ambient n) ∞ M]

example (I J : ComplexStructure n M) (h : I.operator = J.operator) : I = J :=
  ComplexStructure.ext h

variable [ExteriorTheory ℝ (Ambient n) M] [WedgeTheory (2 * n) M]
  (C : RealCoordinateMap (2 * n)) (A : IntegrationAtlas (2 * n) M)

/-- The quadratic expression with coefficients `a` and `b`. -/
example (hpos : 0 < n) (σ : ComplexForms n M 2) (η : RealForms n M 2) (a b : ℂ) :
    quadraticExpression n M C A hpos σ η a b =
      a * complexIntegral n M C A (castComplexForm n M (by omega)
          (complexWedge n M (complexWedge n M (realForm n M η) (realForm n M η))
            (complexWedge n M (complexPower n M σ (n - 1))
              (complexPower n M (conjugateForm n M σ) (n - 1))))) -
        b * complexIntegral n M C A (castComplexForm n M (by omega)
            (complexWedge n M (complexWedge n M (realForm n M η) (complexPower n M σ (n - 1)))
              (complexPower n M (conjugateForm n M σ) n))) *
          complexIntegral n M C A (castComplexForm n M (by omega)
            (complexWedge n M (complexWedge n M (realForm n M η) (complexPower n M σ n))
              (complexPower n M (conjugateForm n M σ) (n - 1)))) /
          symplecticVolume n M C A σ :=
  rfl

end MathlibExtTest.AlgebraicGeometry.HyperkahlerPeriods

namespace MathlibExtTest.AlgebraicGeometry.HyperkahlerPeriods.Small

variable (M : Type) [TopologicalSpace M]

/-- For `n = 1` the Beauville form is half the integral of `η²`: there is no
mixed term. -/
example [ChartedSpace (Ambient 1) M] [IsManifold 𝓘(ℝ, Ambient 1) ∞ M]
    [ExteriorTheory ℝ (Ambient 1) M] [WedgeTheory (2 * 1) M]
    (C : RealCoordinateMap (2 * 1)) (A : IntegrationAtlas (2 * 1) M)
    (σ : ComplexForms 1 M 2) (η : RealForms 1 M 2) :
    2 * beauvilleQuadratic 1 M C A one_pos σ η =
      quadraticExpression 1 M C A one_pos σ η 1 0 := by
  simp only [beauvilleQuadratic, quadraticExpression]
  push_cast
  ring

/-- For `n = 2` both coefficients are `1`, so the mixed product is subtracted. -/
example [ChartedSpace (Ambient 2) M] [IsManifold 𝓘(ℝ, Ambient 2) ∞ M]
    [ExteriorTheory ℝ (Ambient 2) M] [WedgeTheory (2 * 2) M]
    (C : RealCoordinateMap (2 * 2)) (A : IntegrationAtlas (2 * 2) M)
    (σ : ComplexForms 2 M 2) (η : RealForms 2 M 2) :
    beauvilleQuadratic 2 M C A two_pos σ η =
      quadraticExpression 2 M C A two_pos σ η 1 1 := by
  simp only [beauvilleQuadratic]
  norm_num

/-- The zero form has no period points. -/
example (L : Type) [AddCommGroup L] [Module ℤ L] [Module.Finite ℤ L] :
    IsEmpty (PeriodPoint L 0) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨l, -, hpos⟩ := x
  have hmem : l.rep ∈ l.submodule := by
    rw [Projectivization.submodule_eq]
    exact Submodule.mem_span_singleton_self _
  have h := (hpos l.rep hmem l.rep_ne_zero).2
  simp at h

end MathlibExtTest.AlgebraicGeometry.HyperkahlerPeriods.Small
