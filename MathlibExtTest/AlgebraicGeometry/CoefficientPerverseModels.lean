/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.CoefficientPerverseModels

/-!
# The coefficient-generic perverse theory and its rational and real forms

The generic structure is unique, a real-coefficient (or rational) perverse theory provides it, and
the resulting middle t-structure is the real (or rational) one.
-/

namespace MathlibExtTest.AlgebraicGeometry.CoefficientPerverseModels

open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoefficientPerverseModels

variable (X : PerverseSheaves.ComplexScheme) [PerverseSheaves.IsComplexVariety X]

example (k : Type) [Field k] : Subsingleton (CoefficientPerverseTheory k X) := inferInstance

section Real

variable (A : Subfield ℝ) [RealCoefficientPerverseSheaves.PerverseTheory A X]

noncomputable example : CoefficientPerverseTheory A X := inferInstance

/-- The generic middle t-structure at `k = A` is the real-coefficient one. -/
example : perverseTStructure A X = RealCoefficientPerverseSheaves.perverseTStructure A X := rfl

/-- Any generic structure at `k = A` agrees with the one provided by the real theory. -/
example (T : CoefficientPerverseTheory A X) : T = (inferInstance : CoefficientPerverseTheory A X) :=
  Subsingleton.elim _ _

end Real

section Rational

variable [PerverseSheaves.PerverseSheafTheory X]

/-- The generic middle t-structure at `k = ℚ` is the rational one. -/
example : perverseTStructure ℚ X = PerverseSheaves.perverseTStructure X := rfl

end Rational

end MathlibExtTest.AlgebraicGeometry.CoefficientPerverseModels
