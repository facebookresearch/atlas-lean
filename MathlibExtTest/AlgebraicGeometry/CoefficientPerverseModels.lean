/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.CoefficientPerverseModels
import MathlibExt.AlgebraicGeometry.RealCoefficientPerverseSheaves

/-!
# The coefficient-generic perverse theory and its rational and real forms

The generic structure is unique, the rational and real-coefficient theories are literally its cases
`k = ℚ` and `k = A`, and the resulting middle t-structures agree.
-/

namespace MathlibExtTest.AlgebraicGeometry.CoefficientPerverseModels

open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoefficientPerverseModels

variable (X : PerverseSheaves.ComplexScheme) [PerverseSheaves.IsComplexVariety X]

example (k : Type) [Field k] : Subsingleton (CoefficientPerverseTheory k X) := inferInstance

/-- The rational theory is the case `k = ℚ`. -/
example : PerverseSheaves.PerverseSheafTheory X = CoefficientPerverseTheory ℚ X := rfl

/-- The real-coefficient theory is the case `k = A`. -/
example (A : Subfield ℝ) :
    RealCoefficientPerverseSheaves.PerverseTheory A X = CoefficientPerverseTheory A X := rfl

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
