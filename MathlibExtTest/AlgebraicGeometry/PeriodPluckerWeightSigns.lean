/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.PeriodLatticePluckerBounds
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.PeriodPluckerWeightSigns

open MathlibExt.AlgebraicGeometry.PeriodLatticePluckerBounds
open MathlibExt.LinearAlgebra.LocalizedLattices

variable (R : Type) [CommRing R] (r : R)

def weight : Fin 2 → ℤ := ![1, 0]

/-- The unit coordinate of diag(xi,1) has exponent zero, not the largest weight one. -/
example : (1 : FractionRing R r) ∈ scalarLine R r (tailSum 2 weight 1) := by
  apply Submodule.subset_span
  refine ⟨1, ?_⟩
  norm_num [tailSum, weight, Finset.sum_filter, Fin.sum_univ_two, parameterUnit]

/-- The top exterior coordinate of that same actual diagonal matrix has total exponent one. -/
example : Matrix.det (Matrix.diagonal ![
      (parameterUnit R r : (FractionRing R r)ˣ).val, (1 : FractionRing R r)]) ∈
    scalarLine R r (tailSum 2 weight 2) := by
  apply Submodule.subset_span
  refine ⟨1, ?_⟩
  norm_num [tailSum, weight, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.diagonal]

end MathlibExtTest.AlgebraicGeometry.PeriodPluckerWeightSigns
