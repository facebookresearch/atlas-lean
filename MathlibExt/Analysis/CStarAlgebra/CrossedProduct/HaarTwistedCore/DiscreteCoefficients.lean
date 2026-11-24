/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.Basic
public import MathlibExt.Topology.ContinuousMap.CompactlySupported.Discrete

/-!
# Original measure/action-indexed carrier with discrete finite coefficients

The reusable compact-support/Finsupp construction belongs to the neutral
continuous-map owner. Only the original measure/action-indexed Haar carrier wrapper is constructed
here. The formerly unreleased generic aliases have been retired. It needs a monoid, with no inverse or Haar hypothesis.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CompactlySupported

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [TopologicalSpace G] [DiscreteTopology G]
variable {A : Type uA}

variable [Monoid G] [MeasurableSpace G] [NonUnitalCStarAlgebra A]
variable (μ : MeasureTheory.Measure G) (α : PointNormCStarAction G A)

/-- The same original indexed Haar core as its literal finite complex coefficient module. -/
def discreteCoefficientsEquiv : Carrier μ α ≃ₗ[ℂ] (G →₀ A) where
  toFun f := CompactlySupportedContinuousMap.toFinsupp (toCc μ α f)
  invFun x := fromCc μ α (CompactlySupportedContinuousMap.ofFinsupp x)
  left_inv f := by
    apply ext μ α
    intro g
    rfl
  right_inv x := by
    apply Finsupp.ext
    intro g
    rfl
  map_add' f h := by
    apply Finsupp.ext
    intro g
    rfl
  map_smul' c f := by
    apply Finsupp.ext
    intro g
    rfl

/-- The discrete Haar-core coefficient equivalence preserves every original value. -/
@[simp]
theorem discreteCoefficientsEquiv_apply (f : Carrier μ α) (g : G) :
    discreteCoefficientsEquiv μ α f g = f g := rfl

/-- The inverse discrete coefficient map has the literal original finite support values. -/
@[simp]
theorem discreteCoefficientsEquiv_symm_apply (x : G →₀ A) (g : G) :
    (discreteCoefficientsEquiv μ α).symm x g = x g := rfl

end

end HaarTwistedCore
