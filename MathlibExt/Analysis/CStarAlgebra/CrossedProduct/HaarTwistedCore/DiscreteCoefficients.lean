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
# Finite coefficients on a discrete monoid

Let G be a discrete monoid with a measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. Compact support on G is finite
support, so the core Carrier μ α is complex-linearly equivalent to G→₀A, the finitely
supported A-valued functions on G. The equivalence and its inverse preserve every coefficient
value.
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

/-- **Linear equivalence with finitely supported coefficients.**

Let G be a discrete monoid with a measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. The complex linear equivalence
discreteCoefficientsEquiv μ α:Carrier μ α≃ₗ[ℂ](G→₀A) sends a compactly supported continuous
coefficient to its finitely supported function.
-/
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

/-- **Value of the discrete coefficient equivalence.**

Let G be a discrete monoid with a measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For f∈Carrier μ α and g∈G,
discreteCoefficientsEquiv μ α f g=f(g).
-/
@[simp]
theorem discreteCoefficientsEquiv_apply (f : Carrier μ α) (g : G) :
    discreteCoefficientsEquiv μ α f g = f g := rfl

/-- **Value of the inverse finite coefficient map.**

Let G be a discrete monoid with a measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For x:G→₀A and g∈G,
(discreteCoefficientsEquiv μ α).symm x evaluated at g is x(g).
-/
@[simp]
theorem discreteCoefficientsEquiv_symm_apply (x : G →₀ A) (g : G) :
    (discreteCoefficientsEquiv μ α).symm x g = x g := rfl

end

end HaarTwistedCore
