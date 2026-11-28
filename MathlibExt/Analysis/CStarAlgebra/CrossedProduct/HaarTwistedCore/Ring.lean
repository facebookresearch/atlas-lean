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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.Convolution
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Group.Action.Defs

/-!
# The nonunital Haar twisted convolution algebra

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For core coefficients
f,h:G→A, twisted convolution is (f*h)(x)=∫ s:G, f(s)*α_s(h(s⁻¹*x)) ∂μ. The core Carrier μ α is
a nonunital complex algebra with pointwise addition and scalar multiplication and the
associative product *. Complex scaling satisfies (c•f)*h=c•(f*h)=f*(c•h).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)

/-- **Haar twisted convolution multiplication.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For core coefficients
f,h:G→A, twisted convolution is (f*h)(x)=∫ s:G, f(s)*α_s(h(s⁻¹*x)) ∂μ. This integral is the
product on Carrier μ α.
-/
instance instMulCarrier : Mul (Carrier μ α) :=
  ⟨convolution μ α⟩

/-- **Nonunital ring of twisted core coefficients.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For core coefficients
f,h:G→A, twisted convolution is (f*h)(x)=∫ s:G, f(s)*α_s(h(s⁻¹*x)) ∂μ. The core Carrier μ α is
a nonunital ring: its addition is pointwise, the product is associative and distributive, and
convolution with the zero coefficient is zero.
-/
instance instNonUnitalRingCarrier : NonUnitalRing (Carrier μ α) where
  __ := instAddCommGroupCarrier μ α
  __ := instMulCarrier μ α
  mul_assoc := convolution_assoc μ α
  left_distrib := convolution_add_right μ α
  right_distrib := convolution_add_left μ α
  zero_mul := convolution_zero_left μ α
  mul_zero := convolution_zero_right μ α

/-- **Scalar compatibility in the first convolution factor.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For core coefficients
f,h:G→A, twisted convolution is (f*h)(x)=∫ s:G, f(s)*α_s(h(s⁻¹*x)) ∂μ. For c∈ℂ and core
coefficients f,h, (c•f)*h=c•(f*h).
-/
instance instIsScalarTowerCarrier : IsScalarTower ℂ (Carrier μ α) (Carrier μ α) where
  smul_assoc c f g := convolution_smul_left μ α c f g

/-- **Scalar compatibility in the second convolution factor.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For core coefficients
f,h:G→A, twisted convolution is (f*h)(x)=∫ s:G, f(s)*α_s(h(s⁻¹*x)) ∂μ. For c∈ℂ and core
coefficients f,h, f*(c•h)=c•(f*h).
-/
instance instSMulCommClassCarrier : SMulCommClass ℂ (Carrier μ α) (Carrier μ α) where
  smul_comm c f g := (convolution_smul_right μ α c f g).symm

end

end HaarTwistedCore
