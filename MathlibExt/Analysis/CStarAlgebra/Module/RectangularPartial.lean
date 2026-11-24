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

public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Dense rectangular partial operators with right coefficient actions

The operator has its original dense complex submodule as domain and an
actual complex-linear map from that domain to the independent codomain.
Right coefficient stability and linearity express the original nonunital
module action; no `Module B` structure or coefficient unit is imposed.
This carrier uses only normed additive groups, complex modules and right actions.
The adjoint construction supplies the original normed C-star-module context.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open scoped RightActions

namespace CStarModule

universe uB uE uF

/-- A densely defined right-linear operator between the original right modules. -/
structure DenselyDefinedRightPartialOperator
    (B : Type uB) (E : Type uE) (F : Type uF)
    [NormedAddCommGroup E] [Module ℂ E] [SMul Bᵐᵒᵖ E]
    [NormedAddCommGroup F] [Module ℂ F] [SMul Bᵐᵒᵖ F] where
  /-- The original rectangular complex-linear partial map. -/
  toPartial : E →ₗ.[ℂ] F
  /-- Its actual domain is dense in the original source norm topology. -/
  dense_domain : Dense (toPartial.domain : Set E)
  /-- The domain is stable under the original right coefficient action. -/
  domain_right_smul : ∀ (x : E), x ∈ toPartial.domain → ∀ b : B,
    x <• b ∈ toPartial.domain
  /-- The actual partial map preserves that right coefficient action. -/
  map_right_smul : ∀ (x : toPartial.domain) (b : B),
    toPartial ⟨(x : E) <• b, domain_right_smul (x : E) x.property b⟩ =
      toPartial x <• b

namespace DenselyDefinedRightPartialOperator

variable {B : Type uB} {E : Type uE} {F : Type uF}
variable [NormedAddCommGroup E] [Module ℂ E] [SMul Bᵐᵒᵖ E]
variable [NormedAddCommGroup F] [Module ℂ F] [SMul Bᵐᵒᵖ F]

/-- Dense right-linear operators are determined by their genuine partial maps. -/
@[ext]
theorem ext {T S : DenselyDefinedRightPartialOperator B E F}
    (h : T.toPartial = S.toPartial) : T = S := by
  cases T
  cases S
  cases h
  rfl

end DenselyDefinedRightPartialOperator

end CStarModule
