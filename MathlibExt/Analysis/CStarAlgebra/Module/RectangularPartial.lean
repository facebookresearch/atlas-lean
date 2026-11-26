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
# Densely defined operators with right coefficient actions

Let `E,F` be normed additive groups with complex-module structures and actions of `Bᵐᵒᵖ`, for a
coefficient type `B`. A densely defined right-linear partial operator has a complex submodule `D
⊆ E` and a complex-linear map `T : D → F`. The domain is norm-dense and stable under `x <• b`,
and `T (x <• b) = T x <• b` for `x ∈ D` and `b : B`.

The coefficient type need not carry an algebra structure. These data specialize to densely
defined operators between right C-star modules.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open scoped RightActions

namespace CStarModule

universe uB uE uF

/-- **Densely defined right-linear partial operator.** For complex modules `E,F` with normed
additive groups and right actions of a type `B`, this record contains a complex-linear partial
map with norm-dense domain `D`, stability `D <• b ⊆ D`, and `T (x <• b) = T x <• b` on `D`. -/
structure DenselyDefinedRightPartialOperator
    (B : Type uB) (E : Type uE) (F : Type uF)
    [NormedAddCommGroup E] [Module ℂ E] [SMul Bᵐᵒᵖ E]
    [NormedAddCommGroup F] [Module ℂ F] [SMul Bᵐᵒᵖ F] where
  /-- **Complex-linear partial map.** The operator acts complex-linearly from its domain submodule
  of `E` into `F`. -/
  toPartial : E →ₗ.[ℂ] F
  /-- **Density of the partial domain.** The domain of `toPartial` is dense in the norm topology
  of `E`. -/
  dense_domain : Dense (toPartial.domain : Set E)
  /-- **Right invariance of the domain.** For `x ∈ dom T` and `b : B`, the vector `x <• b` belongs
  to `dom T`. -/
  domain_right_smul : ∀ (x : E), x ∈ toPartial.domain → ∀ b : B,
    x <• b ∈ toPartial.domain
  /-- **Right linearity on the partial domain.** For `x ∈ dom T` and `b : B`, `T (x <• b) = T x <•
  b`. -/
  map_right_smul : ∀ (x : toPartial.domain) (b : B),
    toPartial ⟨(x : E) <• b, domain_right_smul (x : E) x.property b⟩ =
      toPartial x <• b

namespace DenselyDefinedRightPartialOperator

variable {B : Type uB} {E : Type uE} {F : Type uF}
variable [NormedAddCommGroup E] [Module ℂ E] [SMul Bᵐᵒᵖ E]
variable [NormedAddCommGroup F] [Module ℂ F] [SMul Bᵐᵒᵖ F]

/-- **Extensionality of dense right-linear operators.** Two such operators `T,S : E → F` are equal
when their complex-linear partial maps are equal, including their domain submodules. -/
@[ext]
theorem ext {T S : DenselyDefinedRightPartialOperator B E F}
    (h : T.toPartial = S.toPartial) : T = S := by
  cases T
  cases S
  cases h
  rfl

end DenselyDefinedRightPartialOperator

end CStarModule
