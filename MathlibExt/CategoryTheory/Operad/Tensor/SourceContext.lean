/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Logic.Small.Defs

/-!
# SourceContext

Source data for tensor-operadic free algebras in complete and cocomplete closed symmetric
monoidal model categories.
-/

/- Source proof segment: TensorOperadicSourceContext -/
section source_TensorOperadicSourceContext
/-!
# The exact source setting for tensor-operadic free algebras

This packages only the article's input setting. The original binary
symmetric tensor, closed adjunctions, model structure, small limits and
colimits, and small colors are source data. Finite tensor coherence,
profile monads, free adjunctions, EM equivalences and created algebra
colimits are subsequently constructed results.
-/

@[expose] public section

set_option autoImplicit false

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

/-- The article's original complete and cocomplete closed
symmetric monoidal model category and small color set. All fields
are source structures; none is a tensor-operadic algebra outcome. -/
structure SourceContext where
  /-- The original category object type, with its independent source universe. -/
  C : Type w
  category : Category.{v} C
  monoidal : @MonoidalCategory C category
  symmetric : @SymmetricCategory C category monoidal
  closed : @MonoidalClosed C category monoidal
  model : @HomotopicalAlgebra.ModelCategory C category
  complete : @HasLimitsOfSize.{us, us} C category
  cocomplete : @HasColimitsOfSize.{us, us} C category
  /-- The original small color type, independently sized from the category. -/
  W : Type u
  smallColors : Small.{us} W

attribute [instance] SourceContext.category SourceContext.monoidal
  SourceContext.symmetric SourceContext.closed SourceContext.model
  SourceContext.complete SourceContext.cocomplete SourceContext.smallColors

end CategoryTheory.Operad.Tensor
end
end source_TensorOperadicSourceContext
