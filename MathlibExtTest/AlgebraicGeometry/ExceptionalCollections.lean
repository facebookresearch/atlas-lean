/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ExceptionalCollections

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.ExceptionalCollections

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open _root_.AlgebraicGeometry SchemeModuleLinear

attribute [local instance] HasDerivedCategory.standard

universe u

variable (k : Type u) [Field k] (X : Over (Spec (.of k)))

noncomputable local instance : Linear k X.left.Modules := modulesLinear k X

-- The scalar endomorphism map sends `c` to `c • 𝟙`.
example (E : DerivedCategory X.left.Modules) (c : k) : scalarEnd k X E c = c • 𝟙 E := rfl

-- The zero object is not exceptional: its endomorphisms cannot receive `k` injectively.
example : ¬ IsExceptional k X 0 := fun h ↦ by
  have := h.1.1 (show scalarEnd k X 0 1 = scalarEnd k X 0 0 from
    (isZero_zero (DerivedCategory X.left.Modules)).eq_of_src _ _)
  exact one_ne_zero this

-- The generated subcategory contains the generators.
example {r : ℕ} (G : Fin r → DerivedCategory X.left.Modules) (a : Fin r) :
    generatedBy k X G (G a) :=
  fun _ _ _ hPG ↦ hPG a

end MathlibExt.AlgebraicGeometry.ExceptionalCollections
