/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.ModelCategory.Under
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Fibrant objects in the native Under model category

The terminal Under object is the original map from its base into
the terminal object. Its terminal morphism has the same underlying
terminal map, so the existing created fibration class identifies
fibrancy of an Under object with fibrancy of its original target.
-/

public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace HomotopicalAlgebra

/-- Fibrancy in the native Under model is exactly fibrancy of the supplied
original target, for its actual base map. -/
theorem isFibrant_under_iff {C : Type u} [Category.{v} C] [ModelCategory C]
    (S : C) (P : Under S) : IsFibrant P ↔ IsFibrant P.right := by
  let T : Under S := Under.mk (terminal.from S)
  have hT : IsTerminal T :=
    IsTerminal.ofUniqueHom
      (fun Q => Under.homMk (terminal.from Q.right) (terminalIsTerminal.hom_ext _ _))
      (fun Q f => StructuredArrow.hom_ext _ _ (terminalIsTerminal.hom_ext _ _))
  let p : P ⟶ T := Under.homMk (terminal.from P.right) (terminalIsTerminal.hom_ext _ _)
  have hright : IsFibrant P.right ↔ Fibration p.right := by
    change IsFibrant P.right ↔ Fibration (terminal.from P.right)
    exact isFibrant_iff P.right
  exact (isFibrant_iff_of_isTerminal p hT).trans
    ((fibrations_under_iff S p).trans hright.symm)

end HomotopicalAlgebra
