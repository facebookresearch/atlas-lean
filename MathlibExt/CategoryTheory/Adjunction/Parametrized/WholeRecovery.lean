/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Adjunction.Parametrized.FunctorTransport

/-!
# Transport of parametrized adjunctions along functor equalities

Transporting both functors of a parametrized adjunction along equalities retains the entire adjunction up to heterogeneous equality. The same statement holds for each fixed-parameter adjunction.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uC vC uD vD uV vV
open CategoryTheory

namespace CategoryTheory.ParametrizedAdjunction

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {V : Type uV} [Category.{vV} V]

/-- Transport through whole functor equalities retains the entire parametrized
adjunction value, including its fixed adjunctions and naturality data. -/
theorem transportWhole_heq {F F' : C ⥤ D ⥤ V} {G G' : Cᵒᵖ ⥤ V ⥤ D}
    (eF : F = F') (eG : G = G') (adj : F ⊣₂ G) :
    HEq (transportWhole eF eG adj) adj := by
  subst F'
  subst G'
  rfl

/-- Transport through whole functor equalities retains every fixed adjunction value. -/
theorem transportWhole_adj {F F' : C ⥤ D ⥤ V} {G G' : Cᵒᵖ ⥤ V ⥤ D}
    (eF : F = F') (eG : G = G') (adj : F ⊣₂ G) (X : C) :
    HEq ((transportWhole eF eG adj).adj X) (adj.adj X) := by
  subst F'
  subst G'
  rfl

end CategoryTheory.ParametrizedAdjunction
