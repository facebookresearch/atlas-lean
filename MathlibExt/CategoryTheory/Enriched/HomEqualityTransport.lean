/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.HomEndpointEquality

/-!
# Exact enriched Hom transport along original object equalities

Transport the entire original Hom objects. The original nullary unit,
full composition and full enriched functor maps obey the same object
equalities. The unit and composition laws follow by equality elimination
of the actual endpoints; functor transport specializes the canonical
endpoint-map square. All coefficient and object universes remain independent.

This is the canonical implementation for every monoidal enriched base.
The historical simplicial transport names are compatibility specializations
of these same full Hom laws.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe uV vV uC uD

open CategoryTheory MonoidalCategory

namespace CategoryTheory.EnrichedHomEqualityTransport

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [EnrichedCategory V C]

/-- The same entire original Hom, transported by both actual endpoint equalities. -/
def hom {X X' Y Y' : C} (hx : X = X') (hy : Y = Y') :
    (X ⟶[V] Y) ⟶ (X' ⟶[V] Y') := eqToHom (congrArg₂ (fun A B : C => A ⟶[V] B) hx hy)

/-- Actual object equality retains the original nullary enriched unit. -/
theorem identity {X X' : C} (hx : X = X') : eId V X ≫ hom hx hx = eId V X' := by
  cases hx
  exact Category.comp_id _

/-- The whole original enriched composition retains all three endpoint equalities and both Hom
factors. -/
theorem composition {X X' Y Y' Z Z' : C} (hx : X = X') (hy : Y = Y') (hz : Z = Z') :
    eComp V X Y Z ≫ hom hx hz = (hom hx hy ⊗ₘ hom hy hz) ≫ eComp V X' Y' Z' := by
  cases hx
  cases hy
  cases hz
  simp only [hom, eqToHom_refl, tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]

/-- Both complete original Hom transports compose to their literal original identity. -/
theorem inverse {X X' Y Y' : C} (hx : X = X') (hy : Y = Y') :
    hom hx hy ≫ hom hx.symm hy.symm = 𝟙 (X ⟶[V] Y) := by
  cases hx
  cases hy
  exact Category.id_comp _

/-- The reflexive-endpoint corollary of `EnrichedFunctor.homMap_endpoint_square`, in transport
orientation. -/
theorem functor_map {D : Type uD} [EnrichedCategory V D] (F : EnrichedFunctor V C D)
    {X X' Y Y' : C} (hx : X = X') (hy : Y = Y') :
    F.map X Y ≫ hom (congrArg F.obj hx) (congrArg F.obj hy) = hom hx hy ≫ F.map X' Y' := by
  simpa only [EnrichedFunctor.homMap, hom, eqToHom_refl, Category.comp_id] using
    (EnrichedFunctor.homMap_endpoint_square F
      (a := F.obj X) (b := F.obj Y) (a' := F.obj X') (b' := F.obj Y')
      hx hy (congrArg F.obj hx) (congrArg F.obj hy) rfl rfl rfl rfl).symm

end CategoryTheory.EnrichedHomEqualityTransport
