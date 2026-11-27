/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomTransport

/-!
# Actual enriched Hom transport with specified original endpoints

The inverse of a genuine Hom isomorphism transports an actual enriched
functor map to the supplied source and target vertices. The complete
identity and composition equations retain those individual vertices.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.HomTransportEndpoints
variable {A B C : Carrier.{u}} (E : A ⟶ B) (F : A ⟶ C)

/-- The whole transported Hom map at the supplied individual source and target endpoints. -/
def map (a b : A) [IsIso (E.map a b)] {x₀ x₁ : B} {y₀ y₁ : C}
    (hx₀ : E.obj a = x₀) (hx₁ : E.obj b = x₁)
    (hy₀ : F.obj a = y₀) (hy₁ : F.obj b = y₁) :
    (x₀ ⟶[SSet.{u}] x₁) ⟶ (y₀ ⟶[SSet.{u}] y₁) :=
  eqToHom (congrArg₂ (fun x y : B => x ⟶[SSet.{u}] y) hx₀.symm hx₁.symm) ≫
    HomTransport.map E F a b ≫
      eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y) hy₀ hy₁)

/-- The supplied source endpoints read back the entire original enriched Hom map. -/
theorem readback (a b : A) [IsIso (E.map a b)] {x₀ x₁ : B} {y₀ y₁ : C}
    (hx₀ : E.obj a = x₀) (hx₁ : E.obj b = x₁)
    (hy₀ : F.obj a = y₀) (hy₁ : F.obj b = y₁) :
    E.map a b ≫ eqToHom (congrArg₂ (fun x y : B => x ⟶[SSet.{u}] y) hx₀ hx₁) ≫
      map E F a b hx₀ hx₁ hy₀ hy₁ =
    F.map a b ≫ eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y) hy₀ hy₁) := by
  subst x₀
  subst x₁
  subst y₀
  subst y₁
  simpa only [map, eqToHom_refl, Category.id_comp, Category.comp_id] using
    HomTransport.map_readback E F a b

/-- The transported map preserves the whole original identity at the specified vertex. -/
theorem map_id (a : A) [IsIso (E.map a a)] {x : B} {y : C}
    (hx : E.obj a = x) (hy : F.obj a = y) :
    eId SSet.{u} x ≫ map E F a a hx hx hy hy = eId SSet.{u} y := by
  subst x
  subst y
  simpa only [map, eqToHom_refl, Category.id_comp, Category.comp_id] using HomTransport.map_id E F a

/-- The transported maps preserve the whole composition at the same three specified vertices. -/
theorem map_comp (a b c : A)
    [IsIso (E.map a b)] [IsIso (E.map b c)] [IsIso (E.map a c)]
    {x₀ x₁ x₂ : B} {y₀ y₁ y₂ : C}
    (hx₀ : E.obj a = x₀) (hx₁ : E.obj b = x₁) (hx₂ : E.obj c = x₂)
    (hy₀ : F.obj a = y₀) (hy₁ : F.obj b = y₁) (hy₂ : F.obj c = y₂) :
    eComp SSet.{u} x₀ x₁ x₂ ≫ map E F a c hx₀ hx₂ hy₀ hy₂ =
      (map E F a b hx₀ hx₁ hy₀ hy₁ ⊗ₘ map E F b c hx₁ hx₂ hy₁ hy₂) ≫
        eComp SSet.{u} y₀ y₁ y₂ := by
  subst x₀
  subst x₁
  subst x₂
  subst y₀
  subst y₁
  subst y₂
  simpa only [map, eqToHom_refl, Category.id_comp, Category.comp_id] using
    HomTransport.map_comp E F a b c

end CategoryTheory.SimplicialEnrichment.HomTransportEndpoints
