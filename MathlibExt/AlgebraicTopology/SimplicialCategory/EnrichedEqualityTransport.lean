/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.StrictCategory
import MathlibExt.CategoryTheory.Enriched.HomEqualityTransport

/-!
# Enriched identity and composition under object equalities

Equality transports change only the supplied endpoint labels. The 
Identity and both composition factors obey the enriched laws;
no equivalence or coherence conclusion is assumed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.EqualityTransport
variable {C : Carrier.{u}}

/-- The Hom equality transport for the two supplied object equalities. -/
def hom {x x' y y' : C} (hx : x = x') (hy : y = y') :
    (x ⟶[SSet.{u}] y) ⟶ (x' ⟶[SSet.{u}] y') :=
  EnrichedHomEqualityTransport.hom hx hy

/-- The enriched identity retains the supplied object equality. -/
theorem identity {x x' : C} (hx : x = x') :
    eId SSet.{u} x ≫ hom hx hx = eId SSet.{u} x' :=
  EnrichedHomEqualityTransport.identity hx

/-- Both Hom factors retain their supplied object equalities under composition. -/
theorem composition {x x' y y' z z' : C} (hx : x = x') (hy : y = y') (hz : z = z') :
    eComp SSet.{u} x y z ≫ hom hx hz =
      (hom hx hy ⊗ₘ hom hy hz) ≫ eComp SSet.{u} x' y' z' :=
  EnrichedHomEqualityTransport.composition hx hy hz

/-- Exact opposite endpoint equality transports cancel on the Hom. -/
theorem cancel {x x' y y' : C} (hx : x = x') (hy : y = y') :
    hom hx.symm hy.symm ≫ hom hx hy = 𝟙 (x' ⟶[SSet.{u}] y') :=
  EnrichedHomEqualityTransport.inverse hx.symm hy.symm

/-- Equality transports retain arbitrary Hom maps in an identity equation. -/
theorem identity_retarget {A : Carrier.{u}} (a : A) {x x' : C} (hx : x = x')
    (d : (a ⟶[SSet.{u}] a) ⟶ (x ⟶[SSet.{u}] x))
    (hd : eId SSet.{u} a ≫ d = eId SSet.{u} x) :
    eId SSet.{u} a ≫ (d ≫ hom hx hx) = eId SSet.{u} x' :=
  (Category.assoc _ _ _).symm.trans ((congrArg (fun f => f ≫ hom hx hx) hd).trans (identity hx))

/-- The two-factor enriched composition equation survives the three exact 
endpoint equalities. -/
theorem composition_retarget {A : Carrier.{u}} (a b c : A) {x x' y y' z z' : C}
    (hx : x = x') (hy : y = y') (hz : z = z')
    (f : (a ⟶[SSet.{u}] b) ⟶ (x ⟶[SSet.{u}] y))
    (g : (b ⟶[SSet.{u}] c) ⟶ (y ⟶[SSet.{u}] z))
    (h : (a ⟶[SSet.{u}] c) ⟶ (x ⟶[SSet.{u}] z))
    (hc : eComp SSet.{u} a b c ≫ h = (f ⊗ₘ g) ≫ eComp SSet.{u} x y z) :
    eComp SSet.{u} a b c ≫ (h ≫ hom hx hz) =
      ((f ≫ hom hx hy) ⊗ₘ (g ≫ hom hy hz)) ≫ eComp SSet.{u} x' y' z' := by
  subst x'
  subst y'
  subst z'
  simpa only [hom, EnrichedHomEqualityTransport.hom, eqToHom_refl, Category.comp_id] using hc

end CategoryTheory.SimplicialEnrichment.EqualityTransport
