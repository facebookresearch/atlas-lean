/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/

import MathlibExt.CategoryTheory.Monoidal.Closed.InternalHomInterchange
import MathlibExt.CategoryTheory.Comma.Arrow.OriginalComparisonSquares

/-!
# Clients of the general closed and Arrow homes alone

The importing scope has no simplicial-set, topology, or model-category
dependency. It exercises both entire currying functions and the actual
coordinate and endpoint comparisons at arbitrary category universes.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped MonoidalClosed

namespace CategoryTheory.OriginalGeneralComparisonClients

open MonoidalClosed.OriginalLoopInterchangeGeometry OriginalLoopedEndpointCoherenceGeometry

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

example (I J X : C) :
    (originalIhomCurryingNatIso I J).hom.app X ≫
        (originalIhomCurryingNatIso I J).inv.app X = 𝟙 ((ihom (I ⊗ J)).obj X) :=
  (originalIhomCurryingNatIso I J).hom_inv_id_app X

example (I J X : C) :
    (originalIhomCurryingNatIso I J).inv.app X ≫
        (originalIhomCurryingNatIso I J).hom.app X = 𝟙 ((ihom J).obj ((ihom I).obj X)) :=
  (originalIhomCurryingNatIso I J).inv_hom_id_app X

example [SymmetricCategory C] (K : C) {X Y : C} (f : X ⟶ Y) :
    ((ihom K).map ((ihom K).map f) ≫ (originalSelfInterchangeNatIso K).hom.app Y) ≫
        (originalSelfInterchangeNatIso K).hom.app Y = (ihom K).map ((ihom K).map f) := by
  rw [Category.assoc]
  have h := congr_app (originalSelfInterchangeNatIso_involution K) Y
  exact (congrArg (fun q => (ihom K).map ((ihom K).map f) ≫ q) h).trans (Category.comp_id _)

example [SymmetricCategory C] (K : C) {X Y : C} (f : X ⟶ Y) :
    (ihom K).map ((ihom K).map f) ≫ (originalSelfInterchangeNatIso K).inv.app Y =
      (originalSelfInterchangeNatIso K).hom.app X ≫ (ihom K).map ((ihom K).map f) :=
  (originalSelfInterchangeNatIso_inv_naturality K f).trans
    (congrArg (fun q => q.app X ≫ (ihom K).map ((ihom K).map f))
      (originalSelfInterchangeNatIso_hom_eq_inv K).symm)

example {A B E : C} (e : A ≅ B) (r : A ⟶ E) (q : B ⟶ E) (h : e.hom ≫ q = r) :
    (originalWholeEndpointArrowIso e r q h).hom ≫
        (originalWholeEndpointArrowIso e r q h).inv = 𝟙 (Arrow.mk r) :=
  (originalWholeEndpointArrowIso e r q h).hom_inv_id

example {A B E : C} (e : A ≅ B) (r : A ⟶ E) (q : B ⟶ E) (h : e.hom ≫ q = r) :
    (originalWholeEndpointArrowIso e r q h).hom.left = e.hom ∧
      (originalWholeEndpointArrowIso e r q h).inv.right = 𝟙 E :=
  ⟨originalWholeEndpointArrowIso_hom_left e r q h,
    originalWholeEndpointArrowIso_inv_right e r q h⟩

end CategoryTheory.OriginalGeneralComparisonClients
