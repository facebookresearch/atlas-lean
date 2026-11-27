/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/

import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Complete original comparison and endpoint Arrow squares

The full original generic comparison constructors and coherence proofs
retain their existing public Names and all original input functions.
-/

set_option autoImplicit false
noncomputable section

section
universe u
open CategoryTheory

namespace CategoryTheory.OriginalLoopPathComparisonCoherenceGeometry

universe u₁ v₁
variable {C : Type u₁} [Category.{v₁} C]

/-- The whole comparison square follows from the complete original projection, map and swap
squares before any actual native specialization. -/
theorem originalWholeComparisonSquare {A A' B B' D D' : C}
    (fA : A ⟶ A') (fB : B ⟶ B') (fD : D ⟶ D')
    (eA : A ⟶ D) (eA' : A' ⟶ D') (eB : B ⟶ D) (eB' : B' ⟶ D')
    (s : D ⟶ D) (s' : D' ⟶ D') (a : A ⟶ B) (a' : A' ⟶ B')
    (hp : a ≫ eB = eA ≫ s) (hp' : a' ≫ eB' = eA' ≫ s')
    (hA : fA ≫ eA' = eA ≫ fD) (hB : fB ≫ eB' = eB ≫ fD)
    (hs : fD ≫ s' = s ≫ fD) [hMono : Mono eB'] : fA ≫ a' = a ≫ fB := by
  apply (cancel_mono eB').mp
  rw [Category.assoc, hp', ← Category.assoc, hA, Category.assoc, hs,
    ← Category.assoc, ← hp, Category.assoc, ← hB, ← Category.assoc]

/-- Both complete inverse comparison functions retain the whole original naturality square. -/
theorem originalWholeInverseComparisonSquare {A A' B B' : C}
    (e : A ≅ B) (e' : A' ≅ B') (fA : A ⟶ A') (fB : B ⟶ B')
    (h : fA ≫ e'.hom = e.hom ≫ fB) : fB ≫ e'.inv = e.inv ≫ fA := by
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, ← h, Category.assoc, e'.hom_inv_id, Category.comp_id,
    ← Category.assoc, e.hom_inv_id, Category.id_comp]

end CategoryTheory.OriginalLoopPathComparisonCoherenceGeometry

end

section
universe u
open CategoryTheory

namespace CategoryTheory.OriginalLoopedEndpointCoherenceGeometry

universe u₁ v₁
variable {C : Type u₁} [Category.{v₁} C]

/-- The full original endpoint square follows from the complete projection and coordinate
squares before native specialization. -/
theorem originalWholeEndpointSquare {A B E P Q : C}
    (m : A ⟶ B) (q : B ⟶ E) (r : A ⟶ E) (e : E ⟶ P)
    (b : B ⟶ Q) (a : A ⟶ Q) (s : Q ⟶ Q) (v w : Q ⟶ P)
    (hq : q ≫ e = b ≫ v) (hm : m ≫ b = a ≫ s)
    (hs : s ≫ v = w) (hr : r ≫ e = a ≫ w) [hMono : Mono e] : m ≫ q = r := by
  apply (cancel_mono e).mp
  rw [Category.assoc, hq, ← Category.assoc, hm, Category.assoc, hs, ← hr]

/-- The entire inverse original comparison retains the SAME complete endpoint square. -/
theorem originalWholeInverseEndpointSquare {A B E : C} (e : A ≅ B)
    (r : A ⟶ E) (q : B ⟶ E) (h : e.hom ≫ q = r) : e.inv ≫ r = q := by
  rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- The full original endpoint Arrow constructor is transported as one whole category function. -/
def originalWholeEndpointArrowIso {A B E : C} (e : A ≅ B)
    (r : A ⟶ E) (q : B ⟶ E) (h : e.hom ≫ q = r) : Arrow.mk r ≅ Arrow.mk q :=
  Arrow.isoMk e (Iso.refl _) (h.trans (Category.comp_id _).symm)

/-- The full forward Arrow total function retains its complete original comparison clause. -/
theorem originalWholeEndpointArrowIso_hom_left {A B E : C} (e : A ≅ B)
    (r : A ⟶ E) (q : B ⟶ E) (h : e.hom ≫ q = r) :
    (originalWholeEndpointArrowIso e r q h).hom.left = e.hom := rfl

/-- The full forward Arrow base function retains its complete original identity clause. -/
theorem originalWholeEndpointArrowIso_hom_right {A B E : C} (e : A ≅ B)
    (r : A ⟶ E) (q : B ⟶ E) (h : e.hom ≫ q = r) :
    (originalWholeEndpointArrowIso e r q h).hom.right = 𝟙 E := rfl

/-- The full inverse Arrow total function retains its complete original comparison clause. -/
theorem originalWholeEndpointArrowIso_inv_left {A B E : C} (e : A ≅ B)
    (r : A ⟶ E) (q : B ⟶ E) (h : e.hom ≫ q = r) :
    (originalWholeEndpointArrowIso e r q h).inv.left = e.inv := rfl

/-- The full inverse Arrow base function retains its complete original identity clause. -/
theorem originalWholeEndpointArrowIso_inv_right {A B E : C} (e : A ≅ B)
    (r : A ⟶ E) (q : B ⟶ E) (h : e.hom ≫ q = r) :
    (originalWholeEndpointArrowIso e r q h).inv.right = 𝟙 E := rfl

end CategoryTheory.OriginalLoopedEndpointCoherenceGeometry

end

section
universe u
open CategoryTheory

namespace CategoryTheory.OriginalLoopedConnectingCompositionGeometry

universe u₁ v₁
variable {C : Type u₁} [Category.{v₁} C]

/-- The complete original identity composition is fixed before its native specialization. -/
theorem originalWholeIdentityComposition (A : C) : 𝟙 A = 𝟙 A ≫ 𝟙 A :=
  (Category.id_comp (𝟙 A)).symm

/-- The whole original lift composition retains all complete comparison maps and projections
before the exact native specialization. -/
theorem originalWholeLoopedConnectingProjection {A B D E P : C}
    (l : A ⟶ D) (f : A ⟶ B) (g : B ⟶ D) (a : D ⟶ P)
    (b : B ⟶ E) (c : E ⟶ P) (s : A ⟶ E)
    (hl : l = f ≫ g) (hga : g ≫ a = b ≫ c) (hfb : f ≫ b = s) : l ≫ a = s ≫ c := by
  rw [hl, Category.assoc, hga, ← Category.assoc, hfb]

end CategoryTheory.OriginalLoopedConnectingCompositionGeometry

end


section
universe u v
open CategoryTheory

namespace CategoryTheory.OriginalNativeChosenConnectingCompositionGeometry

universe u₁ v₁
variable {C : Type u₁} [Category.{v₁} C]

/-- The complete original structure square retains its whole postcomposed comparison before
the exact native selected-fiber specialization. -/
theorem originalWholeFollowedSquare {A B D E P : C}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ E) (k : E ⟶ D) (p : D ⟶ P)
    (hs : f ≫ g = h ≫ k) : f ≫ (g ≫ p) = h ≫ (k ≫ p) := by
  rw [← Category.assoc, hs, Category.assoc]

end CategoryTheory.OriginalNativeChosenConnectingCompositionGeometry

end
