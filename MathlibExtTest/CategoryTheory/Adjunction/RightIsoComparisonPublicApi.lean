/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Adjunction.RightIsoComparison

/-!
# Public callers of the adjunction right-comparison API

Construct the Hom equivalence using both actual comparison directions and
recover the given second adjunction. No spectra module is imported.
-/

set_option autoImplicit false
noncomputable section
universe uA vA uB vB

open CategoryTheory
open CategoryTheory.Adjunction.RightIsoComparison

namespace MathlibExtTest.AdjunctionRightIsoComparison

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {V L : A ⥤ B} {W R : B ⥤ A}

/-- Construct both Hom functions from the actual left and right comparison maps. -/
def comparisonHomEquiv (a : V ⊣ W) (b : L ⊣ R) (r : W ≅ R) (X : A) (Y : B) :
    (L.obj X ⟶ Y) ≃ (X ⟶ R.obj Y) where
  toFun f := a.homEquiv X Y ((comparison a b r).hom.app X ≫ f) ≫ r.hom.app Y
  invFun g := (comparison a b r).inv.app X ≫ (a.homEquiv X Y).symm (g ≫ r.inv.app Y)
  left_inv f := by
    calc
      _ = (comparison a b r).inv.app X ≫
          (a.homEquiv X Y).symm (b.homEquiv X Y f ≫ r.inv.app Y) :=
        congrArg (fun g => (comparison a b r).inv.app X ≫
          (a.homEquiv X Y).symm (g ≫ r.inv.app Y)) (forward a b r X Y f)
      _ = (comparison a b r).inv.app X ≫
          ((comparison a b r).hom.app X ≫ (b.homEquiv X Y).symm (b.homEquiv X Y f)) :=
        congrArg (fun g => (comparison a b r).inv.app X ≫ g)
          (inverse a b r X Y (b.homEquiv X Y f))
      _ = (b.homEquiv X Y).symm (b.homEquiv X Y f) := by
        rw [← Category.assoc, (comparison a b r).inv_hom_id_app, Category.id_comp]
      _ = f := (b.homEquiv X Y).symm_apply_apply f
  right_inv g := by
    have hi : (comparison a b r).inv.app X ≫
        (a.homEquiv X Y).symm (g ≫ r.inv.app Y) = (b.homEquiv X Y).symm g := by
      calc
        _ = (comparison a b r).inv.app X ≫
            ((comparison a b r).hom.app X ≫ (b.homEquiv X Y).symm g) :=
          congrArg (fun f => (comparison a b r).inv.app X ≫ f) (inverse a b r X Y g)
        _ = _ := by
          rw [← Category.assoc, (comparison a b r).inv_hom_id_app, Category.id_comp]
    calc
      _ = a.homEquiv X Y ((comparison a b r).hom.app X ≫
          (b.homEquiv X Y).symm g) ≫ r.hom.app Y :=
        congrArg (fun f => a.homEquiv X Y ((comparison a b r).hom.app X ≫ f) ≫ r.hom.app Y) hi
      _ = b.homEquiv X Y ((b.homEquiv X Y).symm g) :=
        forward a b r X Y ((b.homEquiv X Y).symm g)
      _ = g := (b.homEquiv X Y).apply_symm_apply g

/-- The equivalence built from the comparison retains the entire chosen second Hom correspondence. -/
theorem comparisonHomEquiv_eq (a : V ⊣ W) (b : L ⊣ R) (r : W ≅ R) (X : A) (Y : B) :
    comparisonHomEquiv a b r X Y = b.homEquiv X Y := by
  apply Equiv.ext
  intro f
  exact forward a b r X Y f

example (a : V ⊣ R) (b : L ⊣ R) (X : A) (Y : B) (f : L.obj X ⟶ Y) :
    a.homEquiv X Y ((a.leftAdjointUniq b).hom.app X ≫ f) = b.homEquiv X Y f :=
  common_forward a b X Y f

example (a : V ⊣ R) (b : L ⊣ R) (X : A) (Y : B) (g : X ⟶ R.obj Y) :
    (a.homEquiv X Y).symm g =
      (a.leftAdjointUniq b).hom.app X ≫ (b.homEquiv X Y).symm g :=
  common_inverse a b X Y g

example (a : V ⊣ W) (r : W ≅ R) (X : A) (Y : B) :
    (transported a r).unit.app X = a.unit.app X ≫ r.hom.app (V.obj X) ∧
    (transported a r).counit.app Y = V.map (r.inv.app Y) ≫ a.counit.app Y :=
  ⟨transported_unit a r X, transported_counit a r Y⟩

/-- Both directions of the unit and counit comparison retain all of their given morphisms. -/
theorem comparison_squares (a : V ⊣ W) (b : L ⊣ R) (r : W ≅ R) (X : A) (Y : B) :
    a.unit.app X ≫ r.hom.app (V.obj X) ≫ R.map ((comparison a b r).hom.app X) = b.unit.app X ∧
    (comparison a b r).hom.app (R.obj Y) ≫ b.counit.app Y =
      V.map (r.inv.app Y) ≫ a.counit.app Y ∧
    b.unit.app X ≫ R.map ((comparison a b r).inv.app X) =
      a.unit.app X ≫ r.hom.app (V.obj X) ∧
    (comparison a b r).inv.app (R.obj Y) ≫ V.map (r.inv.app Y) ≫ a.counit.app Y = b.counit.app Y :=
  ⟨unit a b r X, counit a b r Y, inverse_unit a b r X, inverse_counit a b r Y⟩

example (a : V ⊣ W) (b : L ⊣ R) (r : W ≅ R) (X : A) (Y : B) (h : L.obj X ⟶ Y) :
    a.unit.app X ≫ r.hom.app (V.obj X) ≫ R.map ((comparison a b r).hom.app X ≫ h) =
      b.unit.app X ≫ R.map h :=
  unit_postcompose a b r X Y h

example (R : B ⥤ A) {X : A} {Y Z : B} (i : Y ≅ Z)
    (p : X ⟶ R.obj Y) (q : X ⟶ R.obj Z) (h : p ≫ R.map i.hom = q) :
    p = q ≫ R.map i.inv :=
  eq_comp_map_inv R i p q h

/-- The comparisons cancel on their full original carriers. -/
theorem comparison_inverses (a : V ⊣ W) (b : L ⊣ R) (r : W ≅ R) (X : A) (Y : B) :
    (comparison a b r).hom.app X ≫ (comparison a b r).inv.app X = 𝟙 (V.obj X) ∧
    (comparison a b r).inv.app X ≫ (comparison a b r).hom.app X = 𝟙 (L.obj X) ∧
    r.hom.app Y ≫ r.inv.app Y = 𝟙 (W.obj Y) ∧ r.inv.app Y ≫ r.hom.app Y = 𝟙 (R.obj Y) :=
  ⟨(comparison a b r).hom_inv_id_app X, (comparison a b r).inv_hom_id_app X,
    r.hom_inv_id_app Y, r.inv_hom_id_app Y⟩

/-- Both compared adjunctions keep their triangle identities, including the actual right transport. -/
theorem comparison_triangles (a : V ⊣ W) (b : L ⊣ R) (r : W ≅ R) (X : A) (Y : B) :
    V.map ((transported a r).unit.app X) ≫ (transported a r).counit.app (V.obj X) = 𝟙 (V.obj X) ∧
    (transported a r).unit.app (R.obj Y) ≫ R.map ((transported a r).counit.app Y) = 𝟙 (R.obj Y) ∧
    L.map (b.unit.app X) ≫ b.counit.app (L.obj X) = 𝟙 (L.obj X) ∧
    b.unit.app (R.obj Y) ≫ R.map (b.counit.app Y) = 𝟙 (R.obj Y) :=
  ⟨(transported a r).left_triangle_components X, (transported a r).right_triangle_components Y,
    b.left_triangle_components X, b.right_triangle_components Y⟩

/-- Comparing an adjunction with itself through the identity right comparison keeps its Hom equivalence. -/
theorem self_comparisonHomEquiv (a : V ⊣ W) (X : A) (Y : B) :
    comparisonHomEquiv a a (Iso.refl W) X Y = a.homEquiv X Y :=
  comparisonHomEquiv_eq a a (Iso.refl W) X Y

example (X Y : A) (f : X ⟶ Y) :
    comparisonHomEquiv (Adjunction.id (C := A)) (Adjunction.id (C := A))
      (Iso.refl (𝟭 A)) X Y f = f := by
  rw [comparisonHomEquiv_eq]
  rw [(Adjunction.id (C := A)).homEquiv_unit]
  exact Category.id_comp f

example (X Y : A) (f : X ⟶ Y) :
    (comparisonHomEquiv (Adjunction.id (C := A)) (Adjunction.id (C := A))
      (Iso.refl (𝟭 A)) X Y).symm f = f := by
  rw [comparisonHomEquiv_eq]
  rw [(Adjunction.id (C := A)).homEquiv_counit]
  exact Category.comp_id f

#print axioms self_comparisonHomEquiv
#print axioms comparisonHomEquiv
#print axioms comparisonHomEquiv_eq
#print axioms comparison_squares
#print axioms comparison_inverses
#print axioms comparison_triangles
#print axioms CategoryTheory.Adjunction.RightIsoComparison.common_forward
#print axioms CategoryTheory.Adjunction.RightIsoComparison.common_inverse
#print axioms CategoryTheory.Adjunction.RightIsoComparison.transported
#print axioms CategoryTheory.Adjunction.RightIsoComparison.comparison
#print axioms CategoryTheory.Adjunction.RightIsoComparison.forward
#print axioms CategoryTheory.Adjunction.RightIsoComparison.inverse
#print axioms CategoryTheory.Adjunction.RightIsoComparison.transported_unit
#print axioms CategoryTheory.Adjunction.RightIsoComparison.transported_counit
#print axioms CategoryTheory.Adjunction.RightIsoComparison.unit
#print axioms CategoryTheory.Adjunction.RightIsoComparison.counit
#print axioms CategoryTheory.Adjunction.RightIsoComparison.inverse_unit
#print axioms CategoryTheory.Adjunction.RightIsoComparison.inverse_counit
#print axioms CategoryTheory.Adjunction.RightIsoComparison.unit_postcompose
#print axioms CategoryTheory.Adjunction.RightIsoComparison.eq_comp_map_inv

end MathlibExtTest.AdjunctionRightIsoComparison
