/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Comparing adjunctions along an isomorphism of right adjoints

For adjunctions `V ⊣ W` and `L ⊣ R` and a natural isomorphism `W ≅ R`,
transport the first adjunction and use uniqueness of left adjoints to obtain
`V ≅ L`. The comparison preserves both Hom functions and the unit and counit
in each direction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open CategoryTheory

namespace CategoryTheory.Adjunction.RightIsoComparison
universe uA vA uB vB
variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {V L : A ⥤ B} {W R : B ⥤ A}

/-- The canonical comparison between left adjoints preserves the forward Hom correspondence. -/
theorem common_forward (a : V ⊣ R) (b : L ⊣ R) (X : A) (Y : B) (f : L.obj X ⟶ Y) :
    a.homEquiv X Y ((a.leftAdjointUniq b).hom.app X ≫ f) = b.homEquiv X Y f := by
  have h := a.homEquiv_naturality_right ((a.leftAdjointUniq b).hom.app X) f
  have hu := Adjunction.homEquiv_leftAdjointUniq_hom_app a b X
  exact h.trans ((congrArg (fun q => q ≫ R.map f) hu).trans (b.homEquiv_unit X Y f).symm)

/-- The canonical comparison between left adjoints preserves the inverse Hom correspondence. -/
theorem common_inverse (a : V ⊣ R) (b : L ⊣ R) (X : A) (Y : B) (g : X ⟶ R.obj Y) :
    (a.homEquiv X Y).symm g =
      (a.leftAdjointUniq b).hom.app X ≫ (b.homEquiv X Y).symm g := by
  apply (a.homEquiv X Y).injective
  exact ((a.homEquiv X Y).apply_symm_apply g).trans
    (((b.homEquiv X Y).apply_symm_apply g).symm.trans
      (common_forward a b X Y ((b.homEquiv X Y).symm g)).symm)

/-- Transport an adjunction along a natural isomorphism of right adjoints. -/
def transported (a : V ⊣ W) (r : W ≅ R) : V ⊣ R := a.ofNatIsoRight r

/-- Compare left adjoints using the given isomorphism of their right adjoints. -/
def comparison (a : V ⊣ W) (b : L ⊣ R) (r : W ≅ R) : V ≅ L :=
  (transported a r).leftAdjointUniq b

/-- The left and right comparisons preserve the forward Hom correspondence. -/
theorem forward (a : V ⊣ W) (b : L ⊣ R) (r : W ≅ R) (X : A) (Y : B) (f : L.obj X ⟶ Y) :
    a.homEquiv X Y ((comparison a b r).hom.app X ≫ f) ≫ r.hom.app Y = b.homEquiv X Y f :=
  (Adjunction.homEquiv_ofNatIsoRight_apply a r _).symm.trans
    (common_forward (transported a r) b X Y f)

/-- The left and right comparisons preserve the inverse Hom correspondence. -/
theorem inverse (a : V ⊣ W) (b : L ⊣ R) (r : W ≅ R) (X : A) (Y : B) (g : X ⟶ R.obj Y) :
    (a.homEquiv X Y).symm (g ≫ r.inv.app Y) =
      (comparison a b r).hom.app X ≫ (b.homEquiv X Y).symm g :=
  (Adjunction.homEquiv_ofNatIsoRight_symm_apply a r g).symm.trans
    (common_inverse (transported a r) b X Y g)

/-- The transported unit is the given unit followed by the right comparison. -/
theorem transported_unit (a : V ⊣ W) (r : W ≅ R) (X : A) :
    (transported a r).unit.app X = a.unit.app X ≫ r.hom.app (V.obj X) := rfl

/-- The transported counit is the mapped inverse right comparison followed by the given counit. -/
theorem transported_counit (a : V ⊣ W) (r : W ≅ R) (Y : B) :
    (transported a r).counit.app Y = V.map (r.inv.app Y) ≫ a.counit.app Y := rfl

/-- The left and right comparisons carry the first adjunction unit to the second. -/
theorem unit (a : V ⊣ W) (b : L ⊣ R) (r : W ≅ R) (X : A) :
    a.unit.app X ≫ r.hom.app (V.obj X) ≫ R.map ((comparison a b r).hom.app X) = b.unit.app X := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (transported a r) b X
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ R.map ((comparison a b r).hom.app X))
      (transported_unit a r X)).symm.trans h)

/-- The left and right comparisons carry the first adjunction counit to the second. -/
theorem counit (a : V ⊣ W) (b : L ⊣ R) (r : W ≅ R) (Y : B) :
    (comparison a b r).hom.app (R.obj Y) ≫ b.counit.app Y =
      V.map (r.inv.app Y) ≫ a.counit.app Y :=
  (Adjunction.leftAdjointUniq_hom_app_counit (transported a r) b Y).trans (transported_counit a r Y)

/-- The inverse left comparison recovers the first transported unit. -/
theorem inverse_unit (a : V ⊣ W) (b : L ⊣ R) (r : W ≅ R) (X : A) :
    b.unit.app X ≫ R.map ((comparison a b r).inv.app X) =
      a.unit.app X ≫ r.hom.app (V.obj X) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app b (transported a r) X
  have hi := Adjunction.leftAdjointUniq_inv_app (transported a r) b X
  exact (congrArg (fun q => b.unit.app X ≫ R.map q) hi).trans
    (h.trans (transported_unit a r X))

/-- The inverse left comparison recovers the second counit from the first transported counit. -/
theorem inverse_counit (a : V ⊣ W) (b : L ⊣ R) (r : W ≅ R) (Y : B) :
    (comparison a b r).inv.app (R.obj Y) ≫
      V.map (r.inv.app Y) ≫ a.counit.app Y = b.counit.app Y := by
  have h := Adjunction.leftAdjointUniq_hom_app_counit b (transported a r) Y
  have hi := Adjunction.leftAdjointUniq_inv_app (transported a r) b (R.obj Y)
  exact (congrArg (fun q => q ≫ V.map (r.inv.app Y) ≫ a.counit.app Y) hi).trans
    ((congrArg (fun q => (b.leftAdjointUniq (transported a r)).hom.app (R.obj Y) ≫ q)
      (transported_counit a r Y)).symm.trans h)

/-- Postcomposition preserves the complete unit comparison. -/
theorem unit_postcompose (a : V ⊣ W) (b : L ⊣ R) (r : W ≅ R)
    (X : A) (Y : B) (h : L.obj X ⟶ Y) :
    a.unit.app X ≫ r.hom.app (V.obj X) ≫
      R.map ((comparison a b r).hom.app X ≫ h) = b.unit.app X ≫ R.map h := by
  rw [Functor.map_comp]
  calc
    _ = (a.unit.app X ≫ r.hom.app (V.obj X) ≫
        R.map ((comparison a b r).hom.app X)) ≫ R.map h := by
      simp only [Category.assoc]
    _ = _ := congrArg (fun q => q ≫ R.map h) (unit a b r X)

omit V L W in
/-- Recover a morphism before a mapped isomorphism from its postcomposition equation. -/
theorem eq_comp_map_inv (R : B ⥤ A) {X : A} {Y Z : B} (i : Y ≅ Z)
    (p : X ⟶ R.obj Y) (q : X ⟶ R.obj Z) (h : p ≫ R.map i.hom = q) :
    p = q ≫ R.map i.inv :=
  (R.mapIso i).eq_comp_inv.mpr h

end CategoryTheory.Adjunction.RightIsoComparison
