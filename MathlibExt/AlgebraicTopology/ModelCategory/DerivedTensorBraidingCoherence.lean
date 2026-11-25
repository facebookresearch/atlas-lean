/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedTensorClosedStructure
public import Mathlib.CategoryTheory.Monoidal.Braided.Multifunctor

/-!
# The two hexagons of the actual chosen derived braiding

The source comparisons use the original braiding and original Q counits on
all actual cofibrant endpoints. The naturalities in a derived tensor word
are the already constructed complete naturalities. The original hexagons
and cofibrant computation therefore supply the full derived hexagons.

Source: Hovey, *Model Categories*, Theorem 4.3.2.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory Functor BraidedCategory
open CategoryTheory.BraidedCategory.ofBifunctor
open scoped MonoidalClosed

namespace HomotopicalAlgebra.DerivedTensorConstructions.MonoidalHo

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]
  (d : GeneratedFunctorialReplacements.Data (C := C))

/-- The original pushout-product axiom gives cofibrancy of each source tensor word in the hexagons.
-/
local instance braidingTensorCofibrant {X Y : C} [IsCofibrant X] [IsCofibrant Y] : IsCofibrant
    (X ⊗ Y) :=
  tensor_isCofibrant X Y

/-- The braiding is the exact previously constructed complete derived natural isomorphism. -/
def braidingNatIso : curriedTensor (MonoidalHo d) ≅ (curriedTensor (MonoidalHo d)).flip :=
  derivedBraiding d

/-- Its actual original cofibrant source component uses the original braiding and both Q counits. -/
theorem braidingNatIso_hom_app (X Y : C) [IsCofibrant X] [IsCofibrant Y] :
    ((braidingNatIso d).hom.app ((projection d).obj X)).app ((projection d).obj Y) =
      (μ d X Y).hom ≫ (projection d).map (β_ X Y).hom ≫ (μ d Y X).inv := by
  change ((derivedBraiding d).hom.app ((weakEquivalences C).Q.obj X)).app
      ((weakEquivalences C).Q.obj Y) =
    (cofibrantComparison d X Y).hom ≫ (weakEquivalences C).Q.map (β_ X Y).hom ≫
      (cofibrantComparison d Y X).inv
  exact derivedBraiding_cofibrant d X Y

/-- The inverse source associator keeps the original inverse associator and actual comparisons. -/
theorem associator_inv_app (X Y Z : C) [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z] :
    (α_ ((projection d).obj X) ((projection d).obj Y) ((projection d).obj Z)).inv =
      (projection d).obj X ◁ (μ d Y Z).hom ≫ (μ d X (Y ⊗ Z)).hom ≫
        (projection d).map (α_ X Y Z).inv ≫ (μ d (X ⊗ Y) Z).inv ≫
          (μ d X Y).inv ▷ (projection d).obj Z := by
  change (((derivedAssociator d).inv.app ((weakEquivalences C).Q.obj X)).app
      ((weakEquivalences C).Q.obj Y)).app ((weakEquivalences C).Q.obj Z) =
    ((tensor d).obj ((weakEquivalences C).Q.obj X)).map (cofibrantComparison d Y Z).hom ≫
      (cofibrantComparison d X (Y ⊗ Z)).hom ≫ (weakEquivalences C).Q.map (α_ X Y Z).inv ≫
        (cofibrantComparison d (X ⊗ Y) Z).inv ≫
          ((tensor d).map (cofibrantComparison d X Y).inv).app ((weakEquivalences C).Q.obj Z)
  have h := derivedAssociator_inv_cofibrant d X Y Z
  dsimp [leftCofibrantComparison, rightCofibrantComparison] at h
  simpa only [Category.assoc] using h

@[reassoc]
theorem braidingNatIso_naturality_μ_left (X Y Z : C)
    [IsCofibrant Y] [IsCofibrant Z] :
    ((braidingNatIso d).hom.app ((projection d).obj X)).app
        ((projection d).obj Y ⊗ (projection d).obj Z) ≫
      (μ d Y Z).hom ▷ (projection d).obj X =
    (projection d).obj X ◁ (μ d Y Z).hom ≫
      ((braidingNatIso d).hom.app ((projection d).obj X)).app ((projection d).obj (Y ⊗ Z)) :=
  (((braidingNatIso d).hom.app ((projection d).obj X)).naturality (μ d Y Z).hom).symm

@[reassoc]
theorem braidingNatIso_naturality_μ_right (X Y Z : C)
    [IsCofibrant X] [IsCofibrant Y] :
    ((braidingNatIso d).hom.app ((projection d).obj X ⊗ (projection d).obj Y)).app
        ((projection d).obj Z) ≫
      (projection d).obj Z ◁ (μ d X Y).hom =
    (μ d X Y).hom ▷ (projection d).obj Z ≫
      ((braidingNatIso d).hom.app ((projection d).obj (X ⊗ Y))).app ((projection d).obj Z) :=
  (NatTrans.congr_app ((braidingNatIso d).hom.naturality (μ d X Y).hom)
    ((projection d).obj Z)).symm

/-- The original forward hexagon gives the actual full source forward hexagon. -/
@[reassoc]
theorem map_hexagon_forward (X Y Z : C) [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z] :
    (α_ ((projection d).obj X) ((projection d).obj Y) ((projection d).obj Z)).hom ≫
      ((braidingNatIso d).hom.app ((projection d).obj X)).app
        ((projection d).obj Y ⊗ (projection d).obj Z) ≫
          (α_ ((projection d).obj Y) ((projection d).obj Z) ((projection d).obj X)).hom =
    ((braidingNatIso d).hom.app ((projection d).obj X)).app ((projection d).obj Y) ▷
        (projection d).obj Z ≫
      (α_ ((projection d).obj Y) ((projection d).obj X) ((projection d).obj Z)).hom ≫
        (projection d).obj Y ◁
          ((braidingNatIso d).hom.app ((projection d).obj X)).app ((projection d).obj Z) := by
  simp only [associator_hom_app, braidingNatIso_hom_app, comp_whiskerRight,
    whiskerLeft_comp, Category.assoc]
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp,
    μ_natural_left_assoc]
  rw [braidingNatIso_naturality_μ_left_assoc, braidingNatIso_hom_app]
  simp only [Category.assoc, ← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id,
    Category.id_comp, Iso.inv_hom_id_assoc]
  rw [← μ_inv_natural_right_assoc]
  simp only [← (projection d).map_comp_assoc, BraidedCategory.hexagon_forward]

/-- The complete forward hexagon retains all three homotopy-category morphism variables. -/
theorem hexagon_forward_natTrans :
    (curriedAssociatorNatIso (MonoidalHo d)).hom ≫
      Forward.firstMap₂ (braidingNatIso d) ≫ Forward.firstMap₃ (MonoidalHo d) =
    Forward.secondMap₁ (braidingNatIso d) ≫ Forward.secondMap₂ (MonoidalHo d) ≫
      Forward.secondMap₃ (braidingNatIso d) := by
  apply GeneratedFunctorialReplacements.natTrans₃_ext_cofibrant d
  intro X Y Z _ _ _
  exact map_hexagon_forward d X Y Z

/-- Every whole homotopy triple has the same complete forward hexagon. -/
theorem map_hexagon_forward_all (X Y Z : MonoidalHo d) :
    (α_ X Y Z).hom ≫ ((braidingNatIso d).hom.app X).app (Y ⊗ Z) ≫ (α_ Y Z X).hom =
      ((braidingNatIso d).hom.app X).app Y ▷ Z ≫ (α_ Y X Z).hom ≫
        Y ◁ ((braidingNatIso d).hom.app X).app Z :=
  NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app
    (hexagon_forward_natTrans d) X) Y) Z

/-- The inverse is the same previously proved involutive derived braid with its variables exchanged.
-/
theorem braidingNatIso_inv_eq (X Y : MonoidalHo d) :
    (((braidingNatIso d).app X).app Y).inv = ((braidingNatIso d).hom.app Y).app X := by
  apply (cancel_epi (((braidingNatIso d).app X).app Y).hom).mp
  rw [Iso.hom_inv_id]
  change 𝟙 _ = ((derivedBraiding d).hom.app X).app Y ≫ ((derivedBraiding d).hom.app Y).app X
  exact (derivedBraiding_involutive_app d X Y).symm

/-- Inverting the complete forward hexagon and using the actual derived involution
constructs the reverse hexagon on every homotopy triple. -/
theorem map_hexagon_reverse_all (X Y Z : MonoidalHo d) :
    (α_ X Y Z).inv ≫ ((braidingNatIso d).hom.app (X ⊗ Y)).app Z ≫ (α_ Z X Y).inv =
      X ◁ ((braidingNatIso d).hom.app Y).app Z ≫ (α_ X Z Y).inv ≫
        ((braidingNatIso d).hom.app X).app Z ▷ Y := by
  let L := (α_ Z X Y) ≪≫ ((braidingNatIso d).app Z).app (X ⊗ Y) ≪≫ (α_ X Y Z)
  let R := (tensorRight Y).mapIso (((braidingNatIso d).app Z).app X) ≪≫ (α_ X Z Y) ≪≫
    (tensorLeft X).mapIso (((braidingNatIso d).app Z).app Y)
  have h : L = R := by
    apply Iso.ext
    simpa only [L, R, Iso.trans_hom, Iso.app_hom, CategoryTheory.Functor.mapIso_hom,
      tensorLeft, tensorRight, curriedTensor, Functor.flip, Category.assoc] using
      map_hexagon_forward_all d Z X Y
  have hi := congrArg (fun e => e.inv) h
  simpa only [L, R, Iso.trans_inv, CategoryTheory.Functor.mapIso_inv,
    tensorLeft, tensorRight, curriedTensor, Functor.flip, braidingNatIso_inv_eq,
    Category.assoc] using hi

/-- The complete reverse hexagon is an equality of the original derived natural transformations. -/
theorem hexagon_reverse_natTrans :
    (curriedAssociatorNatIso (MonoidalHo d)).inv ≫
      Reverse.firstMap₂ (braidingNatIso d) ≫ Reverse.firstMap₃ (MonoidalHo d) =
    Reverse.secondMap₁ (braidingNatIso d) ≫ Reverse.secondMap₂ (MonoidalHo d) ≫
      Reverse.secondMap₃ (braidingNatIso d) := by
  apply NatTrans.ext
  funext X
  apply NatTrans.ext
  funext Y
  apply NatTrans.ext
  funext Z
  exact map_hexagon_reverse_all d X Y Z

/-- The actual chosen derived braid and both earned full hexagons construct the braided structure.
-/
instance braidedCategory : BraidedCategory (MonoidalHo d) :=
  BraidedCategory.ofBifunctor (braidingNatIso d) (hexagon_forward_natTrans d)
      (hexagon_reverse_natTrans d)

/-- The same original full derived involution constructs the symmetric structure. -/
instance symmetricCategory : SymmetricCategory (MonoidalHo d) := by
  apply SymmetricCategory.ofCurried
  apply NatTrans.ext
  funext X
  apply NatTrans.ext
  funext Y
  change ((derivedBraiding d).hom.app X).app Y ≫ ((derivedBraiding d).hom.app Y).app X = 𝟙 _
  exact derivedBraiding_involutive_app d X Y

end HomotopicalAlgebra.DerivedTensorConstructions.MonoidalHo
