/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSZeroComponentHomology
public import Mathlib.CategoryTheory.Preadditive.SingleObj
public import Mathlib.Data.ZMod.Basic

/-! # Tests for the additive S⁻¹S zero-component homology summand -/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe v u

namespace CategoryTheory.SInverseSZeroComponentHomologyTests

open SInverseS

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

example : SSet.π₀ (nerve (SInverseS.Pair C)) :=
  zeroComponentNerveIndex C

example : (nerve (SInverseS.Pair C)).Subcomplex :=
  zeroComponentNerveComponent C

example :
    nerve (SInverseS.ZeroComponent (C := C)) ≅
      (zeroComponentNerveComponent C : SSet.{max u v}) :=
  zeroComponentNerveIso C

/- The degree-zero forward comparison retains its underlying `Pair C`
vertex. -/
example
    (z : (nerve (SInverseS.ZeroComponent (C := C))).obj (op ⦋0⦌)) :
    ((zeroComponentNerveIso C).hom.app (op ⦋0⦌) z).1 =
      (nerveMap (zeroComponentProperty (C := C)).ι).app (op ⦋0⦌) z :=
  zeroComponentNerveIso_hom_app_val C z

/- The degree-zero inverse comparison retains the underlying object. -/
example
    (z : (zeroComponentNerveComponent C).obj (op ⦋0⦌)) :
    (((zeroComponentNerveIso C).inv.app (op ⦋0⦌) z).obj 0).obj =
      z.1.obj 0 :=
  zeroComponentNerveIso_inv_app_obj C 0 z 0

/- The degree-one inverse comparison retains both underlying objects. -/
example
    (z : (zeroComponentNerveComponent C).obj (op ⦋1⦌))
    (i : Fin 2) :
    (((zeroComponentNerveIso C).inv.app (op ⦋1⦌) z).obj i).obj =
      z.1.obj i :=
  zeroComponentNerveIso_inv_app_obj C 1 z i

/- The degree-one inverse comparison retains the selected underlying map. -/
example
    (z : (zeroComponentNerveComponent C).obj (op ⦋1⦌)) :
    (((zeroComponentNerveIso C).inv.app (op ⦋1⦌) z).map
        (homOfLE (show (0 : Fin 2) ≤ 1 by decide))).hom =
      z.1.map (homOfLE (show (0 : Fin 2) ≤ 1 by decide)) :=
  zeroComponentNerveIso_inv_app_map_hom C 1 z
    (homOfLE (show (0 : Fin 2) ≤ 1 by decide))

example :
    (zeroComponentNerveIso C).hom ≫
        (zeroComponentNerveComponent C).ι =
      nerveMap (zeroComponentProperty (C := C)).ι :=
  zeroComponentNerveIso_hom_comp_ι C

example (R : AddCommGrpCat.{max u v}) (n : ℕ) :
    (nerve (SInverseS.ZeroComponent (C := C))).homology R n ≅
      (zeroComponentNerveComponent C : SSet.{max u v}).homology R n :=
  zeroComponentNerveHomologyIso C R n

example (R : AddCommGrpCat.{max u v}) (n : ℕ) :
    SSet.homologyMap
          (nerveMap (zeroComponentProperty (C := C)).ι) R n ≫
        (SSet.homologyComponentsIso (nerve (SInverseS.Pair C)) R n).hom =
      (zeroComponentNerveHomologyIso C R n).hom ≫
        Sigma.ι
          (fun d : SSet.π₀ (nerve (SInverseS.Pair C)) =>
            (SSet.π₀.component d : SSet.{max u v}).homology R n)
          (zeroComponentNerveIndex C) :=
  zeroComponentHomologyMap_comp_homologyComponentsIso_hom C R n

example (R : AddCommGrpCat.{max u v}) (n : ℕ) :
    SplitMono (SSet.homologyMap
      (nerveMap (zeroComponentProperty (C := C)).ι) R n) :=
  zeroComponentHomologyMapSplitMono C R n

example (R : AddCommGrpCat.{max u v}) (n : ℕ) :
    IsSplitMono (SSet.homologyMap
      (nerveMap (zeroComponentProperty (C := C)).ι) R n) :=
  inferInstance

example (R : AddCommGrpCat.{max u v}) (n : ℕ) :
    SSet.homologyMap
          (nerveMap (zeroComponentProperty (C := C)).ι) R n ≫
        (zeroComponentHomologyMapSplitMono C R n).retraction =
      𝟙 ((nerve (SInverseS.ZeroComponent (C := C))).homology R n) :=
  (zeroComponentHomologyMapSplitMono C R n).id

private abbrev ZeroCategory := SingleObj (ZMod 1)

private instance (X Y : ZeroCategory) : Subsingleton (X ⟶ Y) :=
  inferInstanceAs (Subsingleton (ZMod 1))

private instance : HasZeroObject ZeroCategory where
  zero :=
    ⟨SingleObj.star (ZMod 1),
      (IsZero.iff_id_eq_zero _).2 (Subsingleton.elim _ _)⟩

private instance : HasBinaryBiproducts ZeroCategory where
  has_binary_biproduct X Y := by
    apply hasBinaryBiproduct_of_total
      { pt := SingleObj.star (ZMod 1)
        fst := 0
        snd := 0
        inl := 0
        inr := 0
        inl_fst := Subsingleton.elim _ _
        inl_snd := Subsingleton.elim _ _
        inr_fst := Subsingleton.elim _ _
        inr_snd := Subsingleton.elim _ _ }
    exact Subsingleton.elim _ _

example :
    nerve (SInverseS.ZeroComponent (C := ZeroCategory)) ≅
      (zeroComponentNerveComponent ZeroCategory : SSet.{0}) :=
  zeroComponentNerveIso ZeroCategory

example : IsSplitMono
    (SSet.homologyMap
      (nerveMap (zeroComponentProperty (C := ZeroCategory)).ι)
      (AddCommGrpCat.of (ZMod 1)) 0) :=
  inferInstance

section UniverseOne

variable (C₁ : Type 1) [Category.{1} C₁] [Preadditive C₁]
  [HasZeroObject C₁] [HasBinaryBiproducts C₁]

example :
    nerve (SInverseS.ZeroComponent (C := C₁)) ≅
      (zeroComponentNerveComponent C₁ : SSet.{1}) :=
  zeroComponentNerveIso C₁

example (R₁ : AddCommGrpCat.{1}) : IsSplitMono
    (SSet.homologyMap
      (nerveMap (zeroComponentProperty (C := C₁)).ι) R₁ 1) :=
  inferInstance

end UniverseOne

#print axioms zeroComponentNerveIso
#print axioms zeroComponentNerveIso_hom_comp_ι
#print axioms zeroComponentNerveHomologyIso
#print axioms zeroComponentHomologyMap_comp_homologyComponentsIso_hom
#print axioms zeroComponentHomologyMapSplitMono

end CategoryTheory.SInverseSZeroComponentHomologyTests

end
