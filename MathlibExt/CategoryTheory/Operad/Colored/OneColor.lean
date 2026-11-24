/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Operad.Colored.Profile

/-!
# One-colored profiles

Finite colored profiles with color type `PUnit` recover the finite-bijection groupoid. This file
constructs the comparison functors and their categorical equivalence. It is the compatibility gate
between the colored indexing layer and the one-colored symmetric collections of O1.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

namespace ColoredProfile

universe c

/-- Regard a finite type as a profile with the unique color on every input and output. -/
def oneColorFunctor : FinBijGroupoid ⥤ ColoredProfile PUnit where
  obj X :=
    { inputs := X.of
      inputColor := fun _ => PUnit.unit
      outputColor := PUnit.unit }
  map f :=
    { inputEquiv := FinBijGroupoid.equivOfHom f
      inputColor_eq := fun _ => rfl
      outputColor_eq := rfl }
  map_id X := by
    apply Hom.ext
    exact FinBijGroupoid.equivOfHom_id X
  map_comp f g := by
    apply Hom.ext
    exact FinBijGroupoid.equivOfHom_comp f g

/-- Forget the colors of a one-colored profile. -/
abbrev forgetOneColorFunctor : ColoredProfile PUnit ⥤ FinBijGroupoid :=
  arityFunctor PUnit

@[simp]
theorem oneColorFunctor_obj_inputs (X : FinBijGroupoid) :
    (oneColorFunctor.obj X).inputs = X.of :=
  rfl

@[simp]
theorem oneColorFunctor_map_inputEquiv {X Y : FinBijGroupoid} (f : X ⟶ Y) :
    (oneColorFunctor.map f).inputEquiv = FinBijGroupoid.equivOfHom f :=
  rfl

@[simp]
theorem forgetOneColorFunctor_obj (P : ColoredProfile PUnit) :
    (forgetOneColorFunctor.obj P).of = P.inputs :=
  rfl

@[simp]
theorem forgetOneColorFunctor_map {P Q : ColoredProfile PUnit} (f : P ⟶ Q) :
    FinBijGroupoid.equivOfHom (forgetOneColorFunctor.map f) = f.inputEquiv := by
  exact FinBijGroupoid.equivOfHom_homOfEquiv f.inputEquiv

/-- The unit of the equivalence between finite arities and one-colored profiles. -/
def oneColorUnitIso : 𝟭 FinBijGroupoid ≅ oneColorFunctor ⋙ forgetOneColorFunctor :=
  NatIso.ofComponents (fun X => Iso.refl X) (by
    intro X Y f
    change f ≫ 𝟙 Y = 𝟙 X ≫ FinBijGroupoid.homOfEquiv (FinBijGroupoid.equivOfHom f)
    simp)

@[simp]
theorem oneColorUnitIso_hom_app (X : FinBijGroupoid) :
    oneColorUnitIso.hom.app X = 𝟙 X :=
  rfl

@[simp]
theorem oneColorUnitIso_inv_app (X : FinBijGroupoid) :
    oneColorUnitIso.inv.app X = 𝟙 X :=
  rfl

/-- The canonical color-preserving map from the constant one-colored profile to a given
one-colored profile with the same inputs. -/
def oneColorCounitHom (P : ColoredProfile PUnit) :
    (forgetOneColorFunctor ⋙ oneColorFunctor).obj P ⟶ P where
  inputEquiv := Equiv.refl _
  inputColor_eq := fun _ => Subsingleton.elim _ _
  outputColor_eq := Subsingleton.elim _ _

/-- The counit of the equivalence between finite arities and one-colored profiles. -/
noncomputable def oneColorCounitIso :
    forgetOneColorFunctor ⋙ oneColorFunctor ≅ 𝟭 (ColoredProfile PUnit) :=
  NatIso.ofComponents (fun P => asIso (oneColorCounitHom P)) (by
    intro P Q f
    apply Hom.ext
    rfl)

@[simp]
theorem oneColorCounitIso_hom_app (P : ColoredProfile PUnit) :
    oneColorCounitIso.hom.app P = oneColorCounitHom P :=
  rfl

@[simp]
theorem oneColorCounitIso_inv_app (P : ColoredProfile PUnit) :
    oneColorCounitIso.inv.app P = Groupoid.inv (oneColorCounitHom P) :=
  (Groupoid.inv_eq_inv (oneColorCounitHom P)).symm

/-- Forgetting colors sends the one-color counit to the identity relabelling. -/
@[simp]
theorem forgetOneColorFunctor_map_oneColorCounitHom (P : ColoredProfile PUnit) :
    forgetOneColorFunctor.map (oneColorCounitHom P) =
      𝟙 (forgetOneColorFunctor.obj P) := by
  apply CategoryTheory.Core.hom_ext
  apply FintypeCat.hom_ext
  intro i
  rfl

/-- The chosen unit and counit satisfy the triangle identity. -/
theorem oneColor_triangle (X : FinBijGroupoid) :
    oneColorFunctor.{c}.map (oneColorUnitIso.{c}.hom.app X) ≫
        oneColorCounitIso.{c}.hom.app (oneColorFunctor.{c}.obj X) = 𝟙 _ := by
  rw [oneColorUnitIso_hom_app]
  with_unfolding_all
    change 𝟙 _ ≫ oneColorCounitHom (oneColorFunctor.obj X) = 𝟙 _
  rw [Category.id_comp]
  apply Hom.ext
  rfl

/-- The groupoid of one-colored finite profiles is equivalent to the finite-bijection groupoid. -/
noncomputable def oneColorEquivalence : FinBijGroupoid ≌ ColoredProfile PUnit :=
  CategoryTheory.Equivalence.mk' oneColorFunctor forgetOneColorFunctor
    oneColorUnitIso oneColorCounitIso oneColor_triangle

@[simp]
theorem oneColorEquivalence_functor : oneColorEquivalence.functor = oneColorFunctor :=
  rfl

@[simp]
theorem oneColorEquivalence_inverse : oneColorEquivalence.inverse = forgetOneColorFunctor :=
  rfl

/-- The unit of the one-color profile equivalence is the chosen normalization isomorphism. -/
@[simp]
theorem oneColorEquivalence_unitIso : oneColorEquivalence.unitIso = oneColorUnitIso :=
  rfl

/-- The counit of the one-color profile equivalence is the chosen denormalization isomorphism. -/
@[simp]
theorem oneColorEquivalence_counitIso : oneColorEquivalence.counitIso = oneColorCounitIso :=
  rfl

end ColoredProfile

end CategoryTheory.Operad
