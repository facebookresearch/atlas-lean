/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Whole Arrow comparison between two given pullback corners

Three endpoint isomorphisms and their actual cospan equations
transport the caller's first pullback to its second pullback.
Both complete projection functions are retained. A fourth source
isomorphism and the two actual corner equations then give the
whole Arrow isomorphism, including both coefficient Hom functions.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ChosenPullbackArrowIso

variable {C : Type u} [Category.{v} C]
  {P X Y Z P' X' Y' Z' : C}
  (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
  (fst' : P' ⟶ X') (snd' : P' ⟶ Y') (f' : X' ⟶ Z') (g' : Y' ⟶ Z')
  (pb : IsPullback fst snd f g) (pb' : IsPullback fst' snd' f' g')
  (eX : X ≅ X') (eY : Y ≅ Y') (eZ : Z ≅ Z')
  (hf : f ≫ eZ.hom = eX.hom ≫ f') (hg : g ≫ eZ.hom = eY.hom ≫ g')

include pb hf hg

/-- The original first cone is transported along the three supplied
isomorphisms. Its vertex remains the caller's actual original `P`. -/
theorem transportedSquare : IsPullback (fst ≫ eX.hom) (snd ≫ eY.hom) f' g' :=
  pb.of_iso (Iso.refl P) eX eY eZ
    (Category.id_comp _).symm (Category.id_comp _).symm hf hg

/-- The full chosen pullback comparison is constructed from these
same two original limiting cones. -/
def pointIso : P ≅ P' :=
  (transportedSquare fst snd f g f' g' pb eX eY eZ hf hg).isoIsPullback X' Y' pb'

/-- The entire first forward projection retains the actual `eX`. -/
theorem pointIso_hom_fst :
    (pointIso fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg).hom ≫ fst' =
      fst ≫ eX.hom :=
  (transportedSquare fst snd f g f' g' pb eX eY eZ hf hg).isoIsPullback_hom_fst _ _ pb'

/-- The entire second forward projection retains the actual `eY`. -/
theorem pointIso_hom_snd :
    (pointIso fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg).hom ≫ snd' =
      snd ≫ eY.hom :=
  (transportedSquare fst snd f g f' g' pb eX eY eZ hf hg).isoIsPullback_hom_snd _ _ pb'

/-- The entire first inverse projection is the original inverse
endpoint map, with no pullback selected again. -/
theorem pointIso_inv_fst :
    (pointIso fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg).inv ≫ fst =
      fst' ≫ eX.inv := by
  apply (cancel_mono eX.hom).mp
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact
    (transportedSquare fst snd f g f' g' pb eX eY eZ hf hg).isoIsPullback_inv_fst _ _ pb'

/-- The entire second inverse projection is the original inverse
endpoint map, with the caller's original second coordinate. -/
theorem pointIso_inv_snd :
    (pointIso fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg).inv ≫ snd =
      snd' ≫ eY.inv := by
  apply (cancel_mono eY.hom).mp
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact
    (transportedSquare fst snd f g f' g' pb eX eY eZ hf hg).isoIsPullback_inv_snd _ _ pb'

/-- The forward comparison is exactly the full lift with both
original endpoint coordinates. -/
theorem pointIso_hom_eq_lift :
    (pointIso fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg).hom =
      pb'.lift (fst ≫ eX.hom) (snd ≫ eY.hom)
        (transportedSquare fst snd f g f' g' pb eX eY eZ hf hg).w := by
  apply pb'.hom_ext
  · rw [pointIso_hom_fst, pb'.lift_fst]
  · rw [pointIso_hom_snd, pb'.lift_snd]

section Arrow

variable {S S' : C} (φ : S ⟶ P) (ψ : S' ⟶ P') (eS : S ≅ S')
  (hfst : (φ ≫ fst) ≫ eX.hom = (eS.hom ≫ ψ) ≫ fst')
  (hsnd : (φ ≫ snd) ≫ eY.hom = (eS.hom ≫ ψ) ≫ snd')

include hfst hsnd

/-- The two supplied whole corner equations give the complete
original Arrow equation, not only its projections. -/
theorem corner_equation :
    φ ≫ (pointIso fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg).hom =
      eS.hom ≫ ψ := by
  apply pb'.hom_ext
  · rw [Category.assoc, pointIso_hom_fst, ← Category.assoc]
    exact hfst
  · rw [Category.assoc, pointIso_hom_snd, ← Category.assoc]
    exact hsnd

/-- The entire chosen corner Arrow isomorphism keeps the supplied
source isomorphism and the constructed two-leg pullback isomorphism. -/
def arrowIso : Arrow.mk φ ≅ Arrow.mk ψ :=
  Arrow.isoMk' φ ψ eS
    (pointIso fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg)
    (corner_equation fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg φ ψ eS hfst hsnd).symm

theorem arrowIso_hom_left :
    (arrowIso fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg φ ψ eS hfst hsnd).hom.left =
      eS.hom := rfl

theorem arrowIso_hom_right :
    (arrowIso fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg φ ψ eS hfst hsnd).hom.right =
      (pointIso fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg).hom := rfl

theorem arrowIso_inv_left :
    (arrowIso fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg φ ψ eS hfst hsnd).inv.left =
      eS.inv := rfl

theorem arrowIso_inv_right :
    (arrowIso fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg φ ψ eS hfst hsnd).inv.right =
      (pointIso fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg).inv := rfl

end Arrow

/-- Both full coefficient Hom functions use the same actual
chosen-pullback comparison and its actual inverse. -/
def coefficientHomEquiv (T : C) : (T ⟶ P) ≃ (T ⟶ P') where
  toFun h := h ≫ (pointIso fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg).hom
  invFun h := h ≫ (pointIso fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg).inv
  left_inv h := by
    dsimp only
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv h := by
    dsimp only
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem coefficientHomEquiv_forward (T : C) :
    (coefficientHomEquiv fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg T : _ → _) =
      fun h => h ≫ (pointIso fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg).hom := rfl

theorem coefficientHomEquiv_inverse (T : C) :
    ((coefficientHomEquiv fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg T).symm : _ → _) =
      fun h => h ≫ (pointIso fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg).inv := rfl

theorem coefficientHomEquiv_naturality {T T' : C} (a : T' ⟶ T) (h : T ⟶ P) :
    coefficientHomEquiv fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg T' (a ≫ h) =
      a ≫ coefficientHomEquiv fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg T h :=
  Category.assoc _ _ _

theorem coefficientHomEquiv_inverse_naturality {T T' : C} (a : T' ⟶ T) (h : T ⟶ P') :
    (coefficientHomEquiv fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg T').symm (a ≫ h) =
      a ≫ (coefficientHomEquiv fst snd f g fst' snd' f' g' pb pb' eX eY eZ hf hg T).symm h :=
  Category.assoc _ _ _

end CategoryTheory.ChosenPullbackArrowIso
