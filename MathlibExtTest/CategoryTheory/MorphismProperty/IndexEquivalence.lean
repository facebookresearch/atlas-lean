/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.CategoryTheory.MorphismProperty.IndexEquivalence
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Data
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Nat.Defs

/-!# Fixed original-component and complete lifting-class contracts -/
set_option autoImplicit false
noncomputable section
universe uD vD uS vS uM vM
open CategoryTheory MorphismProperty HomotopicalAlgebra

namespace MathlibExtTest.MorphismPropertyIndexEquivalence

variable {D : Type uD} [Category.{vD} D] {S : Type uS} [Category.{vS} S]
  {M : Type uM} [Category.{vM} M] (e : D ≌ S)
  (P : MorphismProperty M) [P.RespectsIso]

example {F G : D ⥤ M} (f : F ⟶ G) (d : D) :
    Arrow.mk (f.app d) ≅ Arrow.mk (f.app (e.inverse.obj (e.functor.obj d))) :=
  unitComponentArrowIso e f d

example {F G : D ⥤ M} (f : F ⟶ G) (d : D) :
    (unitComponentArrowIso e f d).hom.left = F.map (e.unit.app d) ∧
      (unitComponentArrowIso e f d).hom.right = G.map (e.unit.app d) ∧
      (unitComponentArrowIso e f d).inv.left = F.map (e.unitInv.app d) ∧
      (unitComponentArrowIso e f d).inv.right = G.map (e.unitInv.app d) :=
  unitComponentArrowIso_fields e f d

example {F G : S ⥤ M} (f : F ⟶ G) (s : S) :
    (counitComponentArrowIso e f s).hom.left = F.map (e.counit.app s) ∧
      (counitComponentArrowIso e f s).hom.right = G.map (e.counit.app s) ∧
      (counitComponentArrowIso e f s).inv.left = F.map (e.counitInv.app s) ∧
      (counitComponentArrowIso e f s).inv.right = G.map (e.counitInv.app s) :=
  counitComponentArrowIso_fields e f s

example :
    (P.functorCategory S).inverseImage (e.congrLeft (E := M)).functor =
      P.functorCategory D :=
  functorCategory_inverseImage_congrLeft e P

example :
    (P.functorCategory D).inverseImage (e.congrLeft (E := M)).inverse =
      P.functorCategory S :=
  functorCategory_inverseImage_congrLeft_inverse e P

example :
    (P.functorCategory S).llp.inverseImage (e.congrLeft (E := M)).functor =
      (P.functorCategory D).llp :=
  functorCategory_llp_inverseImage_congrLeft e P

example :
    (P.functorCategory S).rlp.inverseImage (e.congrLeft (E := M)).functor =
      (P.functorCategory D).rlp :=
  functorCategory_rlp_inverseImage_congrLeft e P

example :
    (P.functorCategory D).llp.inverseImage (e.congrLeft (E := M)).inverse =
      (P.functorCategory S).llp :=
  functorCategory_llp_inverseImage_congrLeft_inverse e P

example :
    (P.functorCategory D).rlp.inverseImage (e.congrLeft (E := M)).inverse =
      (P.functorCategory S).rlp :=
  functorCategory_rlp_inverseImage_congrLeft_inverse e P

example :
    (P.functorCategory S).rlp.llp.inverseImage (e.congrLeft (E := M)).functor =
      (P.functorCategory D).rlp.llp :=
  functorCategory_rlp_llp_inverseImage_congrLeft e P

example :
    (P.functorCategory S).llp.rlp.inverseImage (e.congrLeft (E := M)).functor =
      (P.functorCategory D).llp.rlp :=
  functorCategory_llp_rlp_inverseImage_congrLeft e P

example (Q : MorphismProperty S) [Q.RespectsIso] :
    Q.llp.inverseImage e.functor = (Q.inverseImage e.functor).llp :=
  inverseImage_llp_of_equivalence e Q

example (Q : MorphismProperty S) [Q.RespectsIso] :
    Q.rlp.inverseImage e.functor = (Q.inverseImage e.functor).rlp :=
  inverseImage_rlp_of_equivalence e Q

example {A B X Y : D ⥤ M} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty ((e.congrLeft (E := M)).functor.map i)
        ((e.congrLeft (E := M)).functor.map p) ↔ HasLiftingProperty i p :=
  Functor.hasLiftingProperty_iff_of_isEquivalence (e.congrLeft (E := M)).functor i p

section FiveBaseClasses
variable [ModelCategory M]

example :
    ((weakEquivalences M).functorCategory S).inverseImage
        (e.congrLeft (E := M)).functor = (weakEquivalences M).functorCategory D :=
  functorCategory_inverseImage_congrLeft e (weakEquivalences M)

example :
    ((fibrations M).functorCategory S).inverseImage
        (e.congrLeft (E := M)).functor = (fibrations M).functorCategory D :=
  functorCategory_inverseImage_congrLeft e (fibrations M)

example :
    ((trivialFibrations M).functorCategory S).inverseImage
        (e.congrLeft (E := M)).functor = (trivialFibrations M).functorCategory D :=
  functorCategory_inverseImage_congrLeft e (trivialFibrations M)

example :
    ((trivialFibrations M).functorCategory S).llp.inverseImage
        (e.congrLeft (E := M)).functor = ((trivialFibrations M).functorCategory D).llp :=
  functorCategory_llp_inverseImage_congrLeft e (trivialFibrations M)

example :
    ((fibrations M).functorCategory S).llp.inverseImage
        (e.congrLeft (E := M)).functor = ((fibrations M).functorCategory D).llp :=
  functorCategory_llp_inverseImage_congrLeft e (fibrations M)

example :
    ((trivialCofibrations M).functorCategory S).rlp.inverseImage
        (e.congrLeft (E := M)).functor = ((trivialCofibrations M).functorCategory D).rlp :=
  functorCategory_rlp_inverseImage_congrLeft e (trivialCofibrations M)

end FiveBaseClasses

section ActualIndices

example :
    (P.functorCategory (Discrete PEmpty)).inverseImage
        ((CategoryTheory.Equivalence.refl (C := Discrete PEmpty)).congrLeft (E := M)).functor =
      P.functorCategory (Discrete PEmpty) :=
  functorCategory_inverseImage_congrLeft (CategoryTheory.Equivalence.refl (C := Discrete PEmpty)) P

example :
    (P.functorCategory (Discrete ℕ)).llp.inverseImage
        ((CategoryTheory.Equivalence.refl (C := Discrete ℕ)).congrLeft (E := M)).functor =
      (P.functorCategory (Discrete ℕ)).llp :=
  functorCategory_llp_inverseImage_congrLeft (CategoryTheory.Equivalence.refl (C := Discrete ℕ)) P

example :
    (P.functorCategory (SingleObj (Multiplicative ℕ))).rlp.inverseImage
        ((CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ))).congrLeft (E := M)).functor =
      (P.functorCategory (SingleObj (Multiplicative ℕ))).rlp :=
  functorCategory_rlp_inverseImage_congrLeft (CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ))) P

/-- The original index uses the stock category on its raised object type. -/
local instance originalIndexRaisedCategory : Category.{vD} (ULift.{uD + 1} D) := uliftCategory D
/-- The original index uses the stock category on its independently raised Homs. -/
local instance originalIndexRaisedHomCategory :
    Category.{max (vD + 1) vD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  @ULiftHom.category (ULift.{uD + 1} D) (inferInstance : Category.{vD} (ULift.{uD + 1} D))

example :
    (P.functorCategory (ULiftHom.{vD + 1} (ULift.{uD + 1} D))).llp.inverseImage
        ((ULiftHomULiftCategory.equiv.{vD + 1, uD + 1} D).congrLeft (E := M)).functor =
      (P.functorCategory D).llp :=
  functorCategory_llp_inverseImage_congrLeft (ULiftHomULiftCategory.equiv D) P

end ActualIndices

end MathlibExtTest.MorphismPropertyIndexEquivalence
