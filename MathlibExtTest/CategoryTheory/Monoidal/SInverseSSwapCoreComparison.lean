/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Monoidal.SInverseSSwapCoreComparison

/-!
# Actual core and translation comparison consumers

These clients use the genuine zero fiber, literal pair coordinates, the
public translation natural isomorphism and the original homology maps.
-/

open CategoryTheory Limits ZeroObject

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace CategoryTheory.SInverseS

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

example (X : Core C) :
    ((negativeCoreInclusion (C := C) ⋙ swapFunctor).obj X).fst = X.of ∧
      ((negativeCoreInclusion (C := C) ⋙ swapFunctor).obj X).snd = (0 : C) := by
  constructor <;> rfl

example (X : Core C) :
    ((coreToTranslationFiber (⟨0⟩ : Core C)).obj X).1 =
      (negativeCoreInclusion (C := C)).obj X := rfl

example (B : C) {X Y : Pair C} (f : X ⟶ Y) :
    (swapFunctor (C := C)).map ((translateSecondFunctor B).map f) =
      (translateFirstFunctor B).map ((swapFunctor (C := C)).map f) := by
  have h := (translateSecondSwapIso B).hom.naturality f
  simpa only [Functor.comp_map, translateSecondSwapIso_hom_app,
    Category.id_comp, Category.comp_id] using h

example (R : AddCommGrpCat.{max u v}) (n : ℕ)
    (x : ((nerve (Core C)).homology R n : AddCommGrpCat.{max u v})) :
    (swapHomologyIso (C := C) R n).hom
        (SSet.homologyMap (nerveMapCommonValue.{u, 0, u, v} (negativeCoreInclusion (C := C))) R n x) =
      SSet.homologyMap (nerveMapCommonValue.{u, 0, u, v} (coreInclusion (C := C))) R n x :=
  ConcreteCategory.congr_hom (negativeCoreHomology_comp_swap (C := C) R n) x

example (R : AddCommGrpCat.{max u v}) (n : ℕ) (B : C)
    (x : ((nerve (Pair C)).homology R n : AddCommGrpCat.{max u v})) :
    SSet.homologyMap (nerveMap (translateFirstFunctor B)) R n
        ((swapHomologyIso (C := C) R n).hom x) =
      (swapHomologyIso (C := C) R n).hom
        (SSet.homologyMap (nerveMap (translateSecondFunctor B)) R n x) :=
  (ConcreteCategory.congr_hom (swapHomologyIso_intertwines (C := C) R n B) x).symm

example (R : AddCommGrpCat.{max u v}) (n : ℕ)
    (x : ((nerve (Pair C)).homology R n : AddCommGrpCat.{max u v})) :
    (swapHomologyIso (C := C) R n).inv ((swapHomologyIso (C := C) R n).hom x) = x :=
  ConcreteCategory.congr_hom (swapHomologyIso (C := C) R n).hom_inv_id x

example (X : Core C) :
    ((negativeCoreInclusion (C := C) ⋙ swapFunctor).obj X).difference =
      -((negativeCoreInclusion (C := C)).obj X).difference :=
  Pair.difference_swapObj _


/- The legacy hom-level substitution cannot accept the actual initial-core functor
with independent object and hom universes. -/
/-- error: Application type mismatch -/
#guard_msgs (error, substring := true) in
#check nerveMapHomDown.{u, v, max u v} (negativeCoreInclusion (C := C))

/-- Its canonical comparison uses the literal original core and pair nerve objects. -/
example : nerve (Core C) ⟶ nerve (Pair C) :=
  nerveMapCommonValue.{u, 0, u, v} (negativeCoreInclusion (C := C))

end CategoryTheory.SInverseS

end
