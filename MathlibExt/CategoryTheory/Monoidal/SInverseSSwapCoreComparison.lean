/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationCoherence
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationFiber
public import MathlibExt.CategoryTheory.NerveCrossUniverse

/-!
# The initial core fiber and coordinate-swap homology comparison

The negative core inclusion factors through the genuine strict translation
fiber over the initial zero object. Coordinate swap carries it to the
chosen positive core inclusion and conjugates the actual residual actions.
The induced homology isomorphism retains both of these original maps.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.SInverseS

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The actual initial-fiber inclusion, with its core parameterization. -/
def negativeCoreInclusion : Core C ⥤ Pair C :=
  coreToTranslationFiber (⟨0⟩ : Core C) ⋙ Functor.Fiber.fiberInclusion

/-- It is the inclusion of the actual zero fiber through its constructed
core equivalence. The wrapped zero is initial by `Translation.zeroIsInitial`. -/
theorem negativeCoreInclusion_eq_fiber :
    negativeCoreInclusion (C := C) =
      (coreTranslationFiberEquivalence (⟨0⟩ : Core C)).functor ⋙
        Functor.Fiber.fiberInclusion := rfl

/-- The actual initial fiber retains the literal negative pair. -/
@[simp]
theorem negativeCoreInclusion_obj (X : Core C) :
    (negativeCoreInclusion (C := C)).obj X = ⟨(0 : C), X.of⟩ := rfl

/-- Swapping the genuine initial core fiber gives the chosen core inclusion. -/
theorem negativeCoreInclusion_comp_swapFunctor :
    negativeCoreInclusion (C := C) ⋙ swapFunctor = coreInclusion := by
  refine Functor.ext (F := negativeCoreInclusion (C := C) ⋙ swapFunctor)
    (G := coreInclusion) (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- The canonical core square under coordinate swap. -/
def negativeCoreSwapIso :
    negativeCoreInclusion (C := C) ⋙ swapFunctor ≅ coreInclusion :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl)

/-- The core comparison preserves the literal positive pair. -/
@[simp]
theorem negativeCoreSwapIso_hom_app (X : Core C) :
    (negativeCoreSwapIso (C := C)).hom.app X = 𝟙 _ := rfl

/-- The chosen coordinate-swap functor is strictly involutive. -/
theorem swapFunctor_comp_swapFunctor :
    swapFunctor (C := C) ⋙ swapFunctor = 𝟭 (Pair C) := by
  refine Functor.ext (F := swapFunctor (C := C) ⋙ swapFunctor)
    (G := 𝟭 (Pair C)) (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact Hom.swap_swap f

/-- The actual nerve isomorphism induced by coordinate swap. -/
def swapNerveIso : nerve (Pair C) ≅ nerve (Pair C) where
  hom := nerveMap (swapFunctor (C := C))
  inv := nerveMap (swapFunctor (C := C))
  hom_inv_id := by
    rw [nerveMap_comp, swapFunctor_comp_swapFunctor, nerveMap_id]
  inv_hom_id := by
    rw [nerveMap_comp, swapFunctor_comp_swapFunctor, nerveMap_id]

/-- The canonical homology isomorphism of the original pair nerve, with
arbitrary abelian-group coefficients in the nerve universe. -/
def swapHomologyIso (R : AddCommGrpCat.{max u v}) (n : ℕ) :
    (nerve (Pair C)).homology R n ≅ (nerve (Pair C)).homology R n :=
  (SSet.homologyFunctor R n).mapIso (swapNerveIso (C := C))

/-- The forward homology comparison is the original coordinate-swap map. -/
@[simp]
theorem swapHomologyIso_hom (R : AddCommGrpCat.{max u v}) (n : ℕ) :
    (swapHomologyIso (C := C) R n).hom =
      SSet.homologyMap (nerveMap (swapFunctor (C := C))) R n := rfl

/-- Its inverse is the same original involutive map. -/
@[simp]
theorem swapHomologyIso_inv (R : AddCommGrpCat.{max u v}) (n : ℕ) :
    (swapHomologyIso (C := C) R n).inv =
      SSet.homologyMap (nerveMap (swapFunctor (C := C))) R n := rfl

/-- The original negative core homology map becomes the chosen positive
core homology map under the actual coordinate-swap comparison. -/
theorem negativeCoreHomology_comp_swap (R : AddCommGrpCat.{max u v}) (n : ℕ) :
    SSet.homologyMap (nerveMapCommonValue.{u, 0, u, v} (negativeCoreInclusion (C := C))) R n ≫
        (swapHomologyIso (C := C) R n).hom =
      SSet.homologyMap (nerveMapCommonValue.{u, 0, u, v} (coreInclusion (C := C))) R n := by
  rw [swapHomologyIso_hom, ← SSet.homologyMap_comp, nerveMapCommonValue_nerveMap_comp.{u, 0, u, v},
    negativeCoreInclusion_comp_swapFunctor]

/-- The same canonical homology comparison intertwines the actual second
and first residual translations for every translating object. -/
theorem swapHomologyIso_intertwines (R : AddCommGrpCat.{max u v}) (n : ℕ) (B : C) :
    SSet.homologyMap (nerveMap (translateSecondFunctor B)) R n ≫
        (swapHomologyIso (C := C) R n).hom =
      (swapHomologyIso (C := C) R n).hom ≫
        SSet.homologyMap (nerveMap (translateFirstFunctor B)) R n := by
  rw [swapHomologyIso_hom, ← SSet.homologyMap_comp, ← SSet.homologyMap_comp,
    nerveMap_comp, nerveMap_comp, translateSecondFunctor_comp_swapFunctor]

end CategoryTheory.SInverseS

end
