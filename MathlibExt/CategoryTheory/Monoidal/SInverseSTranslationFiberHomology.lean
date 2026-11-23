/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedFiberHomology
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationFiberPushforward

/-!
# Homology of fibers of the additive translation projection

For a small additive category, the strict fibers of the additive `S⁻¹S`
translation projection have the homology of `Core C`.  Under these
isomorphisms, the coefficient-system map of a base translation arrow is the
homology map induced by left translation by its selected stabilizer.

This is the exact conjugation formula needed before localizing the fiber
homology coefficient system in the group-completion spectral sequence.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe u

namespace CategoryTheory
namespace SInverseS

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Category homology of `Core C` is canonically the category homology of
the strict translation fiber over `B`. -/
noncomputable def coreTranslationFiberHomologyIso
    (B : Translation C) (R : AddCommGrpCat.{u}) (n : ℕ) :
    (nerve (Core C)).homology R n ≅
      (nerve (TranslationFiber (⟨B.of⟩ : Core C))).homology R n :=
  categoryHomologyIsoOfEquivalence AddCommGrpCat.{u}
    (coreTranslationFiberEquivalence (⟨B.of⟩ : Core C)) R n

/-- Under the core/fiber homology isomorphisms, pushforward along a base
translation arrow is homology of left translation by its selected
stabilizer. -/
theorem coreTranslationFiberHomologyIso_hom_naturality
    {B T : Translation C} (f : B ⟶ T)
    (R : AddCommGrpCat.{u}) (n : ℕ) :
    (coreTranslationFiberHomologyIso C B R n).hom ≫
        (Functor.IsCofibered.fiberHomologyFunctor
          (p := translationProjection (C := C))
          AddCommGrpCat.{u} R n).map f =
      (categoryHomologyFunctor AddCommGrpCat.{u} R n).map
          (coreLeftTranslationFunctor
            (Translation.representative f).stabilizer).toCatHom ≫
        (coreTranslationFiberHomologyIso C T R n).hom := by
  rcases B with ⟨B⟩
  rcases T with ⟨T⟩
  let H : Cat.{u, u} ⥤ AddCommGrpCat.{u} :=
    categoryHomologyFunctor AddCommGrpCat.{u} R n
  change H.map
        (coreToTranslationFiber (⟨B⟩ : Core C)).toCatHom ≫
      H.map (Functor.IsCofibered.fiberPushforwardFunctor
        (p := translationProjection (C := C)) f).toCatHom =
    H.map (coreLeftTranslationFunctor
        (Translation.representative f).stabilizer).toCatHom ≫
      H.map (coreToTranslationFiber (⟨T⟩ : Core C)).toCatHom
  rw [← H.map_comp, ← H.map_comp]
  exact categoryHomologyMap_eq_of_natIso AddCommGrpCat.{u}
    (chosenExplicitCoreFiberPushforwardIso f) R n

end SInverseS
end CategoryTheory

end
