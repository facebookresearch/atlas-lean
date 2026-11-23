/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.SpectralObject.ZeroColumnEdge
public import MathlibExt.CategoryTheory.Monoidal.SInverseSActualLocalizedSecondPageConsequences
public import MathlibExt.Algebra.Homology.FirstQuadrantSpectralSequenceSupport
public import MathlibExt.Algebra.Homology.FirstQuadrantAbutmentImage

/-!
# The actual localized native zero-column edge

The original native edge of the localized BK module spectral object maps to
localized literal signed-total homology. Its negative support is derived in
all integer degrees from the zero endpoint complexes. Its sharp upper support
uses the actual component isomorphism and the monic cone/cokernel comparison.
Faithful scalar forgetting reflects zero to the integral module model, and
localization preserves it forward. Actual localized concentration then makes
the defined edge an isomorphism.

The stage-zero characteristic retains the original canonical representative,
stage comparison and signed-total inclusion. The core-generator and fraction
formulas remain separate comparisons.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CategoryTheory.ComposableArrows HomologicalComplex₂

universe u

namespace CategoryTheory.SInverseS

variable {C : Type u} [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{u})

local notation "A" => coreTranslationRing C
local notation "T" => coreTranslationDenominators C
local notation "L" => ModuleCat.localizedModuleFunctor T
local notation "Y" => secondTranslationBKModuleSpectralObject (C := C) R
local notation "LY" => secondTranslationBKLocalizedModuleSpectralObject (C := C) R
local notation "PB" => secondTranslationBKLocalizedModuleSpectralSequence (C := C) R

private theorem actualLocalizedRelativeIsZero
    (n : ℤ) {i j : EInt} (h : i ≤ j)
    (hz : IsZero ((((horizontalCompleteFiltrationSpectralObject (SSet.bkAlternatingBicomplex
      AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))).H n).obj
      (mk₁ (homOfLE h)))) :
    IsZero (((LY).H n).obj (mk₁ (homOfLE h))) := by
  let U := forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}
  have hU : IsZero (U.obj (((Y).H n).obj (mk₁ (homOfLE h)))) := by
    change IsZero (((SpectralObject.forgetMonoidModule (Y)).H n).obj
      (mk₁ (homOfLE h)))
    rw [secondTranslationBKModuleSpectralObject_forget]
    exact hz
  have hY : IsZero (((Y).H n).obj (mk₁ (homOfLE h))) := by
    rw [IsZero.iff_id_eq_zero] at hU ⊢
    apply U.map_injective
    simpa only [Functor.map_id, Functor.map_zero] using hU
  change IsZero ((L).obj (((Y).H n).obj (mk₁ (homOfLE h))))
  exact (L).map_isZero hY

private theorem actualLocalizedLowerSupport (n a : ℤ) (ha : a < 0) :
    IsZero (((LY).H n).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))) := by
  apply actualLocalizedRelativeIsZero (C := C) R n
    (bot_le : (⊥ : EInt) ≤ (a : EInt))
  exact horizontalCompleteFiltrationSpectralObject_H_isZero_of_obj_isZero
    (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram
    (translationProjection (C := C))))
    (bot_le : (⊥ : EInt) ≤ (a : EInt))
    (horizontalCompleteFiltrationCochainDiagram_obj_isZero_bot (SSet.bkAlternatingBicomplex
      AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))))
    (horizontalCompleteFiltrationCochainDiagram_obj_isZero_of_neg (SSet.bkAlternatingBicomplex
      AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) a ha) n

private theorem actualLocalizedUpperSupport
    (d : ℕ) (a : ℤ) (hda : (d : ℤ) ≤ a) :
    IsZero (((LY).H (-(d : ℤ))).obj
      (mk₁ (homOfLE (le_top : (a : EInt) ≤ (⊤ : EInt))))) := by
  have ha : 0 ≤ a := by omega
  have haNat : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha
  have hd : d ≤ a.toNat := by omega
  let h : (a : EInt) ≤ (⊤ : EInt) := le_top
  let : IsIso ((horizontalCompleteFilteredTotalToTotal (SSet.bkAlternatingBicomplex
    AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) (a :
    EInt)).f d) :=
    horizontalCompleteFilteredTotalToTotal_f_isIso_of_nonneg (SSet.bkAlternatingBicomplex
      AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) a ha d hd
  let : IsIso ((horizontalCompleteFilteredTotalToTotal (SSet.bkAlternatingBicomplex
    AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) ⊤).f d)
    := by
    rw [horizontalCompleteFilteredTotalToTotal_top, HomologicalComplex.id_f]
    let Z : AddCommGrpCat.{u} := (horizontalCompleteFilteredTotalComplex
      (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram
      (translationProjection (C := C)))) ⊤).X d
    change IsIso (𝟙 Z)
    exact IsIso.id Z
  let : IsIso ((horizontalCompleteFilteredTotalMap (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R
    (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) h).f d) :=
    horizontalCompleteFilteredTotalMap_f_isIso_of_toTotal (SSet.bkAlternatingBicomplex
      AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) h d
  let : IsIso (((horizontalCompleteFiltrationCochainDiagram (SSet.bkAlternatingBicomplex
    AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C))))).map
      (homOfLE h)).f (-(d : ℤ))) :=
    horizontalCompleteFiltrationCochainDiagram_map_f_isIso (SSet.bkAlternatingBicomplex
      AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) h d
  exact actualLocalizedRelativeIsZero (C := C) R (-(d : ℤ)) h
    (horizontalCompleteFiltrationSpectralObject_H_isZero_of_epi_f (SSet.bkAlternatingBicomplex
      AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram (translationProjection (C := C)))) h (-(d :
      ℤ)))

/-- The original localized native zero-column edge, followed by the canonical
comparison with localized literal signed-total homology. -/
noncomputable def secondTranslationBKLocalizedModuleZeroColumnEdge (q : ℕ) :
    (((PB).page (2 : ℤ) (by omega)).X (0, q)) ⟶
      (L).obj (secondTranslationBKTotalHomologyModule (C := C) R q) :=
  (LY).nativeZeroColumnEdge
      (by exact actualLocalizedLowerSupport (C := C) R) q ≫
    (secondTranslationBKLocalizedAbutmentModuleIso (C := C) R q).hom

/-- The actual localized edge is an isomorphism in every natural degree. -/
instance secondTranslationBKLocalizedModuleZeroColumnEdge_isIso (q : ℕ) :
    IsIso (secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q) := by
  let e : (((PB).page (2 : ℤ) (by omega)).X (0, q)) ⟶
      (LY).stableIntervalAbutment (-(q : ℤ)) :=
    (LY).nativeZeroColumnEdge (actualLocalizedLowerSupport (C := C) R) q
  let α : (LY).stableIntervalAbutment (-(q : ℤ)) ⟶
      (L).obj (secondTranslationBKTotalHomologyModule (C := C) R q) :=
    (secondTranslationBKLocalizedAbutmentModuleIso (C := C) R q).hom
  have he : IsIso e :=
    (LY).isIso_nativeZeroColumnEdge
      (actualLocalizedLowerSupport (C := C) R)
      (actualLocalizedUpperSupport (C := C) R)
      (fun p t hp =>
        isZero_secondTranslationBKLocalizedModuleSecondPage (C := C) R p t hp) q
  have hα : IsIso α :=
    (secondTranslationBKLocalizedAbutmentModuleIso (C := C) R q).isIso_hom
  change IsIso (e ≫ α)
  exact IsIso.comp_isIso' he hα

/-- The canonical stage-zero representative recovers the localization of the
original stage-zero inclusion into signed-total homology. -/
theorem secondTranslationBKLocalizedModuleZeroColumnEdge_representation (q : ℕ) :
    (LY).nativeZeroColumnStageZeroRepresentative
        (show ∀ (n a : ℤ), a < 0 →
          IsZero (((LY).H n).obj
            (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))) from by
          intro n a ha
          let U := forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}
          have hE : IsZero ((((horizontalCompleteFiltrationSpectralObject
            (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram
            (translationProjection (C := C)))))).H n).obj
              (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))) :=
            horizontalCompleteFiltrationSpectralObject_H_isZero_of_obj_isZero
              (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram
              (translationProjection (C := C))))
              (bot_le : (⊥ : EInt) ≤ (a : EInt))
              (horizontalCompleteFiltrationCochainDiagram_obj_isZero_bot
                (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram
                (translationProjection (C := C)))))
              (horizontalCompleteFiltrationCochainDiagram_obj_isZero_of_neg
                (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R (SSet.rightCommaNerveDiagram
                (translationProjection (C := C)))) a ha) n
          have hU : IsZero (U.obj (((Y).H n).obj
              (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt)))))) := by
            change IsZero (((SpectralObject.forgetMonoidModule (Y)).H n).obj
              (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt)))))
            rw [secondTranslationBKModuleSpectralObject_forget]
            exact hE
          have hY : IsZero (((Y).H n).obj
              (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))) := by
            rw [IsZero.iff_id_eq_zero] at hU ⊢
            apply U.map_injective
            simpa only [Functor.map_id, Functor.map_zero] using hU
          change IsZero ((L).obj (((Y).H n).obj
            (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))))
          exact (L).map_isZero hY)
        q ≫
      secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q =
    (secondTranslationBKLocalizedStageModuleIso (C := C) R q
        ((0 : ℤ) : EInt)).hom ≫
      (L).map (secondTranslationBKStageToTotalModuleMap (C := C) R q
        ((0 : ℤ) : EInt)) := by
  let ρ : (LY).stableIntervalStep (-(q : ℤ)) ((0 : ℤ) : EInt) ⟶
      (((PB).page (2 : ℤ) (by omega)).X (0, q)) :=
    (LY).nativeZeroColumnStageZeroRepresentative
      (actualLocalizedLowerSupport (C := C) R) q
  let e : (((PB).page (2 : ℤ) (by omega)).X (0, q)) ⟶
      (LY).stableIntervalAbutment (-(q : ℤ)) :=
    (LY).nativeZeroColumnEdge (actualLocalizedLowerSupport (C := C) R) q
  let α : (LY).stableIntervalAbutment (-(q : ℤ)) ⟶
      (L).obj (secondTranslationBKTotalHomologyModule (C := C) R q) :=
    (secondTranslationBKLocalizedAbutmentModuleIso (C := C) R q).hom
  have hρe : ρ ≫ e =
      (LY).stableIntervalStepToAbutment (-(q : ℤ)) ((0 : ℤ) : EInt) :=
    (LY).nativeZeroColumnEdge_representation
      (actualLocalizedLowerSupport (C := C) R) q
  have hstep :
      (LY).stableIntervalStepToAbutment (-(q : ℤ)) ((0 : ℤ) : EInt) =
        ((LY).H (-(q : ℤ))).map
          (secondTranslationBKStageIntervalMap
            (show ((0 : ℤ) : EInt) ≤ ⊤ from le_top)) := by
    dsimp only [SpectralObject.stableIntervalStepToAbutment]
    congr 1
  change ρ ≫ (e ≫ α) =
    (secondTranslationBKLocalizedStageModuleIso (C := C) R q
        ((0 : ℤ) : EInt)).hom ≫
      (L).map (secondTranslationBKStageToTotalModuleMap (C := C) R q
        ((0 : ℤ) : EInt))
  have htoTotal :
      ((LY).H (-(q : ℤ))).map
          (secondTranslationBKStageIntervalMap
            (show ((0 : ℤ) : EInt) ≤ ⊤ from le_top)) ≫ α =
        (secondTranslationBKLocalizedStageModuleIso (C := C) R q
          ((0 : ℤ) : EInt)).hom ≫
        (L).map (secondTranslationBKStageToTotalModuleMap (C := C) R q
          ((0 : ℤ) : EInt)) :=
    (secondTranslationBKLocalizedStageModuleIso_comp_toTotal
      (C := C) R q ((0 : ℤ) : EInt)).symm
  exact (Category.assoc ρ e α).symm.trans
    ((congrArg (fun f => f ≫ α) hρe).trans
      ((congrArg (fun f => f ≫ α) hstep).trans htoTotal))

end CategoryTheory.SInverseS

end
