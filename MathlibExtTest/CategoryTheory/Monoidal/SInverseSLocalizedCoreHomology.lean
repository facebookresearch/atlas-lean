/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedCoreHomology

/-!
# Ordinary use of the canonical localized core comparison

The public characteristics recover the strict original comparison and both
translated core-inclusion formulas on every native core fraction.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.SInverseS.LocalizedCoreHomologyTests

variable {C : Type} [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The ordinary public interface gives the strict original comparison,
its isomorphism and the two core-fraction orientations in every degree. -/
theorem canonicalCoreFractionClient (R : AddCommGrpCat.{0}) (q : ℕ) :
    let T := coreTranslationDenominators C
    let U := forget₂ (ModuleCat.{0} (Localization T)) AddCommGrpCat.{0}
    let θ : U.obj (localizedCoreTranslationHomologyModuleCat C R q) ⟶
        (nerve (Pair C)).homology R q :=
      U.map ((secondTranslationBKLocalizedModuleSecondPageZeroIso (C := C) R q).inv ≫
          secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q) ≫
        (secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R q).hom ≫
        (translationBKAbutmentHomologyIso C R q).hom
    let σ := swapHomologyIso (C := C) R q
    let θplus := θ ≫ σ.hom
    let ε := coreTranslationHomologyModuleAddCommGrpIso C R q
    let jMinus := SSet.homologyMap (nerveMap (negativeCoreInclusion (C := C))) R q
    let jPlus := SSet.homologyMap (nerveMap (coreInclusion (C := C))) R q
    IsIso θ ∧ IsIso θplus ∧
      (∀ x : coreTranslationHomologyModule C R q,
        θ (LocalizedModule.mk x (1 : T)) = jMinus (ε.hom x) ∧
          θplus (LocalizedModule.mk x (1 : T)) = jPlus (ε.hom x)) ∧
      (∀ (d : T) (x : coreTranslationHomologyModule C R q),
        let m := Classical.choose (MonoidHom.mem_mrange.mp d.property)
        let J := pairTranslationHomologyIsoOfObject C R q m.toAdd.out
        θ (LocalizedModule.mk x d) = J.hom (jMinus (ε.hom x)) ∧
          θplus (LocalizedModule.mk x d) = J.inv (jPlus (ε.hom x))) ∧
      (∀ (s : Skeleton C) (x : coreTranslationHomologyModule C R q),
        θ (LocalizedModule.mk x (coreTranslationDenominator C s)) =
            (pairTranslationHomologyIso C R q s).hom (jMinus (ε.hom x)) ∧
          θplus (LocalizedModule.mk x (coreTranslationDenominator C s)) =
            (pairTranslationHomologyIso C R q s).inv (jPlus (ε.hom x))) := by
  classical
  dsimp only
  let T := coreTranslationDenominators C
  let U := forget₂ (ModuleCat.{0} (Localization T)) AddCommGrpCat.{0}
  let θ : U.obj (localizedCoreTranslationHomologyModuleCat C R q) ⟶
      (nerve (Pair C)).homology R q :=
    U.map ((secondTranslationBKLocalizedModuleSecondPageZeroIso (C := C) R q).inv ≫
        secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q) ≫
      (secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R q).hom ≫
      (translationBKAbutmentHomologyIso C R q).hom
  let σ := swapHomologyIso (C := C) R q
  let E := secondTranslationBKLocalizedCoreHomologyIso (C := C) R q
  let Eplus := E ≪≫ σ
  have negative := secondTranslationBKLocalizedCoreHomologyIso_characteristic (C := C) R q
  have positive := secondTranslationBKLocalizedCoreHomologyIso_swap_characteristic (C := C) R q
  have hn : E.hom = θ := negative.1
  have hp : Eplus.hom = θ ≫ σ.hom :=
    positive.1.trans (congrArg (fun f => f ≫ σ.hom) hn)
  have : IsIso θ := by
    rw [← hn]
    infer_instance
  have : IsIso (θ ≫ σ.hom) := by infer_instance
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro x
    constructor
    · exact (congrArg
        (fun f => f (LocalizedModule.mk x (1 : coreTranslationDenominators C))) hn.symm).trans
        (negative.2.1 x)
    · exact (congrArg
        (fun f => f (LocalizedModule.mk x (1 : coreTranslationDenominators C))) hp.symm).trans
        (positive.2.1 x)
  · intro d x
    constructor
    · exact (congrArg (fun f => f (LocalizedModule.mk x d)) hn.symm).trans
        (negative.2.2.1 d x)
    · exact (congrArg (fun f => f (LocalizedModule.mk x d)) hp.symm).trans
        (positive.2.2.1 d x)
  · intro s x
    constructor
    · exact (congrArg
        (fun f => f (LocalizedModule.mk x (coreTranslationDenominator C s))) hn.symm).trans
        (negative.2.2.2 s x)
    · exact (congrArg
        (fun f => f (LocalizedModule.mk x (coreTranslationDenominator C s))) hp.symm).trans
        (positive.2.2.2 s x)

end CategoryTheory.SInverseS.LocalizedCoreHomologyTests
