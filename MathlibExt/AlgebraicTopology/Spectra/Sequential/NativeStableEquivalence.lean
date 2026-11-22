/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.Omega
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.ModelCategory.CanonicalLevelModel
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.ModelCategory.CanonicalLevelFibrancy
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Yoneda

/-!
# Omega tests in the actual sequential level homotopy category

The testing maps are precomposition by the canonical localization of the
already constructed native projective level model. The targets are precisely
the genuine native Omega spectra. Every native sequential spectrum is fibrant
in this selected level model, so this is also testing against level-fibrant
Omega spectra.

The formal closure assertions and endpoint rigidity are the model-independent
part of MMSS Definition 8.3 and Lemma 8.11. No stable model, derived-mapping
comparison, localization recognition packet or new model instance is supplied.
-/

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe u v

open CategoryTheory CategoryTheory.MorphismProperty HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum

/-- The homotopy category of the actual named native projective level model. -/
abbrev LevelHomotopyCategory : Type (v + 1) :=
  letI : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
    PointedCGWH.Spectra.Sequential.levelModel
  HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}

/-- The original canonical localization functor for that same level model. -/
abbrev toLevelHomotopyCategory :
    PointedCGWH.SequentialSpectrum.{u, v} ⥤ LevelHomotopyCategory.{u, v} :=
  letI : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
    PointedCGWH.Spectra.Sequential.levelModel
  toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}

/-- MMSS level-homotopy tests restricted to the actual native Omega targets. -/
def omegaTestEquivalences :
    MorphismProperty PointedCGWH.SequentialSpectrum.{u, v} :=
  fun _X Y f => ∀ E : PointedCGWH.SequentialSpectrum.{u, v}, E.IsOmega →
    Function.Bijective
      (fun g : (toLevelHomotopyCategory.{u, v}).obj Y ⟶
          (toLevelHomotopyCategory.{u, v}).obj E =>
        (toLevelHomotopyCategory.{u, v}).map f ≫ g)

/-- The test retains the original arrow and both actual localized Hom sets. -/
theorem omegaTestEquivalences_iff
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    omegaTestEquivalences f ↔
      ∀ E : PointedCGWH.SequentialSpectrum.{u, v}, E.IsOmega →
        Function.Bijective
          (fun g : (toLevelHomotopyCategory.{u, v}).obj Y ⟶
              (toLevelHomotopyCategory.{u, v}).obj E =>
            (toLevelHomotopyCategory.{u, v}).map f ≫ g) :=
  Iff.rfl

/-- The same original tests may record the selected level fibrancy explicitly. -/
theorem omegaTestEquivalences_iff_levelFibrantTests
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    letI : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
      PointedCGWH.Spectra.Sequential.levelModel
    omegaTestEquivalences f ↔
      ∀ E : PointedCGWH.SequentialSpectrum.{u, v},
        (IsFibrant E ∧ E.IsOmega) →
          Function.Bijective
            (fun g : (toLevelHomotopyCategory.{u, v}).obj Y ⟶
                (toLevelHomotopyCategory.{u, v}).obj E =>
              (toLevelHomotopyCategory.{u, v}).map f ≫ g) := by
  let _ : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
    PointedCGWH.Spectra.Sequential.levelModel
  constructor
  · intro h E hE
    exact h E hE.2
  · intro h E hE
    exact h E ⟨PointedCGWH.Spectra.Sequential.level_allObjectsFibrant E, hE⟩

/-- Each targetwise test is an opposite inverse image of actual isomorphisms. -/
theorem omegaTestEquivalences_eq_iInf_isomorphisms :
    omegaTestEquivalences.{u, v} =
      ⨅ E : {E : PointedCGWH.SequentialSpectrum.{u, v} // E.IsOmega},
        ((MorphismProperty.isomorphisms (Type (v + 1))).inverseImage
          ((toLevelHomotopyCategory.{u, v}).op ⋙
            yoneda.obj ((toLevelHomotopyCategory.{u, v}).obj E.1))).unop := by
  ext X Y f
  rw [MorphismProperty.iInf_iff]
  change (∀ E : PointedCGWH.SequentialSpectrum.{u, v}, E.IsOmega →
      Function.Bijective
        (fun g : (toLevelHomotopyCategory.{u, v}).obj Y ⟶
            (toLevelHomotopyCategory.{u, v}).obj E =>
          (toLevelHomotopyCategory.{u, v}).map f ≫ g)) ↔
    ∀ E : {E : PointedCGWH.SequentialSpectrum.{u, v} // E.IsOmega},
      IsIso (((toLevelHomotopyCategory.{u, v}).op ⋙
        yoneda.obj ((toLevelHomotopyCategory.{u, v}).obj E.1)).map f.op)
  constructor
  · intro h E
    exact (CategoryTheory.isIso_iff_bijective _).2 (h E.1 E.2)
  · intro h E hE
    exact (CategoryTheory.isIso_iff_bijective _).1 (h ⟨E, hE⟩)

/-- Actual identity arrows satisfy every Omega test. -/
instance omegaTestEquivalences.containsIdentities :
    omegaTestEquivalences.{u, v}.ContainsIdentities where
  id_mem X := by
    rw [omegaTestEquivalences_eq_iInf_isomorphisms, MorphismProperty.iInf_iff]
    intro E
    exact (((MorphismProperty.isomorphisms (Type (v + 1))).inverseImage
      ((toLevelHomotopyCategory.{u, v}).op ⋙
        yoneda.obj ((toLevelHomotopyCategory.{u, v}).obj E.1))).unop).id_mem X

/-- All three two-out-of-three directions hold for these same original tests. -/
instance omegaTestEquivalences.hasTwoOutOfThreeProperty :
    omegaTestEquivalences.{u, v}.HasTwoOutOfThreeProperty := by
  rw [omegaTestEquivalences_eq_iInf_isomorphisms]
  refine { toIsStableUnderComposition := inferInstance
           of_postcomp := ?_
           of_precomp := ?_ }
  · intro X Y Z f g hg hfg
    rw [MorphismProperty.iInf_iff] at hg hfg ⊢
    intro E
    exact (((MorphismProperty.isomorphisms (Type (v + 1))).inverseImage
      ((toLevelHomotopyCategory.{u, v}).op ⋙
        yoneda.obj ((toLevelHomotopyCategory.{u, v}).obj E.1))).unop).of_postcomp
      f g (hg E) (hfg E)
  · intro X Y Z f g hf hfg
    rw [MorphismProperty.iInf_iff] at hf hfg ⊢
    intro E
    exact (((MorphismProperty.isomorphisms (Type (v + 1))).inverseImage
      ((toLevelHomotopyCategory.{u, v}).op ⋙
        yoneda.obj ((toLevelHomotopyCategory.{u, v}).obj E.1))).unop).of_precomp
      f g (hf E) (hfg E)

/-- Arbitrary whole-arrow retracts preserve every original Omega test. -/
instance omegaTestEquivalences.isStableUnderRetracts :
    omegaTestEquivalences.{u, v}.IsStableUnderRetracts where
  of_retract h hg := by
    rw [omegaTestEquivalences_eq_iInf_isomorphisms] at hg ⊢
    rw [MorphismProperty.iInf_iff] at hg ⊢
    intro E
    exact MorphismProperty.of_retract h (hg E)

/-- A weak equivalence in the actual level model satisfies every Omega test. -/
theorem levelWeakEquivalences_le_omegaTestEquivalences :
    (PointedCGWH.Spectra.Sequential.levelModel.{u, v}).categoryWithWeakEquivalences.weakEquivalences ≤
      omegaTestEquivalences.{u, v} := by
  intro X Y f hf E _
  have hInv : IsIso ((toLevelHomotopyCategory.{u, v}).map f) := by
    let _ : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
      PointedCGWH.Spectra.Sequential.levelModel
    exact (weakEquivalence_iff_isIso_toHomotopyCategory_map f).1 hf
  exact (isIso_iff_coyoneda_map_bijective _).1 hInv
    ((toLevelHomotopyCategory.{u, v}).obj E)

/-- Between genuine Omega spectra, the actual tests detect the level weak class. -/
theorem omegaTestEquivalences_iff_levelWeakEquivalences_of_isOmega
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hX : X.IsOmega) (hY : Y.IsOmega) :
    omegaTestEquivalences f ↔
      (PointedCGWH.Spectra.Sequential.levelModel.{u, v}).categoryWithWeakEquivalences.weakEquivalences f := by
  constructor
  · intro hf
    obtain ⟨g, hfg⟩ := (hf X hX).2 (𝟙 ((toLevelHomotopyCategory.{u, v}).obj X))
    have hgf : g ≫ (toLevelHomotopyCategory.{u, v}).map f =
        𝟙 ((toLevelHomotopyCategory.{u, v}).obj Y) := by
      apply (hf Y hY).1
      simp only [← Category.assoc, hfg, Category.id_comp, Category.comp_id]
    have hInv : IsIso ((toLevelHomotopyCategory.{u, v}).map f) := ⟨g, hfg, hgf⟩
    let _ : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
      PointedCGWH.Spectra.Sequential.levelModel
    exact (weakEquivalence_iff_isIso_toHomotopyCategory_map f).2 hInv
  · exact levelWeakEquivalences_le_omegaTestEquivalences f

/-- The same rigidity assertion retains each actual native level component. -/
theorem omegaTestEquivalences_iff_levelwiseWeakEquivalences_of_isOmega
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hX : X.IsOmega) (hY : Y.IsOmega) :
    omegaTestEquivalences f ↔ ∀ n : ℕ,
      weakEquivalences PointedCGWH.{u, v} (levelMap f n) :=
  (omegaTestEquivalences_iff_levelWeakEquivalences_of_isOmega f hX hY).trans
    (PointedCGWH.Spectra.Sequential.levelModel_weakEquivalences_iff f)

end PointedCGWH.SequentialSpectrum
