/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.PartialTotalStablePage
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Tactic.NormNum

/-!
# A nonzero integer stable-page quotient coordinate

Use the first-quadrant bicomplex with an integer module at every lattice point and zero
horizontal and vertical differentials. The corner summand supplies a total homology class
whose coproduct detector has value three.

The degree-zero image filtration is exhaustive and its preceding integer cut has zero image.
The actual filtration-to-stable-page map therefore gives a page-two class whose graded-quotient
coordinate has value three. All coordinate isomorphisms used below come from the zero
homology data or the proved filtration and stable-page APIs; no output isomorphism or flatness
premise is assumed.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open CategoryTheory.Abelian.SpectralObject

namespace MathlibExtTest.PartialTotalStablePage

private abbrev E := ModuleCat.{0} ℤ
private abbrev N : E := ModuleCat.of ℤ ℤ
private abbrev row : ChainComplex E ℕ :=
  ChainComplex.of (fun _ => N) (fun _ => 0) (by intro n; simp)

private abbrev B : HomologicalComplex₂ E (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  ChainComplex.of (fun _ => row) (fun _ => 0) (by intro n; simp)

private abbrev T := B.total (ComplexShape.down ℕ)

private theorem row_d_zero (i j : ℕ) : row.d i j = 0 := by
  simp [row, ChainComplex.of.d]

private theorem outer_d_zero (i j : ℕ) : B.d i j = 0 := by
  simp [B, ChainComplex.of.d]

private theorem total_d_zero (i j : ℕ) : T.d i j = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    B.ι_D₁ (ComplexShape.down ℕ) i j a b hab,
    B.ι_D₂ (ComplexShape.down ℕ) i j a b hab]
  simp only [HomologicalComplex₂.d₁, HomologicalComplex₂.d₂, outer_d_zero,
    HomologicalComplex.zero_f, row_d_zero, zero_comp, smul_zero, add_zero, comp_zero]

private def totalDetector : T.X 0 ⟶ N :=
  B.totalDesc (c₁₂ := ComplexShape.down ℕ) (i₁₂ := 0) (fun _ _ _ => 𝟙 N)

private def corner : T.X 0 := (B.ιTotal (ComplexShape.down ℕ) 0 0 0 (by simp)).hom (3 : ℤ)

private theorem corner_value : totalDetector.hom corner = 3 := by
  have h := B.ι_totalDesc (c₁₂ := ComplexShape.down ℕ) (i₁₂ := 0)
    (fun _ _ _ => 𝟙 N) 0 0 (by simp)
  exact ConcreteCategory.congr_hom h (3 : ℤ)

private def homologyCoordinate : T.homology 0 ≅ T.X 0 :=
  (ShortComplex.HomologyData.ofZeros (T.sc 0)
    (total_d_zero _ _) (total_d_zero _ _)).left.homologyIso

private def totalClass : T.homology 0 := homologyCoordinate.inv.hom corner

private abbrev I := (B.partialTotalHomologyFiltration 0).obj (((0 : ℤ) : EInt))
private abbrev imageInclusion : I ⟶ T.homology 0 :=
  (B.partialTotalHomologyFiltration 0).ι.app (((0 : ℤ) : EInt))

private instance : IsIso imageInclusion := B.partialTotalHomologyFiltration_exhaustive_at_degree 0

private def imageClass : I := (asIso imageInclusion).inv.hom totalClass
private abbrev G := B.partialTotalHomologyGradedPiece 0 0

private def gradedDetector : G ⟶ N :=
  (B.partialTotalHomologyGradedZeroIso 0).inv ≫ imageInclusion ≫
    homologyCoordinate.hom ≫ totalDetector

private abbrev Page :=
  ((B.partialTotalSpectralObject.spectralSequence coreE₁IncreasingHomologicalNat).page (2 : ℤ)).X
    ((0 : ℕ), (0 : ℕ))

private def pageClass : Page :=
  (B.partialTotalStablePageIso 0 0).inv.hom
    ((B.partialTotalHomologyFiltrationToStable 0 0).hom imageClass)

private theorem gradedProjection_detector :
    B.partialTotalHomologyGradedπ 0 0 ≫ gradedDetector =
      imageInclusion ≫ homologyCoordinate.hom ≫ totalDetector := by
  change (B.partialTotalHomologyGradedZeroIso 0).hom ≫
    (B.partialTotalHomologyGradedZeroIso 0).inv ≫
      imageInclusion ≫ homologyCoordinate.hom ≫ totalDetector = _
  simp only [Iso.hom_inv_id_assoc]

private theorem page_detector_map :
    (B.partialTotalHomologyFiltrationToStable 0 0 ≫ (B.partialTotalStablePageIso 0 0).inv) ≫
        (B.partialTotalStablePageGradedIso 0 0).hom ≫ gradedDetector =
      imageInclusion ≫ homologyCoordinate.hom ≫ totalDetector := by
  calc
    _ = B.partialTotalHomologyGradedπ 0 0 ≫ gradedDetector := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ gradedDetector)
        (B.partialTotalHomologyFiltrationToStablePage_comp_gradingIso_hom 0 0)
    _ = _ := gradedProjection_detector

private theorem page_value :
    gradedDetector.hom ((B.partialTotalStablePageGradedIso 0 0).hom.hom pageClass) = 3 := by
  have h := ConcreteCategory.congr_hom page_detector_map imageClass
  change gradedDetector.hom ((B.partialTotalStablePageGradedIso 0 0).hom.hom pageClass) =
    totalDetector.hom (homologyCoordinate.hom.hom (imageInclusion.hom imageClass)) at h
  have hv : totalDetector.hom
      (homologyCoordinate.hom.hom (imageInclusion.hom imageClass)) = 3 := by
    change totalDetector.hom (homologyCoordinate.hom.hom
      ((asIso imageInclusion).hom.hom ((asIso imageInclusion).inv.hom totalClass))) = 3
    rw [ModuleCat.hom_inv_apply, totalClass, ModuleCat.hom_inv_apply, corner_value]
  exact h.trans hv

example : totalDetector.hom corner = 3 := corner_value

example : gradedDetector.hom ((B.partialTotalStablePageGradedIso 0 0).hom.hom pageClass) = 3 :=
  page_value

example : pageClass ≠ 0 := by
  intro hzero
  have h := congrArg (fun x => gradedDetector.hom
    ((B.partialTotalStablePageGradedIso 0 0).hom.hom x)) hzero
  rw [page_value, map_zero, map_zero] at h
  norm_num at h

example : IsZero ((B.partialTotalHomologyFiltration 0).obj (((-1 : ℤ) : EInt))) :=
  B.isZero_partialTotalHomologyFiltration_obj_of_neg 0 (-1) (by norm_num)

example : IsZero (B.partialTotalHomologyGradedPiece 0 1) :=
  B.isZero_partialTotalHomologyGradedPiece_of_degree_lt 0 1 (by decide)

example : IsIso (B.partialTotalHomologyGradedπ 0 0) := B.isIso_partialTotalHomologyGradedπ_zero 0

end MathlibExtTest.PartialTotalStablePage
