/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantBottomRelativeNaturality
public import MathlibExt.Algebra.Homology.FirstQuadrantConvergence

/-!
# Bicomplex naturality of the bottom-relative-to-total comparison

The bottom-relative homology comparison at the finite upper abutment stage
is natural with respect to bicomplex maps.  The proof combines naturality at
that complete-filtration stage with compatibility of stage maps and the map
of total complexes.

This file does not pass to image quotients or stable associated-graded terms.
-/

@[expose] public section

open CategoryTheory Limits ComposableArrows

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The bottom-relative-to-total comparison is natural under bicomplex
morphisms. -/
theorem horizontalBottomRelativeHomologyToTotalIso_naturality_of_bicomplex
    (f : K ⟶ L) (p q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom
        (-((p + q : ℕ) : ℤ))).app
          (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) ≫
      (horizontalBottomRelativeHomologyToTotalIso L p q).hom =
    (horizontalBottomRelativeHomologyToTotalIso K p q).hom ≫
      HomologicalComplex.homologyMap
        (total.map f (ComplexShape.down ℕ)) (p + q) := by
  let n : ℕ := p + q
  let I : EInt := horizontalAbutmentUpperIndex p q
  let m : horizontalCompleteFilteredTotalComplex K I ⟶
      horizontalCompleteFilteredTotalComplex L I :=
    horizontalCompleteFilteredTotalComplexMapOfBicomplex f I
  let uK : horizontalCompleteFilteredTotalComplex K I ⟶ K.total (ComplexShape.down ℕ) :=
    horizontalCompleteFilteredTotalToTotal K I
  let uL : horizontalCompleteFilteredTotalComplex L I ⟶ L.total (ComplexShape.down ℕ) :=
    horizontalCompleteFilteredTotalToTotal L I
  let t : K.total (ComplexShape.down ℕ) ⟶ L.total (ComplexShape.down ℕ) :=
    total.map f (ComplexShape.down ℕ)
  have hbottom : horizontalBottomToStageMap I = horizontalCanonicalAbutmentTotalMap p q :=
    Subsingleton.elim _ _
  have hstage : ((horizontalCompleteFiltrationSpectralObjectMap f).hom (-(n : ℤ))).app
        (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) ≫
      (horizontalBottomRelativeHomologyStageIso L I n).hom =
      (horizontalBottomRelativeHomologyStageIso K I n).hom ≫
        HomologicalComplex.homologyMap m n := by
    have hs := horizontalBottomRelativeHomologyStageIso_naturality_of_bicomplex f I n
    rw [hbottom] at hs
    exact hs
  have hchain : m ≫ uL = uK ≫ t :=
    horizontalCompleteFilteredTotalComplexMapOfBicomplex_toTotal f I
  have htotal : HomologicalComplex.homologyMap m n ≫
        HomologicalComplex.homologyMap uL n =
      HomologicalComplex.homologyMap uK n ≫ HomologicalComplex.homologyMap t n := by
    simpa only [HomologicalComplex.homologyMap_comp] using
      congrArg (fun g : horizontalCompleteFilteredTotalComplex K I ⟶
          L.total (ComplexShape.down ℕ) => HomologicalComplex.homologyMap g n) hchain
  have huK : (horizontalAbutmentUpperHomologyToTotalIso K p q).hom =
      HomologicalComplex.homologyMap uK n := by
    change horizontalCompleteHomologyToTotal K n I = HomologicalComplex.homologyMap uK n
    exact horizontalCompleteHomologyToTotal_eq K n I
  have huL : (horizontalAbutmentUpperHomologyToTotalIso L p q).hom =
      HomologicalComplex.homologyMap uL n := by
    change horizontalCompleteHomologyToTotal L n I = HomologicalComplex.homologyMap uL n
    exact horizontalCompleteHomologyToTotal_eq L n I
  simp only [horizontalBottomRelativeHomologyToTotalIso, Iso.trans_hom]
  rw [huK, huL]
  change ((horizontalCompleteFiltrationSpectralObjectMap f).hom (-(n : ℤ))).app
      (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) ≫
      (horizontalBottomRelativeHomologyStageIso L I n).hom ≫
        HomologicalComplex.homologyMap uL n =
    ((horizontalBottomRelativeHomologyStageIso K I n).hom ≫
      HomologicalComplex.homologyMap uK n) ≫ HomologicalComplex.homologyMap t n
  calc
    _ = (horizontalBottomRelativeHomologyStageIso K I n).hom ≫
        HomologicalComplex.homologyMap m n ≫ HomologicalComplex.homologyMap uL n := by
      simpa only [Category.assoc] using hstage =≫ HomologicalComplex.homologyMap uL n
    _ = _ := by
      simpa only [Category.assoc] using
        (horizontalBottomRelativeHomologyStageIso K I n).hom ≫= htotal

end HomologicalComplex₂

end
