/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantBottomRelativeTotalNaturality
public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedFunctor
public import MathlibExt.Algebra.Homology.HomologyMapSquare

/-!
# Naturality of the canonical-abutment current image

A bicomplex map induces a canonical square between the homology-to-total
maps at every complete filtration stage.  At the first-page upper index,
the resulting image map is the existing current filtration map.  The
canonical-abutment current-image comparison intertwines this map with the
corresponding relative-homology image map.

This file does not treat the preceding image or the final associated-graded
comparison.
-/

@[expose] public section

open CategoryTheory Limits ComposableArrows

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The commutative square between complete-stage homology-to-total maps
induced by a bicomplex morphism. -/
noncomputable def horizontalCompleteHomologyToTotalSquareOfBicomplex
    (f : K ⟶ L) (n : ℕ) (i : EInt) :
    Arrow.mk (horizontalCompleteHomologyToTotal K n i) ⟶
      Arrow.mk (horizontalCompleteHomologyToTotal L n i) :=
  Arrow.homMk
    (HomologicalComplex.homologyMap
      (horizontalCompleteFilteredTotalComplexMapOfBicomplex f i) n)
    (HomologicalComplex.homologyMap
      (total.map f (ComplexShape.down ℕ)) n)
    (by
      change HomologicalComplex.homologyMap
            (horizontalCompleteFilteredTotalComplexMapOfBicomplex f i) n ≫
          HomologicalComplex.homologyMap
            (horizontalCompleteFilteredTotalToTotal L i) n =
        HomologicalComplex.homologyMap
            (horizontalCompleteFilteredTotalToTotal K i) n ≫
          HomologicalComplex.homologyMap
            (total.map f (ComplexShape.down ℕ)) n
      exact HomologicalComplex.homologyMap_square
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex_toTotal f i) n)

/-- The image map induced by the complete-stage homology-to-total square. -/
noncomputable def horizontalCompleteHomologyImageMapOfBicomplex
    (f : K ⟶ L) (n : ℕ) (i : EInt) :
    image (horizontalCompleteHomologyToTotal K n i) ⟶
      image (horizontalCompleteHomologyToTotal L n i) :=
  image.map (horizontalCompleteHomologyToTotalSquareOfBicomplex f n i)

/-- The complete-stage image map commutes with the canonical inclusions into
total homology. -/
@[reassoc (attr := simp)]
theorem horizontalCompleteHomologyImageMapOfBicomplex_ι
    (f : K ⟶ L) (n : ℕ) (i : EInt) :
    horizontalCompleteHomologyImageMapOfBicomplex f n i ≫
        image.ι (horizontalCompleteHomologyToTotal L n i) =
      image.ι (horizontalCompleteHomologyToTotal K n i) ≫
        HomologicalComplex.homologyMap
          (total.map f (ComplexShape.down ℕ)) n :=
  by
    let sq := horizontalCompleteHomologyToTotalSquareOfBicomplex f n i
    change image.map sq ≫ image.ι (Arrow.mk
        (horizontalCompleteHomologyToTotal L n i)).hom =
      image.ι (Arrow.mk
        (horizontalCompleteHomologyToTotal K n i)).hom ≫ sq.right
    exact image.map_ι sq

/-- At the first-page upper index, the generic complete-stage image map is
the reviewed current total-homology filtration map. -/
@[simp]
theorem horizontalCompleteHomologyImageMapOfBicomplex_eq_current
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCompleteHomologyImageMapOfBicomplex f (p + q)
        (horizontalFirstPageUpperIndex p) =
      horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
        f p q := by
  let eK :=
    (horizontalCompleteFiniteHomologyFiltrationDiagramIso K (p + q)).app p
  let eL :=
    (horizontalCompleteFiniteHomologyFiltrationDiagramIso L (p + q)).app p
  let EL := horizontalCompleteFiniteHomologyFiltrationDiagramIso L (p + q)
  let m := horizontalFiniteHomologyImageMapOfBicomplex f (p + q) p
  have hK :=
    horizontalCompleteFiniteHomologyFiltrationDiagramIso_hom_ι
      K (p + q) p
  have hL :=
    horizontalCompleteFiniteHomologyFiltrationDiagramIso_hom_ι
      L (p + q) p
  have hLinv :
      EL.inv.app p ≫
          (horizontalTotalHomologyFiltration L (p + q)).ι.app
            (((p : ℤ) : EInt)) =
        (horizontalFiniteTotalHomologyFiltration L (p + q)).ι.app p := by
    rw [← hL]
    dsimp only [EL]
    rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  have hm :
      m ≫ (horizontalFiniteTotalHomologyFiltration L (p + q)).ι.app p =
        (horizontalFiniteTotalHomologyFiltration K (p + q)).ι.app p ≫
          HomologicalComplex.homologyMap
            (total.map f (ComplexShape.down ℕ)) (p + q) := by
    simpa only [m, horizontalFiniteTotalHomologyFiltration_ι_app] using
      horizontalFiniteHomologyImageMapOfBicomplex_ι f (p + q) p
  change horizontalCompleteHomologyImageMapOfBicomplex f (p + q)
      (horizontalFirstPageUpperIndex p) = eK.hom ≫ m ≫ eL.inv
  apply (cancel_mono (image.ι
    (horizontalCompleteHomologyToTotal L (p + q)
      (horizontalFirstPageUpperIndex p)))).1
  rw [horizontalCompleteHomologyImageMapOfBicomplex_ι]
  symm
  change (eK.hom ≫ m ≫ eL.inv) ≫
      (horizontalTotalHomologyFiltration L (p + q)).ι.app
        (((p : ℤ) : EInt)) =
    (horizontalTotalHomologyFiltration K (p + q)).ι.app
        (((p : ℤ) : EInt)) ≫
      HomologicalComplex.homologyMap
        (total.map f (ComplexShape.down ℕ)) (p + q)
  calc
    (eK.hom ≫ m ≫ eL.inv) ≫
          (horizontalTotalHomologyFiltration L (p + q)).ι.app
            (((p : ℤ) : EInt)) =
        eK.hom ≫ m ≫
          (eL.inv ≫
            (horizontalTotalHomologyFiltration L (p + q)).ι.app
              (((p : ℤ) : EInt))) := by
      simp only [Category.assoc]
    _ = eK.hom ≫ m ≫
        (horizontalFiniteTotalHomologyFiltration L (p + q)).ι.app p := by
      simpa only [eL, EL, Iso.app_inv] using
        eK.hom ≫= (m ≫= hLinv)
    _ = eK.hom ≫
        (m ≫ (horizontalFiniteTotalHomologyFiltration L
          (p + q)).ι.app p) := by
      rfl
    _ = eK.hom ≫
        ((horizontalFiniteTotalHomologyFiltration K (p + q)).ι.app p ≫
          HomologicalComplex.homologyMap
            (total.map f (ComplexShape.down ℕ)) (p + q)) := by
      rw [hm]
    _ = (eK.hom ≫
          (horizontalFiniteTotalHomologyFiltration K (p + q)).ι.app p) ≫
        HomologicalComplex.homologyMap
          (total.map f (ComplexShape.down ℕ)) (p + q) := by
      simp only [Category.assoc]
    _ = (horizontalTotalHomologyFiltration K (p + q)).ι.app
          (((p : ℤ) : EInt)) ≫
        HomologicalComplex.homologyMap
          (total.map f (ComplexShape.down ℕ)) (p + q) := by
      simpa only [eK, Iso.app_hom] using
        hK =≫ HomologicalComplex.homologyMap
          (total.map f (ComplexShape.down ℕ)) (p + q)

/-- The relative-homology square for the current canonical-abutment image
induced by a bicomplex morphism. -/
noncomputable def horizontalCanonicalAbutmentCurrentHomologySquareOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    Arrow.mk (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ⟶
      Arrow.mk (horizontalCanonicalAbutmentToUpperHomologyMap L p q) := by
  let φ := horizontalCompleteFiltrationSpectralObjectMap f
  let n : ℤ := -((p + q : ℕ) : ℤ)
  let d := twoδ₂Toδ₁
    (horizontalCanonicalAbutmentLowerCompositeMap p)
    (horizontalCanonicalAbutmentUpperMap p q)
    (horizontalCanonicalAbutmentTotalMap p q)
    (horizontalCanonicalAbutmentLowerComposite_comp_upper p q)
  exact Arrow.homMk
    ((φ.hom n).app
      (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p)))
    ((φ.hom n).app
      (mk₁ (horizontalCanonicalAbutmentTotalMap p q)))
    ((φ.hom n).naturality d).symm

/-- The map between current canonical-abutment images induced by a
bicomplex morphism. -/
noncomputable def horizontalCanonicalAbutmentCurrentImageMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    image (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ⟶
      image (horizontalCanonicalAbutmentToUpperHomologyMap L p q) :=
  image.map
    (horizontalCanonicalAbutmentCurrentHomologySquareOfBicomplex f p q)

/-- The current canonical-abutment image map commutes with the canonical
inclusions. -/
@[reassoc (attr := simp)]
theorem horizontalCanonicalAbutmentCurrentImageMapOfBicomplex_ι
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentCurrentImageMapOfBicomplex f p q ≫
        image.ι (horizontalCanonicalAbutmentToUpperHomologyMap L p q) =
      image.ι (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
        ((horizontalCompleteFiltrationSpectralObjectMap f).hom
          (-((p + q : ℕ) : ℤ))).app
            (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) :=
  image.map_ι
    (horizontalCanonicalAbutmentCurrentHomologySquareOfBicomplex f p q)

/-- The comparison from the current canonical-abutment image to the current
total-homology filtration stage is natural in the bicomplex. -/
theorem horizontalCanonicalAbutmentCurrentImageIso_naturality_of_bicomplex
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentCurrentImageMapOfBicomplex f p q ≫
        (horizontalCanonicalAbutmentCurrentImageIso L p q).hom =
      (horizontalCanonicalAbutmentCurrentImageIso K p q).hom ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
          f p q := by
  let sourceSquare :=
    horizontalCanonicalAbutmentCurrentHomologySquareOfBicomplex f p q
  let targetSquare :=
    horizontalCompleteHomologyToTotalSquareOfBicomplex f (p + q)
      (horizontalFirstPageUpperIndex p)
  let eK := horizontalCanonicalAbutmentCurrentArrowIso K p q
  let eL := horizontalCanonicalAbutmentCurrentArrowIso L p q
  have hArrow : sourceSquare ≫ eL.hom = eK.hom ≫ targetSquare := by
    apply Arrow.hom_ext
    · change
        ((horizontalCompleteFiltrationSpectralObjectMap f).hom
            (-((p + q : ℕ) : ℤ))).app
              (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p)) ≫
            (horizontalBottomRelativeHomologyStageIso L
              (horizontalFirstPageUpperIndex p) (p + q)).hom =
          (horizontalBottomRelativeHomologyStageIso K
              (horizontalFirstPageUpperIndex p) (p + q)).hom ≫
            HomologicalComplex.homologyMap
              (horizontalCompleteFilteredTotalComplexMapOfBicomplex f
                (horizontalFirstPageUpperIndex p)) (p + q)
      have h :=
        horizontalBottomRelativeHomologyStageIso_naturality_of_bicomplex
          f (horizontalFirstPageUpperIndex p) (p + q)
      have hbottom :
          horizontalBottomToStageMap (horizontalFirstPageUpperIndex p) =
            horizontalCanonicalAbutmentLowerCompositeMap p :=
        Subsingleton.elim _ _
      rw [hbottom] at h
      simpa only [sourceSquare, targetSquare, eK, eL,
        horizontalCanonicalAbutmentCurrentHomologySquareOfBicomplex,
        horizontalCompleteHomologyToTotalSquareOfBicomplex,
        horizontalCanonicalAbutmentCurrentArrowIso,
        Arrow.comp_left, Arrow.homMk_left, Arrow.isoMk_hom_left] using h
    · change
        ((horizontalCompleteFiltrationSpectralObjectMap f).hom
            (-((p + q : ℕ) : ℤ))).app
              (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) ≫
            (horizontalBottomRelativeHomologyToTotalIso L p q).hom =
          (horizontalBottomRelativeHomologyToTotalIso K p q).hom ≫
            HomologicalComplex.homologyMap
              (total.map f (ComplexShape.down ℕ)) (p + q)
      exact
        (by
          simpa only [sourceSquare, targetSquare, eK, eL,
            horizontalCanonicalAbutmentCurrentHomologySquareOfBicomplex,
            horizontalCompleteHomologyToTotalSquareOfBicomplex,
            horizontalCanonicalAbutmentCurrentArrowIso,
            Arrow.comp_right, Arrow.homMk_right, Arrow.isoMk_hom_right] using
            horizontalBottomRelativeHomologyToTotalIso_naturality_of_bicomplex
              f p q)
  rw [← horizontalCompleteHomologyImageMapOfBicomplex_eq_current f p q]
  change (Limits.im (C := C)).map sourceSquare ≫
      ((Limits.im (C := C)).mapIso eL).hom =
    ((Limits.im (C := C)).mapIso eK).hom ≫
      (Limits.im (C := C)).map targetSquare
  simpa only [Functor.map_comp, Functor.mapIso_hom] using
    congrArg (fun k => (Limits.im (C := C)).map k) hArrow

end HomologicalComplex₂

end
