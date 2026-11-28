/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantCanonicalAbutmentCurrentImageNaturality

/-!
# Naturality of the preceding abutment image

Let K be a first-quadrant bicomplex in an abelian category and p,q∈ℕ. Put m=p+q, ℓ=(p:ℤ)−1 and
u=m+1. If a_K:H^{-m}_K(⊥,ℓ)→H^{-m}_K(⊥,p) and b_K:H^{-m}_K(⊥,p)→H^{-m}_K(⊥,u) are the
complete-filtration relative homology maps, the preceding abutment image is image(a_K≫b_K). Its
bottom-relative comparison identifies it with F_ℓH_m(Tot K), the horizontal homology filtration
subobject at the integer cut ℓ.

A bicomplex morphism gives a commutative square between a_K≫b_K and a_L≫b_L, hence a map of
these images. The image comparison is natural under that map and the preceding filtration map.
At p=0 the cut is ℓ=-1 and both preceding subobjects are zero; the formulas include this case
without a separate choice.
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

/-- For a morphism f:K→L of first-quadrant bicomplexes in an abelian category and p,q∈ℕ, set m=p+q
and ℓ=(p:ℤ)−1. The image map induced by H_m(G_ℓ(K))→H_m(Tot K) equals the preceding horizontal
filtration map F_ℓH_m(Tot K)→F_ℓH_m(Tot L). When p=0, ℓ=-1, the complete filtered stages and
these image subobjects are zero; the same equality applies. -/
@[simp]
theorem horizontalCompleteHomologyImageMapOfBicomplex_eq_previous
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCompleteHomologyImageMapOfBicomplex f (p + q)
        (horizontalFirstPageLowerIndex p) =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q := by
  let lower : EInt := horizontalFirstPageLowerIndex p
  let upper : EInt := horizontalFirstPageUpperIndex p
  let stepK := horizontalTotalHomologyFiltrationStepMap K p q
  let stepL := horizontalTotalHomologyFiltrationStepMap L p q
  let current :=
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q
  let previous := horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q
  let totalMap := HomologicalComplex.homologyMap
    (total.map f (ComplexShape.down ℕ)) (p + q)
  have hcurrent :=
    horizontalCompleteHomologyImageMapOfBicomplex_ι f (p + q) upper
  rw [horizontalCompleteHomologyImageMapOfBicomplex_eq_current] at hcurrent
  have hstepK := MonoOver.w
    ((horizontalTotalHomologyFiltration K (p + q)).toMonoOver.map
      (homOfLE (horizontalTotalHomologyPrevIndex_le p)))
  change stepK ≫
      image.ι (horizontalCompleteHomologyToTotal K (p + q) upper) =
    image.ι (horizontalCompleteHomologyToTotal K (p + q) lower) at hstepK
  have hstepL := MonoOver.w
    ((horizontalTotalHomologyFiltration L (p + q)).toMonoOver.map
      (homOfLE (horizontalTotalHomologyPrevIndex_le p)))
  change stepL ≫
      image.ι (horizontalCompleteHomologyToTotal L (p + q) upper) =
    image.ι (horizontalCompleteHomologyToTotal L (p + q) lower) at hstepL
  change horizontalCompleteHomologyImageMapOfBicomplex f (p + q) lower =
    previous
  apply (cancel_mono
    (image.ι (horizontalCompleteHomologyToTotal L (p + q) lower))).1
  rw [horizontalCompleteHomologyImageMapOfBicomplex_ι]
  symm
  calc
    previous ≫
          image.ι (horizontalCompleteHomologyToTotal L (p + q) lower) =
        previous ≫
          (stepL ≫ image.ι
            (horizontalCompleteHomologyToTotal L (p + q) upper)) := by
      rw [hstepL]
    _ = (previous ≫ stepL) ≫
        image.ι (horizontalCompleteHomologyToTotal L (p + q) upper) := by
      simp only [Category.assoc]
    _ = (stepK ≫ current) ≫
        image.ι (horizontalCompleteHomologyToTotal L (p + q) upper) := by
      rw [horizontalTotalHomologyFiltrationStepMap_naturality]
    _ = stepK ≫
        (current ≫ image.ι
          (horizontalCompleteHomologyToTotal L (p + q) upper)) :=
      Category.assoc _ _ _
    _ = stepK ≫
        (image.ι (horizontalCompleteHomologyToTotal K (p + q) upper) ≫
          totalMap) := by
      rw [hcurrent]
    _ = (stepK ≫
          image.ι (horizontalCompleteHomologyToTotal K (p + q) upper)) ≫
        totalMap := (Category.assoc _ _ _).symm
    _ = image.ι
          (horizontalCompleteHomologyToTotal K (p + q) lower) ≫
        totalMap := by
      rw [hstepK]

/-- Let C be abelian, f:K→L a morphism of bicomplexes of shape (down ℕ,down ℕ), and p,q∈ℕ. Set
m=p+q, ℓ=(p:ℤ)−1 and u=m+1. For the complete-filtration relative homology maps
a_K:H^{-m}_K(⊥,ℓ)→H^{-m}_K(⊥,p) and b_K:H^{-m}_K(⊥,p)→H^{-m}_K(⊥,u), this is the arrow-category
morphism (a_K≫b_K)→(a_L≫b_L). Its edges are the degree -m spectral components α at ⊥→ℓ and τ at
⊥→u, and its square satisfies α≫(a_L≫b_L)=(a_K≫b_K)≫τ. -/
noncomputable def horizontalCanonicalAbutmentPreviousHomologySquareOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    Arrow.mk (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
      horizontalCanonicalAbutmentToUpperHomologyMap K p q) ⟶
      Arrow.mk (horizontalCanonicalAbutmentPreviousHomologyMap L p q ≫
        horizontalCanonicalAbutmentToUpperHomologyMap L p q) := by
  let φ := horizontalCompleteFiltrationSpectralObjectMap f
  let n : ℤ := -((p + q : ℕ) : ℤ)
  let d := twoδ₂Toδ₁
    (horizontalCanonicalAbutmentLowerMap p)
    (homOfLE ((horizontalFirstPageIndex_le p).trans
      (horizontalAbutmentIndices_le p q).2))
    (horizontalCanonicalAbutmentTotalMap p q)
    (Subsingleton.elim _ _)
  refine Arrow.homMk
    ((φ.hom n).app (mk₁ (horizontalCanonicalAbutmentLowerMap p)))
    ((φ.hom n).app (mk₁ (horizontalCanonicalAbutmentTotalMap p q))) ?_
  rw [horizontalCanonicalAbutmentPrevious_comp_toUpper K p q,
    horizontalCanonicalAbutmentPrevious_comp_toUpper L p q]
  exact ((φ.hom n).naturality d).symm

/-- For f:K→L between first-quadrant bicomplexes in an abelian category and p,q∈ℕ, put m=p+q,
ℓ=(p:ℤ)−1 and u=m+1. Let a:H^{-m}(⊥,ℓ)→H^{-m}(⊥,p) and b:H^{-m}(⊥,p)→H^{-m}(⊥,u) be the
complete-filtration relative cochain homology maps. The spectral morphism of f induces this
image morphism image(a_K≫b_K)→image(a_L≫b_L), with its ambient target map the relative homology
component in degree -m at ⊥→u. -/
noncomputable def horizontalCanonicalAbutmentPreviousImageMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    image (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
        horizontalCanonicalAbutmentToUpperHomologyMap K p q) ⟶
      image (horizontalCanonicalAbutmentPreviousHomologyMap L p q ≫
        horizontalCanonicalAbutmentToUpperHomologyMap L p q) :=
  image.map
    (horizontalCanonicalAbutmentPreviousHomologySquareOfBicomplex f p q)

/-- Let f:K→L be a first-quadrant bicomplex morphism in an abelian category and p,q∈ℕ. Set m=p+q,
ℓ=(p:ℤ)−1 and u=m+1. For a:H^{-m}(⊥,ℓ)→H^{-m}(⊥,p) and b:H^{-m}(⊥,p)→H^{-m}(⊥,u), let
J_f:image(a_K≫b_K)→image(a_L≫b_L) be the preceding image map and τ:H^{-m}_K(⊥,u)→H^{-m}_L(⊥,u)
the spectral component of f in degree -m. Then J_f≫image.ι(a_L≫b_L)=image.ι(a_K≫b_K)≫τ. -/
@[reassoc (attr := simp)]
theorem horizontalCanonicalAbutmentPreviousImageMapOfBicomplex_ι
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f p q ≫
        image.ι (horizontalCanonicalAbutmentPreviousHomologyMap L p q ≫
          horizontalCanonicalAbutmentToUpperHomologyMap L p q) =
      image.ι (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
          horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
        ((horizontalCompleteFiltrationSpectralObjectMap f).hom
          (-((p + q : ℕ) : ℤ))).app
            (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) :=
  image.map_ι
    (horizontalCanonicalAbutmentPreviousHomologySquareOfBicomplex f p q)

/-- For a morphism f:K→L of first-quadrant bicomplexes in an abelian category and p,q∈ℕ, put m=p+q,
ℓ=(p:ℤ)−1 and u=m+1. Let a:H^{-m}(⊥,ℓ)→H^{-m}(⊥,p), b:H^{-m}(⊥,p)→H^{-m}(⊥,u), and
e_K:image(a_K≫b_K)≅F_ℓH_m(Tot K) be the bottom-relative image comparison. With J_f the preceding
relative image map and F_ℓH_m(Tot f) the preceding filtration map,
J_f≫e_L.hom=e_K.hom≫F_ℓH_m(Tot f). The integer cut ℓ=-1 at p=0 is included. -/
theorem horizontalCanonicalAbutmentPreviousImageIso_naturality_of_bicomplex
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f p q ≫
        (horizontalCanonicalAbutmentPreviousImageIso L p q).hom =
      (horizontalCanonicalAbutmentPreviousImageIso K p q).hom ≫
        horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q := by
  let sourceSquare :=
    horizontalCanonicalAbutmentPreviousHomologySquareOfBicomplex f p q
  let targetSquare :=
    horizontalCompleteHomologyToTotalSquareOfBicomplex f (p + q)
      (horizontalFirstPageLowerIndex p)
  let eK := horizontalCanonicalAbutmentPreviousArrowIso K p q
  let eL := horizontalCanonicalAbutmentPreviousArrowIso L p q
  have hArrow : sourceSquare ≫ eL.hom = eK.hom ≫ targetSquare := by
    apply Arrow.hom_ext
    · change
        ((horizontalCompleteFiltrationSpectralObjectMap f).hom
            (-((p + q : ℕ) : ℤ))).app
              (mk₁ (horizontalCanonicalAbutmentLowerMap p)) ≫
            (horizontalBottomRelativeHomologyStageIso L
              (horizontalFirstPageLowerIndex p) (p + q)).hom =
          (horizontalBottomRelativeHomologyStageIso K
              (horizontalFirstPageLowerIndex p) (p + q)).hom ≫
            HomologicalComplex.homologyMap
              (horizontalCompleteFilteredTotalComplexMapOfBicomplex f
                (horizontalFirstPageLowerIndex p)) (p + q)
      have h :=
        horizontalBottomRelativeHomologyStageIso_naturality_of_bicomplex
          f (horizontalFirstPageLowerIndex p) (p + q)
      have hbottom :
          horizontalBottomToStageMap (horizontalFirstPageLowerIndex p) =
            horizontalCanonicalAbutmentLowerMap p :=
        Subsingleton.elim _ _
      rw [hbottom] at h
      simpa only [sourceSquare, targetSquare, eK, eL,
        horizontalCanonicalAbutmentPreviousHomologySquareOfBicomplex,
        horizontalCompleteHomologyToTotalSquareOfBicomplex,
        horizontalCanonicalAbutmentPreviousArrowIso,
        Arrow.comp_left, Arrow.homMk_left, Arrow.isoMk_hom_left] using h
    · change
        ((horizontalCompleteFiltrationSpectralObjectMap f).hom
            (-((p + q : ℕ) : ℤ))).app
              (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) ≫
            (horizontalBottomRelativeHomologyToTotalIso L p q).hom =
          (horizontalBottomRelativeHomologyToTotalIso K p q).hom ≫
            HomologicalComplex.homologyMap
              (total.map f (ComplexShape.down ℕ)) (p + q)
      simpa only [sourceSquare, targetSquare, eK, eL,
        horizontalCanonicalAbutmentPreviousHomologySquareOfBicomplex,
        horizontalCompleteHomologyToTotalSquareOfBicomplex,
        horizontalCanonicalAbutmentPreviousArrowIso,
        Arrow.comp_right, Arrow.homMk_right, Arrow.isoMk_hom_right] using
        horizontalBottomRelativeHomologyToTotalIso_naturality_of_bicomplex
          f p q
  rw [← horizontalCompleteHomologyImageMapOfBicomplex_eq_previous f p q]
  change (Limits.im (C := C)).map sourceSquare ≫
      ((Limits.im (C := C)).mapIso eL).hom =
    ((Limits.im (C := C)).mapIso eK).hom ≫
      (Limits.im (C := C)).map targetSquare
  simpa only [Functor.map_comp, Functor.mapIso_hom] using
    congrArg (fun k => (Limits.im (C := C)).map k) hArrow

end HomologicalComplex₂

end
