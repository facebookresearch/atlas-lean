/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantBottomRelativeTotalNaturality
public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedFunctor
public import MathlibExt.Algebra.Homology.HomologyMapSquare

/-!
# Naturality of the current abutment image

For a first-quadrant bicomplex K in an abelian category, let G_i be its complete horizontal
filtered total complex at i∈ℤ∪{⊥,⊤}. Write t_{K,n,i}:H_n(G_i)→H_n(Tot K). A bicomplex morphism
f:K→L gives a commutative square between t_K and t_L, hence a map between their images that
commutes with the inclusions into total homology.

For p,q∈ℕ put m=p+q and u=m+1. Let H^a_K(s,t) denote the relative cochain homology of the
complete filtration between s≤t. The current abutment arrow is b_K:H^{-m}_K(⊥,p)→H^{-m}_K(⊥,u).
The bottom-relative comparisons identify image b_K with the pth horizontal filtration subobject
of H_m(Tot K). These image comparisons commute with every bicomplex morphism, with arbitrary
object and morphism universes.
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

/-- Let C be an abelian category, f:K→L a morphism of bicomplexes of shape (down ℕ,down ℕ), n∈ℕ and
i∈ℤ∪{⊥,⊤}. Write G_i(K) for the complete horizontal filtered total stage and
t_K:H_n(G_i(K))→H_n(Tot K) for its inclusion map on homology. This is the arrow-category
morphism from t_K to t_L with left edge H_n(G_i(f)) and right edge H_n(Tot f); its square
satisfies H_n(G_i(f))≫t_L=t_K≫H_n(Tot f). -/
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

/-- For f:K→L between first-quadrant bicomplexes in an abelian category, n∈ℕ and a complete cut
i∈ℤ∪{⊥,⊤}, let t_K:H_n(G_i(K))→H_n(Tot K) and t_L be the stage-to-total maps. The square with
edges H_n(G_i(f)) and H_n(Tot f) induces this morphism image t_K→image t_L of subobjects of
total homology. -/
noncomputable def horizontalCompleteHomologyImageMapOfBicomplex
    (f : K ⟶ L) (n : ℕ) (i : EInt) :
    image (horizontalCompleteHomologyToTotal K n i) ⟶
      image (horizontalCompleteHomologyToTotal L n i) :=
  image.map (horizontalCompleteHomologyToTotalSquareOfBicomplex f n i)

/-- Let f:K→L be a first-quadrant bicomplex morphism in an abelian category, n∈ℕ and i∈ℤ∪{⊥,⊤}. For
t_K:H_n(G_i(K))→H_n(Tot K), let I_f:image t_K→image t_L be the induced image map and ι_K,ι_L
their image inclusions. Then I_f≫ι_L=ι_K≫H_n(Tot f). Thus the image map agrees with the
total-complex homology map after inclusion. -/
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

/-- For a morphism f:K→L of first-quadrant bicomplexes in an abelian category and p,q∈ℕ, put m=p+q.
The complete-stage image map in homology degree m at the finite cut i=p equals the current
filtration map obtained from the finite horizontal filtration through its complete-to-finite
comparison. Both are morphisms between the pth filtration subobjects of H_m(Tot K) and H_m(Tot
L). -/
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

/-- Let C be abelian, f:K→L a morphism of bicomplexes of shape (down ℕ,down ℕ), and p,q∈ℕ. Put m=p+q
and u=m+1, and let H^a_K(s,t) be relative cochain homology of the complete horizontal
filtration. For b_K:H^{-m}_K(⊥,p)→H^{-m}_K(⊥,u), this arrow-category morphism b_K→b_L has edges
s_f:H^{-m}_K(⊥,p)→H^{-m}_L(⊥,p) and v_f:H^{-m}_K(⊥,u)→H^{-m}_L(⊥,u) induced by the spectral
morphism of f. Its equation is s_f≫b_L=b_K≫v_f. -/
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

/-- For a morphism f:K→L of first-quadrant bicomplexes in an abelian category and p,q∈ℕ, put m=p+q
and u=m+1. Let b_K:H^{-m}_K(⊥,p)→H^{-m}_K(⊥,u) be the current relative-homology map of the
complete horizontal filtration. The natural square of these arrows induces this map image
b_K→image b_L. Its codomain edge is the relative spectral map in degree -m at ⊥→u. -/
noncomputable def horizontalCanonicalAbutmentCurrentImageMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    image (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ⟶
      image (horizontalCanonicalAbutmentToUpperHomologyMap L p q) :=
  image.map
    (horizontalCanonicalAbutmentCurrentHomologySquareOfBicomplex f p q)

/-- Let f:K→L be a first-quadrant bicomplex morphism in an abelian category and p,q∈ℕ. Set m=p+q and
u=m+1, and write b_K:H^{-m}_K(⊥,p)→H^{-m}_K(⊥,u) for the current relative-homology arrow. If
I_f:image b_K→image b_L is its induced image map and v_f:H^{-m}_K(⊥,u)→H^{-m}_L(⊥,u) is the
degree -m spectral component at ⊥→u, then I_f≫image.ι(b_L)=image.ι(b_K)≫v_f. -/
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

/-- For f:K→L between first-quadrant bicomplexes in an abelian category and p,q∈ℕ, put m=p+q and
u=m+1. Let b_K:H^{-m}_K(⊥,p)→H^{-m}_K(⊥,u), I_f:image b_K→image b_L, and F_pH_m(Tot K) be the
pth horizontal homology filtration subobject. The bottom-relative isomorphisms induce e_K:image
b_K≅F_pH_m(Tot K). If F_pH_m(Tot f) is the current filtration map, then
I_f≫e_L.hom=e_K.hom≫F_pH_m(Tot f). -/
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
