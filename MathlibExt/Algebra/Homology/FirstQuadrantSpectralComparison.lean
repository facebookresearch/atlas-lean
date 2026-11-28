/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantSecondPageMap
public import
  MathlibExt.Algebra.Homology.FirstQuadrantStablePageGradedNaturality
public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyFiltrationNaturality

/-!
# Comparison theorems for first-quadrant total complexes

Let C be an abelian category and f : K → L a morphism of bicomplexes of shape (down ℕ,down ℕ).
If f induces an isomorphism on Gr_pH_{p+q}(Tot) for every p,q ∈ ℕ, then Tot(f) is a
quasi-isomorphism. The finite image filtration of H_n(Tot) is exhaustive by stage n, and its
consecutive stages give short exact sequences used in the comparison.

The same conclusion follows if every stable-page component of f is invertible. At bidegree
(p,q), the chosen stable page is r₀=max(p+1,q+2), and its term is naturally isomorphic to
Gr_pH_{p+q}(Tot).
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), and p,q ∈ ℕ.
In degree n=p+q, let c(f) : F_pH_n(Tot(K)) → F_pH_n(Tot(L)) be the current complete
image-stage map, and ι_p^K,ι_p^L the image inclusions. Then c(f) ≫ ι_p^L = ι_p^K ≫
H_n(Tot(f)). The stage index is the finite integer p in EInt, and the equality holds at p=0 as
well. -/
@[reassoc]
/- This commutation is used by name: simp unfolding of the current-stage map can rewrite its
left-hand side before the equation matches. -/
theorem horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_ι
    (f : K ⟶ L) (p q : ℕ) :
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q ≫
        (horizontalTotalHomologyFiltration L (p + q)).ι.app
          (((p : ℤ) : EInt)) =
      (horizontalTotalHomologyFiltration K (p + q)).ι.app
          (((p : ℤ) : EInt)) ≫
        HomologicalComplex.homologyMap
          (total.map f (ComplexShape.down ℕ)) (p + q) := by
  have hιK := horizontalCompleteFiniteHomologyFiltrationDiagramIso_hom_ι
    K (p + q) p
  have hιL := horizontalCompleteFiniteHomologyFiltrationDiagramIso_hom_ι
    L (p + q) p
  have hfin := horizontalFiniteHomologyImageMapOfBicomplex_ι f (p + q) p
  simp only [horizontalFiniteTotalHomologyFiltration_ι_app] at hιK hιL
  have hinvL :
      (horizontalCompleteFiniteHomologyFiltrationDiagramIso L
          (p + q)).inv.app p ≫
        (horizontalTotalHomologyFiltration L (p + q)).ι.app
          (((p : ℤ) : EInt)) =
      image.ι (HomologicalComplex.homologyMap
        (horizontalFilteredTotalComplexToTotal L p) (p + q)) := by
    rw [← hιL, ← Category.assoc, CategoryTheory.Iso.inv_hom_id_app,
      Category.id_comp]
  rw [horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_eq,
    horizontalFiniteTotalHomologyFilteredObjectFunctor_map_natTrans_app]
  calc
    ((horizontalCompleteFiniteHomologyFiltrationDiagramIso K
          (p + q)).hom.app p ≫
        horizontalFiniteHomologyImageMapOfBicomplex f (p + q) p ≫
        (horizontalCompleteFiniteHomologyFiltrationDiagramIso L
          (p + q)).inv.app p) ≫
        (horizontalTotalHomologyFiltration L (p + q)).ι.app
          (((p : ℤ) : EInt))
      = (horizontalCompleteFiniteHomologyFiltrationDiagramIso K
          (p + q)).hom.app p ≫
        (horizontalFiniteHomologyImageMapOfBicomplex f (p + q) p ≫
          ((horizontalCompleteFiniteHomologyFiltrationDiagramIso L
              (p + q)).inv.app p ≫
            (horizontalTotalHomologyFiltration L (p + q)).ι.app
              (((p : ℤ) : EInt)))) := by
        simp only [Category.assoc]
    _ = (horizontalCompleteFiniteHomologyFiltrationDiagramIso K
          (p + q)).hom.app p ≫
        (horizontalFiniteHomologyImageMapOfBicomplex f (p + q) p ≫
          image.ι (HomologicalComplex.homologyMap
            (horizontalFilteredTotalComplexToTotal L p) (p + q))) := by
        rw [hinvL]
    _ = (horizontalCompleteFiniteHomologyFiltrationDiagramIso K
          (p + q)).hom.app p ≫
        (image.ι (HomologicalComplex.homologyMap
            (horizontalFilteredTotalComplexToTotal K p) (p + q)) ≫
          HomologicalComplex.homologyMap
            (total.map f (ComplexShape.down ℕ)) (p + q)) := by
        rw [hfin]
    _ = ((horizontalCompleteFiniteHomologyFiltrationDiagramIso K
          (p + q)).hom.app p ≫
        image.ι (HomologicalComplex.homologyMap
            (horizontalFilteredTotalComplexToTotal K p) (p + q))) ≫
          HomologicalComplex.homologyMap
            (total.map f (ComplexShape.down ℕ)) (p + q) :=
        (Category.assoc _ _ _).symm
    _ = _ := by rw [hιK]

/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), and p,q ∈ ℕ.
The short complexes F_{p−1}H_{p+q}(Tot) → F_pH_{p+q}(Tot) → Gr_pH_{p+q}(Tot) have a morphism
induced by f. Its three components are the predecessor-stage map, the current-stage map, and
the associated graded cokernel map. Their commutation equations are the consecutive-stage
naturality square and the defining cokernel-map square. -/
noncomputable def horizontalFiltrationStepShortComplexMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    ShortComplex.cokernelSequence
        (horizontalTotalHomologyFiltrationStepMap K p q) ⟶
      ShortComplex.cokernelSequence
        (horizontalTotalHomologyFiltrationStepMap L p q) where
  τ₁ := horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q
  τ₂ := horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q
  τ₃ := horizontalTotalHomologyGradedPieceMapOfBicomplex f p q
  comm₁₂ := (horizontalTotalHomologyFiltrationStepMap_naturality f p q).symm
  comm₂₃ := by
    change horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
          f p q ≫
        cokernel.π (horizontalTotalHomologyFiltrationStepMap L p q) =
      cokernel.π (horizontalTotalHomologyFiltrationStepMap K p q) ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex f p q
    simp only [horizontalTotalHomologyGradedPieceMapOfBicomplex,
      Limits.coker_map,
      horizontalTotalHomologyFiltrationStepSquareOfBicomplex_right]
    exact (cokernel.π_desc _ _ _).symm

@[simp]
theorem horizontalFiltrationStepShortComplexMapOfBicomplex_τ₁
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalFiltrationStepShortComplexMapOfBicomplex f p q).τ₁ =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q :=
  rfl

@[simp]
theorem horizontalFiltrationStepShortComplexMapOfBicomplex_τ₂
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalFiltrationStepShortComplexMapOfBicomplex f p q).τ₂ =
      horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q :=
  rfl

@[simp]
theorem horizontalFiltrationStepShortComplexMapOfBicomplex_τ₃
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalFiltrationStepShortComplexMapOfBicomplex f p q).τ₃ =
      horizontalTotalHomologyGradedPieceMapOfBicomplex f p q :=
  rfl

private theorem isIso_horizontalPositiveCurrent_iff
    (f : K ⟶ L) (p q : ℕ) :
    IsIso (horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
        f p q) ↔
      IsIso (horizontalFiniteHomologyImageMapOfBicomplex f (p + q) p) := by
  rw [horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_eq,
    horizontalFiniteTotalHomologyFilteredObjectFunctor_map_natTrans_app]
  simp only [← CategoryTheory.Iso.app_hom, ← CategoryTheory.Iso.app_inv]
  constructor
  · intro h
    let _ := h
    have h₁ : IsIso (horizontalFiniteHomologyImageMapOfBicomplex
        f (p + q) p ≫
      ((horizontalCompleteFiniteHomologyFiltrationDiagramIso L
          (p + q)).app p).inv) :=
      IsIso.of_isIso_comp_left
        (((horizontalCompleteFiniteHomologyFiltrationDiagramIso K
            (p + q)).app p).hom) _
    let _ := h₁
    exact IsIso.of_isIso_comp_right _
      (((horizontalCompleteFiniteHomologyFiltrationDiagramIso L
          (p + q)).app p).inv)
  · intro h
    let _ := h
    infer_instance

private theorem isIso_horizontalPositivePrev_iff
    (f : K ⟶ L) (p q : ℕ) (hp : 0 < p) :
    IsIso (horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
        f p q hp) ↔
      IsIso (horizontalFiniteHomologyImageMapOfBicomplex f (p + q) (p - 1)) := by
  rw [horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_eq,
    horizontalFiniteTotalHomologyFilteredObjectFunctor_map_natTrans_app]
  constructor
  · intro h
    let _ := h
    have h₁ : IsIso (horizontalFiniteHomologyImageMapOfBicomplex
        f (p + q) (p - 1) ≫
      (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
          L (p + q) p hp).inv) :=
      IsIso.of_isIso_comp_left
        ((horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
            K (p + q) p hp).hom) _
    let _ := h₁
    exact IsIso.of_isIso_comp_right _
      ((horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
          L (p + q) p hp).inv)
  · intro h
    let _ := h
    infer_instance

private theorem isIso_horizontalFiniteHomologyImageMapOfBicomplex_of_eq
    (f : K ⟶ L) {m₁ m₂ : ℕ} (h : m₁ = m₂) (p : ℕ) :
    IsIso (horizontalFiniteHomologyImageMapOfBicomplex f m₁ p) ↔
      IsIso (horizontalFiniteHomologyImageMapOfBicomplex f m₂ p) := by
  subst h
  exact Iff.rfl

/-- Let C be an abelian category and f : K → L a bicomplex map of shape (down ℕ,down ℕ). Suppose
the induced map Gr_aH_{a+b}(Tot(K)) → Gr_aH_{a+b}(Tot(L)) is an isomorphism for every a,b ∈ ℕ.
Then for every p,q ∈ ℕ the current-stage map F_pH_{p+q}(Tot(K)) → F_pH_{p+q}(Tot(L)) is an
isomorphism. The argument compares the short exact sequences of consecutive image-filtration
stages, starting from the zero stage at integer index −1. -/
theorem isIso_horizontalPositiveCurrent_of_isIso_gradedPieceMap
    (f : K ⟶ L)
    (hf : ∀ p q : ℕ, IsIso
      (horizontalTotalHomologyGradedPieceMapOfBicomplex f p q))
    (p q : ℕ) :
    IsIso (horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
      f p q) := by
  induction p generalizing q with
  | zero =>
      refine ShortComplex.isIso₂_of_shortExact_of_isIso₁₃'
        (horizontalFiltrationStepShortComplexMapOfBicomplex f 0 q)
        (horizontalTotalHomologyFiltrationStepShortExact K 0 q)
        (horizontalTotalHomologyFiltrationStepShortExact L 0 q) ?_ (hf 0 q)
      change IsIso (horizontalPrevTotalHomologyFiltrationMapOfBicomplex f 0 q)
      have hK : IsZero ((horizontalTotalHomologyFiltration K (0 + q)).obj
          ((((0 : ℕ) : ℤ) - 1 : ℤ) : EInt)) := by
        simpa using horizontalTotalHomologyFiltration_obj_isZero_of_neg
          K (-1) (by norm_num) (0 + q)
      have hL : IsZero ((horizontalTotalHomologyFiltration L (0 + q)).obj
          ((((0 : ℕ) : ℤ) - 1 : ℤ) : EInt)) := by
        simpa using horizontalTotalHomologyFiltration_obj_isZero_of_neg
          L (-1) (by norm_num) (0 + q)
      exact IsZero.isIso hK hL _
  | succ p ih =>
      refine ShortComplex.isIso₂_of_shortExact_of_isIso₁₃'
        (horizontalFiltrationStepShortComplexMapOfBicomplex f (p + 1) q)
        (horizontalTotalHomologyFiltrationStepShortExact K (p + 1) q)
        (horizontalTotalHomologyFiltrationStepShortExact L (p + 1) q) ?_
        (hf (p + 1) q)
      have hp : 0 < p + 1 := Nat.succ_pos p
      change IsIso
        (horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
          f (p + 1) q hp)
      rw [isIso_horizontalPositivePrev_iff]
      change IsIso (horizontalFiniteHomologyImageMapOfBicomplex
        f ((p + 1) + q) p)
      rw [isIso_horizontalFiniteHomologyImageMapOfBicomplex_of_eq f
        (show (p + 1) + q = p + (q + 1) by omega) p]
      exact (isIso_horizontalPositiveCurrent_iff f p (q + 1)).1 (ih (q + 1))

/-- Let C be an abelian category and f : K → L a map of bicomplexes of shape (down ℕ,down ℕ). If
for every p,q ∈ ℕ the induced map Gr_pH_{p+q}(Tot(K)) → Gr_pH_{p+q}(Tot(L)) is an isomorphism,
then Tot(f) is a quasi-isomorphism. Here Gr_p is the cokernel of the complete image-stage
inclusion F_{p−1} → F_p, with p−1 computed in ℤ. The conclusion means that H_n(Tot(f)) is an
isomorphism for every n ∈ ℕ. -/
theorem quasiIso_totalMap_of_isIso_horizontalGradedPieceMap_firstQuadrant
    (f : K ⟶ L)
    (hf : ∀ p q : ℕ, IsIso
      (horizontalTotalHomologyGradedPieceMapOfBicomplex f p q)) :
    QuasiIso (total.map f (ComplexShape.down ℕ)) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hcurr :=
    isIso_horizontalPositiveCurrent_of_isIso_gradedPieceMap f hf n 0
  have hι := horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_ι
    f n 0
  simp only [Nat.add_zero] at hcurr hι
  let _ := hcurr
  let _ := horizontalTotalHomologyFiltration_exhaustive K n
  let _ := horizontalTotalHomologyFiltration_exhaustive L n
  have hcomp : IsIso ((horizontalTotalHomologyFiltration K n).ι.app
      (((n : ℤ) : EInt)) ≫
    HomologicalComplex.homologyMap (total.map f (ComplexShape.down ℕ)) n) := by
    rw [← hι]
    infer_instance
  let _ := hcomp
  exact IsIso.of_isIso_comp_left
    ((horizontalTotalHomologyFiltration K n).ι.app (((n : ℤ) : EInt))) _

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), and p,q ∈ ℕ.
Put r₀=max((p:ℤ)+1,(q:ℤ)+2). The stable-page map at (p,q) equals the (p,q)-component of the
fixed-page map E^{r₀}(K) → E^{r₀}(L). The bound r₀ is the canonical first-quadrant stable
index, meeting both the lower and upper finite-abutment bounds. -/
theorem horizontalStablePageMapOfBicomplex_eq_pageMap
    (f : K ⟶ L) (p q : ℕ) :
    horizontalStablePageMapOfBicomplex f p q =
      (horizontalPageMapOfBicomplex f (horizontalStablePageIndex p q)
        (horizontalStablePageIndex_one_le p q)).f (p, q) := by
  let data :=
    CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
  let r := horizontalStablePageIndex p q
  let hr := horizontalStablePageIndex_one_le p q
  let n₀ : ℤ := -((p + q + 1 : ℕ) : ℤ)
  let n₁ : ℤ := -((p + q : ℕ) : ℤ)
  let n₂ : ℤ := -((p + q : ℕ) : ℤ) + 1
  let φ := horizontalCompleteFiltrationSpectralObjectMap f
  let eK := (horizontalCompleteFiltrationSpectralObject
      K).spectralSequencePageXIso data r hr (p, q)
    (horizontalSpectralPageLowerIndex r p)
    (horizontalFirstPageLowerIndex p) (horizontalFirstPageUpperIndex p)
    (horizontalSpectralPageUpperIndex r p) rfl rfl rfl rfl n₀ n₁ n₂ (by
      change -((p + q : ℕ) : ℤ) = -(p : ℤ) - (q : ℤ)
      push_cast
      omega)
  let eL := (horizontalCompleteFiltrationSpectralObject
      L).spectralSequencePageXIso data r hr (p, q)
    (horizontalSpectralPageLowerIndex r p)
    (horizontalFirstPageLowerIndex p) (horizontalFirstPageUpperIndex p)
    (horizontalSpectralPageUpperIndex r p) rfl rfl rfl rfl n₀ n₁ n₂ (by
      change -((p + q : ℕ) : ℤ) = -(p : ℤ) - (q : ℤ)
      push_cast
      omega)
  have hpage :
      (horizontalPageMapOfBicomplex f r hr).f (p, q) ≫ eL.hom =
        eK.hom ≫
          CategoryTheory.Abelian.SpectralObject.Hom.EMap φ
            (homOfLE (data.le₀₁ r (p, q))) (homOfLE (data.le₁₂ (p, q)))
            (homOfLE (data.le₂₃ r (p, q))) n₀ n₁ n₂ := by
    rw [horizontalPageMapOfBicomplex_f]
    exact
      CategoryTheory.Abelian.SpectralObject.Hom.pageMapComponent_pageXIso_hom
        φ data r hr (p, q)
        (horizontalSpectralPageLowerIndex r p)
        (horizontalFirstPageLowerIndex p) (horizontalFirstPageUpperIndex p)
        (horizontalSpectralPageUpperIndex r p) rfl rfl rfl rfl n₀ n₁ n₂ (by
          change -((p + q : ℕ) : ℤ) = -(p : ℤ) - (q : ℤ)
          push_cast
          omega)
  apply (cancel_mono eL.hom).1
  rw [hpage]
  change (eK.hom ≫
      CategoryTheory.Abelian.SpectralObject.Hom.EMap φ
        (homOfLE (data.le₀₁ r (p, q))) (homOfLE (data.le₁₂ (p, q)))
        (homOfLE (data.le₂₃ r (p, q))) n₀ n₁ n₂ ≫ eL.inv) ≫ eL.hom =
    eK.hom ≫
      CategoryTheory.Abelian.SpectralObject.Hom.EMap φ
        (homOfLE (data.le₀₁ r (p, q))) (homOfLE (data.le₁₂ (p, q)))
        (homOfLE (data.le₂₃ r (p, q))) n₀ n₁ n₂
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Let C be an abelian category, f : K → L an invertible bicomplex morphism of shape (down ℕ,down
ℕ), and p,q ∈ ℕ. The induced map E^{r₀}_{p,q}(K) → E^{r₀}_{p,q}(L) is an isomorphism, where
r₀=max((p:ℤ)+1,(q:ℤ)+2) is the chosen stable-page index. Its inverse is the stable-page map
induced by f⁻¹. -/
noncomputable instance isIso_horizontalStablePageMapOfBicomplex
    (f : K ⟶ L) [IsIso f] (p q : ℕ) :
    IsIso (horizontalStablePageMapOfBicomplex f p q) := by
  rw [horizontalStablePageMapOfBicomplex_eq_pageMap]
  infer_instance

/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), and p,q ∈ ℕ.
If the induced stable-page map at (p,q) is an isomorphism, then Gr_pH_{p+q}(Tot(K)) →
Gr_pH_{p+q}(Tot(L)) is an isomorphism. The stable page is r₀=max(p+1,q+2), computed in ℤ. The
conclusion follows through the natural stable-term isomorphisms E^{r₀}_{p,q} ≅
Gr_pH_{p+q}(Tot). -/
theorem
    isIso_horizontalTotalHomologyGradedPieceMapOfBicomplex_of_isIso_horizontalStablePageMap
    (f : K ⟶ L) (p q : ℕ)
    (hf : IsIso (horizontalStablePageMapOfBicomplex f p q)) :
    IsIso (horizontalTotalHomologyGradedPieceMapOfBicomplex f p q) := by
  have hnat := horizontalStablePageGradedIsoAtIndex_naturality f p q
  have heq : horizontalTotalHomologyGradedPieceMapOfBicomplex f p q =
      (horizontalStablePageGradedIsoAtIndex K p q).inv ≫
        horizontalStablePageMapOfBicomplex f p q ≫
        (horizontalStablePageGradedIsoAtIndex L p q).hom := by
    rw [← cancel_epi (horizontalStablePageGradedIsoAtIndex K p q).hom]
    simp only [Iso.hom_inv_id_assoc]
    rw [hnat]
  rw [heq]
  let _ := hf
  infer_instance

/-- Let C be an abelian category and f : K → L a bicomplex map of shape (down ℕ,down ℕ). Suppose
that for every p,q ∈ ℕ the induced stable-page map E^{r₀(p,q)}_{p,q}(K) → E^{r₀(p,q)}_{p,q}(L)
is an isomorphism, where r₀(p,q)=max((p:ℤ)+1,(q:ℤ)+2). Then Tot(f) is a quasi-isomorphism. The
stable comparisons give isomorphisms on every associated graded piece, and the finite
exhaustive image filtrations give isomorphisms on H_n(Tot) for all n ∈ ℕ. -/
theorem quasiIso_totalMap_of_isIso_horizontalStablePageMap_firstQuadrant
    (f : K ⟶ L)
    (hf : ∀ p q : ℕ, IsIso (horizontalStablePageMapOfBicomplex f p q)) :
    QuasiIso (total.map f (ComplexShape.down ℕ)) :=
  quasiIso_totalMap_of_isIso_horizontalGradedPieceMap_firstQuadrant f
    (fun p q ↦
      isIso_horizontalTotalHomologyGradedPieceMapOfBicomplex_of_isIso_horizontalStablePageMap
        f p q (hf p q))

end HomologicalComplex₂

end
