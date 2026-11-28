/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantBottomRelativeHomology

/-!
# Bounded convergence to the filtration on total homology

Let K be a bicomplex in an abelian category C, with both differentials
lowering nonnegative degrees. Put T = Tot(K) with total differential
d_h+(−1)^p d_v on bidegree (p,q), and let F_a be its complete
horizontal filtration by columns p ≤ a.

For n = p+q, the finite upper stage a = n+1 has H_n(F_a) ≅ H_n(T).
The bottom-relative spectral homology groups identify with the stage
homologies. Transporting their maps to H_n(T) identifies the current
and preceding images with
F_p H_n(T) = Im(H_n(F_p) → H_n(T))
and F_(p−1) H_n(T), respectively.

Their nested-image quotient is therefore
gr_p H_n(T) = coker(F_(p−1) H_n(T) → F_p H_n(T)).
For every integer r ≥ 1 with r ≥ p+1 and r ≥ q+2, there is a canonical
isomorphism E^r_(p,q) ≅ gr_p H_(p+q)(T).
The least such page is r = max(p+1,q+2). This identifies the associated
graded of the induced homology filtration; no direct-sum splitting
is part of the statement. The category object and morphism worlds
are independent.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ComposableArrows

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- For a nonnegative homological bicomplex and p,q ≥ 0,
the upper index used in the finite abutment comparison is
p+q+1, viewed as a finite element of EInt.
This is one stage above the total degree n = p+q. -/
theorem horizontalAbutmentUpperIndex_eq_succ (p q : ℕ) :
    horizontalAbutmentUpperIndex p q =
      ((((p + q : ℕ) : ℤ) + 1) : EInt) := by
  apply congrArg (@WithBotTop.coe ℤ)
  push_cast
  omega

/-- For a nonnegative homological bicomplex K in an abelian
category C and p,q ≥ 0, the inclusion F_(p+q+1) → Tot(K)
induces the isomorphism H_(p+q)(F_(p+q+1)) ≅ H_(p+q)(Tot(K)).
The filtration contains horizontal columns up to its stage index. -/
noncomputable def horizontalAbutmentUpperHomologyToTotalIso (p q : ℕ) :
    (horizontalCompleteFilteredTotalComplex K
      (horizontalAbutmentUpperIndex p q)).homology (p + q) ≅
      (K.total (ComplexShape.down ℕ)).homology (p + q) := by
  have hIso : IsIso (horizontalCompleteHomologyToTotal K (p + q)
      (horizontalAbutmentUpperIndex p q)) := by
    rw [horizontalAbutmentUpperIndex_eq_succ]
    exact horizontalCompleteHomologyToTotal_isIso_succ K (p + q)
  let _ := hIso
  exact asIso (horizontalCompleteHomologyToTotal K (p + q)
    (horizontalAbutmentUpperIndex p q))

/-- For a bicomplex K in an abelian category with nonnegative
homological degrees, put n = p+q and u = n+1.
The bottom-to-u interval group of the complete spectral object in
cochain degree −n is isomorphic to H_n(Tot(K)).
It is the bottom-relative stage comparison followed by the
isomorphism H_n(F_u) ≅ H_n(Tot(K)). -/
noncomputable def horizontalBottomRelativeHomologyToTotalIso (p q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObject K).H
      (-((p + q : ℕ) : ℤ))).obj
        (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) ≅
      (K.total (ComplexShape.down ℕ)).homology (p + q) :=
  horizontalBottomRelativeHomologyStageIso K
      (horizontalAbutmentUpperIndex p q) (p + q) ≪≫
    horizontalAbutmentUpperHomologyToTotalIso K p q

/-- For a nonnegative homological bicomplex K in an abelian
category, put n = p+q and u = n+1. For every i ≤ u in EInt,
identifying the bottom-relative group B_i with H_n(F_i) and then
mapping to H_n(Tot(K)) equals mapping B_i → B_u first and then
using B_u ≅ H_n(Tot(K)). The diagram commutes for all such stages i. -/
theorem horizontalBottomRelativeHomologyToTotal_naturality
    (p q : ℕ) (i : EInt)
    (h : i ≤ horizontalAbutmentUpperIndex p q) :
    (horizontalBottomRelativeHomologyStageIso K i (p + q)).hom ≫
        horizontalCompleteHomologyToTotal K (p + q) i =
      ((horizontalCompleteFiltrationSpectralObject K).H
        (-((p + q : ℕ) : ℤ))).map
          (twoδ₂Toδ₁
            (horizontalBottomToStageMap i)
            (homOfLE h)
            (horizontalCanonicalAbutmentTotalMap p q)
            (Subsingleton.elim _ _)) ≫
        (horizontalBottomRelativeHomologyToTotalIso K p q).hom := by
  have hstage := horizontalBottomRelativeHomologyStageIso_naturality K h (p + q)
  have hstage' :
      ((horizontalCompleteFiltrationSpectralObject K).H
        (-((p : ℤ) + (q : ℤ)))).map
          (twoδ₂Toδ₁
            (horizontalBottomToStageMap i)
            (homOfLE h)
            (horizontalCanonicalAbutmentTotalMap p q)
            (Subsingleton.elim _ _)) ≫
        (horizontalBottomRelativeHomologyStageIso K
          (horizontalAbutmentUpperIndex p q) (p + q)).hom =
      (horizontalBottomRelativeHomologyStageIso K i (p + q)).hom ≫
        HomologicalComplex.homologyMap
          (horizontalCompleteFilteredTotalMap K h) (p + q) := by
    push_cast at hstage
    exact hstage
  have htotal := horizontalCompleteHomologyToTotal_naturality K (p + q) (homOfLE h)
  change HomologicalComplex.homologyMap
      (horizontalCompleteFilteredTotalMap K h) (p + q) ≫
        horizontalCompleteHomologyToTotal K (p + q)
          (horizontalAbutmentUpperIndex p q) =
      horizontalCompleteHomologyToTotal K (p + q) i at htotal
  rw [horizontalCompleteHomologyToTotal_eq K (p + q) i] at htotal ⊢
  rw [horizontalCompleteHomologyToTotal_eq K (p + q)
    (horizontalAbutmentUpperIndex p q)] at htotal
  dsimp [horizontalBottomRelativeHomologyToTotalIso,
    horizontalAbutmentUpperHomologyToTotalIso]
  rw [horizontalCompleteHomologyToTotal_eq K (p + q)
    (horizontalAbutmentUpperIndex p q)]
  rw [reassoc_of% hstage', htotal]

/-- For a nonnegative homological bicomplex K in an abelian
category and n = p+q, the preceding-to-upper map is
B_(p−1) → B_(n+1), where B_a is the bottom-relative interval group
in cochain degree −n. It is induced by the filtration inclusion
from the finite stage p−1 to the upper stage n+1. -/
noncomputable abbrev horizontalCanonicalAbutmentPreviousToUpperHomologyMap
    (p q : ℕ) :=
  ((horizontalCompleteFiltrationSpectralObject K).H
    (-((p + q : ℕ) : ℤ))).map
      (twoδ₂Toδ₁
        (horizontalCanonicalAbutmentLowerMap p)
        (homOfLE (show horizontalFirstPageLowerIndex p ≤
          horizontalAbutmentUpperIndex p q from
            (horizontalFirstPageIndex_le p).trans
              (horizontalAbutmentIndices_le p q).2))
        (horizontalCanonicalAbutmentTotalMap p q)
        (Subsingleton.elim _ _))

/-- For a nonnegative homological bicomplex K in an abelian
category and n = p+q, the bottom-relative maps
B_(p−1) → B_p → B_(n+1) compose to the direct map
B_(p−1) → B_(n+1). Each map is induced by the corresponding
complete-filtration inclusion. -/
theorem horizontalCanonicalAbutmentPrevious_comp_toUpper (p q : ℕ) :
    horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
        horizontalCanonicalAbutmentToUpperHomologyMap K p q =
      horizontalCanonicalAbutmentPreviousToUpperHomologyMap K p q := by
  rw [← Functor.map_comp]
  apply Functor.congr_map
  apply Subsingleton.elim

/-- For a bicomplex K in an abelian category with nonnegative
homological degrees, put n = p+q. The arrow B_p → B_(n+1) is
isomorphic to H_n(F_p) → H_n(Tot(K)).
The source isomorphism is the bottom-relative stage comparison,
and the target isomorphism is the upper-stage total comparison. -/
noncomputable def horizontalCanonicalAbutmentCurrentArrowIso (p q : ℕ) :
    Arrow.mk (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≅
      Arrow.mk (horizontalCompleteHomologyToTotal K (p + q)
        (horizontalFirstPageUpperIndex p)) :=
  Arrow.isoMk'
    (horizontalCanonicalAbutmentToUpperHomologyMap K p q)
    (horizontalCompleteHomologyToTotal K (p + q)
      (horizontalFirstPageUpperIndex p))
    (horizontalBottomRelativeHomologyStageIso K
      (horizontalFirstPageUpperIndex p) (p + q))
    (horizontalBottomRelativeHomologyToTotalIso K p q)
    (horizontalBottomRelativeHomologyToTotal_naturality K p q
      (horizontalFirstPageUpperIndex p)
      (horizontalAbutmentIndices_le p q).2)

/-- For a nonnegative homological bicomplex K in an abelian
category and n = p+q, the composite B_(p−1) → B_p → B_(n+1)
is isomorphic as an arrow to H_n(F_(p−1)) → H_n(Tot(K)).
Its endpoint maps are the bottom-relative stage and total
comparisons, with p−1 interpreted as an integer filtration stage. -/
noncomputable def horizontalCanonicalAbutmentPreviousArrowIso (p q : ℕ) :
    Arrow.mk (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
      horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≅
      Arrow.mk (horizontalCompleteHomologyToTotal K (p + q)
        (horizontalFirstPageLowerIndex p)) :=
  Arrow.isoMk'
    (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
      horizontalCanonicalAbutmentToUpperHomologyMap K p q)
    (horizontalCompleteHomologyToTotal K (p + q)
      (horizontalFirstPageLowerIndex p))
    (horizontalBottomRelativeHomologyStageIso K
      (horizontalFirstPageLowerIndex p) (p + q))
    (horizontalBottomRelativeHomologyToTotalIso K p q) (by
      rw [horizontalCanonicalAbutmentPrevious_comp_toUpper]
      exact horizontalBottomRelativeHomologyToTotal_naturality K p q
        (horizontalFirstPageLowerIndex p)
        ((horizontalFirstPageIndex_le p).trans
          (horizontalAbutmentIndices_le p q).2))

/-- For a nonnegative homological bicomplex K in an abelian
category and n = p+q, the image of B_p → B_(n+1) is isomorphic
to F_p H_n(Tot(K)) = Im(H_n(F_p) → H_n(Tot(K))).
The isomorphism is induced by the current-stage arrow comparison. -/
noncomputable def horizontalCanonicalAbutmentCurrentImageIso (p q : ℕ) :
    image (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≅
      (horizontalTotalHomologyFiltration K (p + q)).obj
        (horizontalFirstPageUpperIndex p) :=
  (Limits.im (C := C)).mapIso
    (horizontalCanonicalAbutmentCurrentArrowIso K p q)

/-- For a nonnegative homological bicomplex K in an abelian
category and n = p+q, the image of
B_(p−1) → B_p → B_(n+1) is isomorphic to
F_(p−1) H_n(Tot(K)).
The source and target homology maps are those of the preceding
stage inclusion into the upper stage and total complex. -/
noncomputable def horizontalCanonicalAbutmentPreviousImageIso (p q : ℕ) :
    image (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
      horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≅
      (horizontalTotalHomologyFiltration K (p + q)).obj
        (horizontalFirstPageLowerIndex p) :=
  (Limits.im (C := C)).mapIso
    (horizontalCanonicalAbutmentPreviousArrowIso K p q)

/-- For a nonnegative homological bicomplex K in an abelian
category, the previous and current abutment image isomorphisms
commute with their inclusion maps. Thus the square from
Im(B_(p−1) → B_(n+1)) to Im(B_p → B_(n+1))
and from F_(p−1)H_n to F_p H_n commutes, where n = p+q. -/
theorem horizontalCanonicalAbutmentImageSquare (p q : ℕ) :
    CategoryTheory.imageCompMap
        (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
        (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
      (horizontalCanonicalAbutmentCurrentImageIso K p q).hom =
    (horizontalCanonicalAbutmentPreviousImageIso K p q).hom ≫
      horizontalTotalHomologyFiltrationStepMap K p q := by
  let F := horizontalTotalHomologyFiltration K (p + q)
  let lower : EInt := horizontalFirstPageLowerIndex p
  let upper : EInt := horizontalFirstPageUpperIndex p
  have hcurrent := image.map_ι
    (horizontalCanonicalAbutmentCurrentArrowIso K p q).hom
  change (horizontalCanonicalAbutmentCurrentImageIso K p q).hom ≫
      image.ι (horizontalCompleteHomologyToTotal K (p + q) upper) =
    image.ι (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
      (horizontalBottomRelativeHomologyToTotalIso K p q).hom at hcurrent
  have hprevious := image.map_ι
    (horizontalCanonicalAbutmentPreviousArrowIso K p q).hom
  change (horizontalCanonicalAbutmentPreviousImageIso K p q).hom ≫
      image.ι (horizontalCompleteHomologyToTotal K (p + q) lower) =
    image.ι (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
      horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
      (horizontalBottomRelativeHomologyToTotalIso K p q).hom at hprevious
  have hstep := MonoOver.w (F.toMonoOver.map
    (homOfLE (horizontalTotalHomologyPrevIndex_le p)))
  change horizontalTotalHomologyFiltrationStepMap K p q ≫
      image.ι (horizontalCompleteHomologyToTotal K (p + q) upper) =
    image.ι (horizontalCompleteHomologyToTotal K (p + q) lower) at hstep
  apply (cancel_mono (image.ι
    (horizontalCompleteHomologyToTotal K (p + q) upper))).1
  calc
    _ = CategoryTheory.imageCompMap
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
        image.ι (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
        (horizontalBottomRelativeHomologyToTotalIso K p q).hom := by
      simpa only [Category.assoc] using
        CategoryTheory.imageCompMap
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫= hcurrent
    _ = image.ι (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
          horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
        (horizontalBottomRelativeHomologyToTotalIso K p q).hom := by
      simpa only [Category.assoc] using
        CategoryTheory.imageCompMap_ι
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentToUpperHomologyMap K p q) =≫
            (horizontalBottomRelativeHomologyToTotalIso K p q).hom
    _ = (horizontalCanonicalAbutmentPreviousImageIso K p q).hom ≫
        image.ι (horizontalCompleteHomologyToTotal K (p + q) lower) :=
      hprevious.symm
    _ = _ :=
      (((horizontalCanonicalAbutmentPreviousImageIso K p q).hom ≫=
        hstep).symm).trans (Category.assoc _ _ _).symm

/-- For a nonnegative homological bicomplex K in an abelian
category and n = p+q, the cokernel of the inclusion of preceding
into current bottom-relative images is isomorphic to
gr_p H_n(Tot(K)) = coker(F_(p−1)H_n → F_p H_n).
The comparison is induced by the two image isomorphisms and
their commuting inclusion square. -/
noncomputable def horizontalCanonicalAbutmentImageQuotientGradedIso
    (p q : ℕ) :
    horizontalCanonicalAbutmentImageQuotient K p q ≅
      horizontalTotalHomologyGradedPiece K p q :=
  cokernel.mapIso
    (CategoryTheory.imageCompMap
      (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
      (horizontalCanonicalAbutmentToUpperHomologyMap K p q))
    (horizontalTotalHomologyFiltrationStepMap K p q)
    (horizontalCanonicalAbutmentPreviousImageIso K p q)
    (horizontalCanonicalAbutmentCurrentImageIso K p q)
    (horizontalCanonicalAbutmentImageSquare K p q)

/-- For a nonnegative homological bicomplex K in an abelian
category and p,q ≥ 0, the canonical finite abutment term is
isomorphic to gr_p H_(p+q)(Tot(K)).
Its finite upper stage is p+q+1, and the preceding and current
stages are p−1 and p. -/
noncomputable def horizontalCanonicalAbutmentGradedIso (p q : ℕ) :
    horizontalFirstQuadrantCanonicalAbutmentTerm K p q ≅
      horizontalTotalHomologyGradedPiece K p q :=
  horizontalCanonicalAbutmentImageQuotientIso K p q ≪≫
    horizontalCanonicalAbutmentImageQuotientGradedIso K p q

/-- For a nonnegative homological bicomplex K in an abelian
category, p,q ≥ 0 and an integer r with 1 ≤ r,
p+1 ≤ r and q+2 ≤ r, the horizontal spectral sequence has
E^r_(p,q) ≅ gr_p H_(p+q)(Tot(K)).
The target is the quotient of the pth induced homology filtration
stage by the preceding stage. -/
noncomputable def horizontalStablePageGradedIso
    (r : ℤ) (hr : 1 ≤ r) (p q : ℕ)
    (hlower : (p : ℤ) + 1 ≤ r) (hupper : (q : ℤ) + 2 ≤ r) :
    ((horizontalFirstQuadrantSpectralSequence K).page r).X (p, q) ≅
      horizontalTotalHomologyGradedPiece K p q :=
  horizontalStablePageCanonicalAbutmentIso K r hr p q hlower hupper ≪≫
    horizontalCanonicalAbutmentGradedIso K p q

/-- For a nonnegative homological bicomplex K in an abelian
category and p,q ≥ 0, the page r = max(p+1,q+2) satisfies
E^r_(p,q) ≅ gr_p H_(p+q)(Tot(K)).
This is the least page index meeting both canonical bidegree bounds. -/
noncomputable def horizontalStablePageGradedIsoAtIndex (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page
      (horizontalStablePageIndex p q)).X (p, q) ≅
      horizontalTotalHomologyGradedPiece K p q :=
  horizontalStablePageGradedIso K (horizontalStablePageIndex p q)
    (horizontalStablePageIndex_one_le p q) p q
    (horizontalStablePageIndex_lower_bound p q)
    (horizontalStablePageIndex_upper_bound p q)

end HomologicalComplex₂
