/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantSecondPageMap
public import
  MathlibExt.Algebra.Homology.FirstQuadrantStablePageGradedNaturality
public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyFiltrationNaturality

/-!
# Spectral-sequence comparison for first-quadrant bicomplexes

For a morphism `f : K ⟶ L` of first-quadrant bicomplexes, an isomorphism on
every associated graded piece of total homology, or on every stable page of
the horizontal-filtration spectral sequence, implies that the induced map of
total complexes is a quasi-isomorphism.

The graded statement is proved by induction on the finite filtration of total
homology, using the five lemma on consecutive filtration steps.  The stable
statement follows from naturality of the stable-page/associated-graded
comparison.  Propagation of an isomorphism from the second page through
successor pages to the stable page is not included here.
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

/-- The current-stage total-homology filtration map induced by a bicomplex
morphism commutes with the inclusions into total homology. Not a `simp`
lemma: the upstream `@[simp]` unfolding of the current-stage map rewrites
the left-hand side before this commutation can match, so consumers rewrite
by name. -/
@[reassoc]
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

/-- The short-complex map between consecutive-step cokernel sequences induced
by a bicomplex morphism. -/
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

/-- If a bicomplex morphism induces isomorphisms on all associated graded
pieces, then it induces isomorphisms on all current-stage total-homology
filtration objects. -/
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

/-- Comparison theorem, graded form: if a bicomplex morphism induces
isomorphisms on all associated graded pieces of total homology for the
horizontal filtration, then its total map is a quasi-isomorphism. -/
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
/-- The stable-page map induced by a bicomplex morphism is the corresponding
component of the fixed-page map at the stable index. -/
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

/-- A bicomplex isomorphism induces an isomorphism on every stable page of
the horizontal-filtration spectral sequence. -/
noncomputable instance isIso_horizontalStablePageMapOfBicomplex
    (f : K ⟶ L) [IsIso f] (p q : ℕ) :
    IsIso (horizontalStablePageMapOfBicomplex f p q) := by
  rw [horizontalStablePageMapOfBicomplex_eq_pageMap]
  infer_instance

/-- A stable-page isomorphism induces an isomorphism on the corresponding
associated graded piece of total homology. -/
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

/-- Comparison theorem, stable form: if a bicomplex morphism induces
isomorphisms on all stable pages of the horizontal-filtration spectral
sequence, then its total map is a quasi-isomorphism. -/
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
