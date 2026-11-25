/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantConvergence

/-!
# Columnwise collapse of a first-quadrant spectral sequence

Vanishing of a second-page term persists on every later page.  At a stable
page, bounded convergence therefore transports this vanishing to the
corresponding associated graded piece of total homology.  Since that graded
piece is the cokernel of a monic filtration step, the filtration step is an
isomorphism.

In particular, if the second page is concentrated in horizontal degree zero,
all positive steps of the induced total-homology filtration are isomorphisms.
This file deliberately isolates that filtration-collapse statement from the
additional edge-map comparison between the surviving second-page column and
the zeroth filtration stage.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- Vanishing at a fixed bidegree on the second page persists after any
finite number of successor pages. -/
theorem isZero_horizontalPage_add_two_of_isZero_secondPage
    (p q m : ℕ)
    (h : IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q))) :
    IsZero (((horizontalFirstQuadrantSpectralSequence K).page
      ((m : ℤ) + 2)).X (p, q)) := by
  induction m with
  | zero => simpa
  | succ m ih =>
      have hhomology : IsZero
          (((horizontalFirstQuadrantSpectralSequence K).page
            ((m : ℤ) + 2)).homology (p, q)) :=
        (HomologicalComplex.ExactAt.of_isZero ih).isZero_homology
      exact IsZero.of_iso hhomology
        ((horizontalFirstQuadrantSpectralSequence K).iso
          ((m : ℤ) + 2) (((m + 1 : ℕ) : ℤ) + 2) (p, q)
          (by push_cast; omega) (by omega)).symm

/-- A second-page zero is still zero on the canonical stable page. -/
theorem isZero_horizontalStablePage_of_isZero_secondPage
    (p q : ℕ)
    (h : IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q))) :
    IsZero (((horizontalFirstQuadrantSpectralSequence K).page
      (horizontalStablePageIndex p q)).X (p, q)) := by
  have hr : 2 ≤ horizontalStablePageIndex p q := by
    exact le_trans (by omega)
      (horizontalStablePageIndex_upper_bound p q)
  let m := (horizontalStablePageIndex p q - 2).toNat
  have hrm : horizontalStablePageIndex p q = (m : ℤ) + 2 := by
    dsimp [m]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hz :=
    isZero_horizontalPage_add_two_of_isZero_secondPage K p q m h
  exact IsZero.of_iso hz
    (CategoryTheory.SpectralSequence.pageXIsoOfEq
      (horizontalFirstQuadrantSpectralSequence K) (p, q)
      (horizontalStablePageIndex p q) ((m : ℤ) + 2) hrm
      (horizontalStablePageIndex_one_le p q))

/-- If a second-page term vanishes, then the corresponding associated graded
piece of total homology vanishes. -/
theorem isZero_horizontalTotalHomologyGradedPiece_of_secondPage
    (p q : ℕ)
    (h : IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q))) :
    IsZero (horizontalTotalHomologyGradedPiece K p q) :=
  IsZero.of_iso
    (isZero_horizontalStablePage_of_isZero_secondPage K p q h)
    (horizontalStablePageGradedIsoAtIndex K p q).symm

/-- If a second-page term vanishes, the corresponding consecutive step of
the induced total-homology filtration is an isomorphism. -/
theorem horizontalTotalHomologyFiltrationStepMap_isIso_of_secondPage_isZero
    (p q : ℕ)
    (h : IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q))) :
    IsIso (horizontalTotalHomologyFiltrationStepMap K p q) := by
  have hgraded : IsZero (horizontalTotalHomologyGradedPiece K p q) :=
    isZero_horizontalTotalHomologyGradedPiece_of_secondPage K p q h
  have hepi : Epi (horizontalTotalHomologyFiltrationStepMap K p q) :=
    Preadditive.epi_of_isZero_cokernel
      (horizontalTotalHomologyFiltrationStepMap K p q) hgraded
  let _ := hepi
  exact isIso_of_mono_of_epi _

end HomologicalComplex₂

end
