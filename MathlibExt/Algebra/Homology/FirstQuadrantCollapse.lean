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
# Vanishing and filtration collapse for a first-quadrant spectral sequence

Let K be a bicomplex of shape (down ℕ,down ℕ) in an abelian category. Write E^r_{p,q} for its
horizontal spectral sequence, with p,q∈ℕ and r≥1. A zero term E^2_{p,q} remains zero at the same
bidegree on every page r≥2. The stable index is r_*(p,q)=max(p+1,q+2), and bounded convergence
identifies E^{r_*}_{p,q} with gr_pH_{p+q}(Tot K).

Consequently, E^2_{p,q}=0 implies that the monic filtration step F_{p-1}H_{p+q}(Tot
K)→F_pH_{p+q}(Tot K) has zero cokernel and is an isomorphism. Here p−1 is an integer cut, so the
source is zero when p=0. If the second page is supported in horizontal degree zero, every
positive horizontal filtration step is therefore an isomorphism. The category's object and
morphism universes are arbitrary.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- Let C be an abelian category and K a bicomplex of shape (down ℕ,down ℕ). For p,q,m∈ℕ, suppose
E^2_{p,q} is zero in the horizontal first-quadrant spectral sequence of K. Then E^{m+2}_{p,q} is
zero. Each successor page is the homology of its predecessor, so vanishing at the fixed bidegree
propagates through every finite number of pages. -/
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

/-- For a first-quadrant bicomplex K in an abelian category and p,q∈ℕ, let r_*(p,q)=max(p+1,q+2). If
the horizontal second-page term E^2_{p,q} is zero, then E^{r_*}_{p,q} is zero. The stable index
is at least two, so the result follows from the persistence of vanishing on all later pages. -/
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

/-- Let K be a bicomplex of shape (down ℕ,down ℕ) in an abelian category and p,q∈ℕ. If its
horizontal second-page term E^2_{p,q} is zero, then gr_pH_{p+q}(Tot K)=coker(F_{p-1}H_{p+q}(Tot
K)→F_pH_{p+q}(Tot K)) is zero. The conclusion uses persistence of vanishing to r_*=max(p+1,q+2)
and the stable-page comparison with this associated-graded piece; p−1 is an integer cut. -/
theorem isZero_horizontalTotalHomologyGradedPiece_of_secondPage
    (p q : ℕ)
    (h : IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q))) :
    IsZero (horizontalTotalHomologyGradedPiece K p q) :=
  IsZero.of_iso
    (isZero_horizontalStablePage_of_isZero_secondPage K p q h)
    (horizontalStablePageGradedIsoAtIndex K p q).symm

/-- For a first-quadrant bicomplex K in an abelian category and p,q∈ℕ, suppose the horizontal
second-page term E^2_{p,q} is zero. Then the canonical filtration inclusion F_{p-1}H_{p+q}(Tot
K)→F_pH_{p+q}(Tot K) is an isomorphism. Its cokernel is the associated-graded piece, which
vanishes by stable convergence, and the inclusion is monic. The cut p−1 is taken in ℤ, including
the zero preceding stage at p=0. -/
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
