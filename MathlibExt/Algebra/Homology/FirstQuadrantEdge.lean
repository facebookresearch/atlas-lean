/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCollapse

/-!
# The surviving edge of a column-zero first-quadrant spectral sequence

Suppose the second page of the horizontal first-quadrant spectral sequence
is zero in every positive horizontal degree.  The zero-column term has no
outgoing differential, while every possible incoming differential has zero
source.  It therefore maps isomorphically to every successor page and hence
to the stable associated graded piece.

The positive filtration steps are isomorphisms by the collapse theorem.  The
zeroth graded piece is the zeroth filtration stage because the preceding
stage is zero, and finite exhaustiveness identifies that stage with total
homology.  Composing these comparisons gives the edge isomorphism from the
surviving second-page term to total homology.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- At a page concentrated in horizontal degree zero, the zero-column object
is canonically isomorphic to its page homology. -/
noncomputable def horizontalZeroColumnPageHomologyIso
    (r : ℤ) (hr : 2 ≤ r) (n : ℕ)
    (hpos : ∀ p q : ℕ, 1 ≤ p → IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page r).X (p, q))) :
    ((horizontalFirstQuadrantSpectralSequence K).page r).X (0, n) ≅
      ((horizontalFirstQuadrantSpectralSequence K).page r).homology (0, n) := by
  let P := (horizontalFirstQuadrantSpectralSequence K).page r
  let c := ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩
  let i := c.prev (0, n)
  let j : ℕ × ℕ := (0, n)
  let k := c.next (0, n)
  have hout : P.d j k = 0 := by
    apply P.shape
    intro hjk
    change c.Rel j k at hjk
    have hfirst : (0 : ℤ) - r = (k.1 : ℤ) := by
      simpa [c, j] using hjk.1
    omega
  have hin : P.d i j = 0 := by
    by_cases hij : c.Rel i j
    · have hi : 1 ≤ i.1 := by
        have hfirst : (i.1 : ℤ) + (-r) = 0 := by
          simpa [c, j] using hij.1
        omega
      exact (hpos i.1 i.2 hi).eq_of_src _ _
    · exact P.shape i j hij
  exact (P.iCyclesIso j k rfl hout).symm ≪≫
    P.isoHomologyπ i j rfl hin

/-- The zero column is unchanged from page `r` to page `r+1` when every
positive-column object on page `r` is zero. -/
noncomputable def horizontalZeroColumnPageSuccIso
    (r : ℤ) (hr : 2 ≤ r) (n : ℕ)
    (hpos : ∀ p q : ℕ, 1 ≤ p → IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page r).X (p, q))) :
    ((horizontalFirstQuadrantSpectralSequence K).page r).X (0, n) ≅
      ((horizontalFirstQuadrantSpectralSequence K).page (r + 1)).X (0, n) :=
  horizontalZeroColumnPageHomologyIso K r hr n hpos ≪≫
    (horizontalFirstQuadrantSpectralSequence K).iso r (r + 1) (0, n)
      rfl (by omega)

/-- Under second-page concentration in horizontal degree zero, the surviving
term is unchanged after any finite number of successor pages. -/
noncomputable def horizontalSecondPageZeroColumnPageIso
    (n m : ℕ)
    (hpos : ∀ p q : ℕ, 1 ≤ p → IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q))) :
    ((horizontalFirstQuadrantSpectralSequence K).page 2).X (0, n) ≅
      ((horizontalFirstQuadrantSpectralSequence K).page
        ((m : ℤ) + 2)).X (0, n) := by
  induction m with
  | zero => exact Iso.refl _
  | succ m ih =>
      have hpage : ∀ p q : ℕ, 1 ≤ p → IsZero
          (((horizontalFirstQuadrantSpectralSequence K).page
            ((m : ℤ) + 2)).X (p, q)) :=
        fun p q hp ↦
          isZero_horizontalPage_add_two_of_isZero_secondPage
            K p q m (hpos p q hp)
      let eSucc := horizontalZeroColumnPageSuccIso K
        ((m : ℤ) + 2) (by omega) n hpage
      let ePage := CategoryTheory.SpectralSequence.pageXIsoOfEq
        (horizontalFirstQuadrantSpectralSequence K) (0, n)
        (((m : ℤ) + 2) + 1) (((m + 1 : ℕ) : ℤ) + 2)
        (by push_cast; omega) (by omega)
      exact ih ≪≫ eSucc ≪≫ ePage

/-- The second-page zero-column term identifies with its canonical stable
page under horizontal-degree-zero concentration. -/
noncomputable def horizontalSecondPageZeroColumnStableIso
    (n : ℕ)
    (hpos : ∀ p q : ℕ, 1 ≤ p → IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q))) :
    ((horizontalFirstQuadrantSpectralSequence K).page 2).X (0, n) ≅
      ((horizontalFirstQuadrantSpectralSequence K).page
        (horizontalStablePageIndex 0 n)).X (0, n) :=
  horizontalSecondPageZeroColumnPageIso K n n hpos ≪≫
    CategoryTheory.SpectralSequence.pageXIsoOfEq
      (horizontalFirstQuadrantSpectralSequence K) (0, n)
      ((n : ℤ) + 2) (horizontalStablePageIndex 0 n)
      (by
        rw [show horizontalStablePageIndex 0 n = (n : ℤ) + 2 by
          simp only [horizontalStablePageIndex]
          omega])
      (by omega)

/-- The zeroth associated graded piece is the zeroth filtration stage: its
preceding filtration stage is zero. -/
noncomputable def horizontalTotalHomologyGradedPieceZeroIsoFiltrationZero
    (n : ℕ) :
    horizontalTotalHomologyGradedPiece K 0 n ≅
      (horizontalTotalHomologyFiltration K n).obj ((0 : ℤ) : EInt) := by
  let f := horizontalTotalHomologyFiltrationStepMap K 0 n
  have hsource : IsZero
      ((horizontalTotalHomologyFiltration K (0 + n)).obj
        (((0 : ℤ) - 1 : ℤ) : EInt)) := by
    simpa using horizontalTotalHomologyFiltration_obj_isZero_of_neg
      K (-1) (by omega) (0 + n)
  have hzero : f = 0 := by
    exact hsource.eq_of_src _ _
  have hf : IsIso (cokernel.π f) := by
    rw [hzero]
    infer_instance
  let _ := hf
  let eTarget :
      (horizontalTotalHomologyFiltration K (0 + n)).obj
          ((0 : ℤ) : EInt) ≅
        (horizontalTotalHomologyFiltration K n).obj
          ((0 : ℤ) : EInt) :=
    eqToIso (congrArg
      (fun t : ℕ ↦ (horizontalTotalHomologyFiltration K t).obj
        ((0 : ℤ) : EInt)) (Nat.zero_add n))
  exact (asIso (cokernel.π f)).symm ≪≫ eTarget

/-- Under second-page concentration in horizontal degree zero, the zeroth
filtration stage is isomorphic to every finite nonnegative stage on a fixed
total-degree diagonal. -/
noncomputable def horizontalTotalHomologyFiltrationZeroStageIso
    (hpos : ∀ p q : ℕ, 1 ≤ p → IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q)))
    (p q : ℕ) :
    (horizontalTotalHomologyFiltration K (p + q)).obj
        ((0 : ℤ) : EInt) ≅
      (horizontalTotalHomologyFiltration K (p + q)).obj
        (((p : ℕ) : ℤ) : EInt) := by
  induction p generalizing q with
  | zero => exact Iso.refl _
  | succ p ih =>
      have htotal : p + (q + 1) = (p + 1) + q := by omega
      let eTotalZero :
          (horizontalTotalHomologyFiltration K (p + (q + 1))).obj
              ((0 : ℤ) : EInt) ≅
            (horizontalTotalHomologyFiltration K ((p + 1) + q)).obj
              ((0 : ℤ) : EInt) :=
        eqToIso (congrArg
          (fun t : ℕ ↦ (horizontalTotalHomologyFiltration K t).obj
            ((0 : ℤ) : EInt)) htotal)
      let eTotalStage :
          (horizontalTotalHomologyFiltration K (p + (q + 1))).obj
              (((p : ℕ) : ℤ) : EInt) ≅
            (horizontalTotalHomologyFiltration K ((p + 1) + q)).obj
              (((p : ℕ) : ℤ) : EInt) :=
        eqToIso (congrArg
          (fun t : ℕ ↦ (horizontalTotalHomologyFiltration K t).obj
            (((p : ℕ) : ℤ) : EInt)) htotal)
      have hindex :
          (((p : ℕ) : ℤ) : EInt) =
            ((((p + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt) := by
        apply congrArg (@WithBotTop.coe ℤ)
        push_cast
        omega
      let eIndex :
          (horizontalTotalHomologyFiltration K ((p + 1) + q)).obj
              (((p : ℕ) : ℤ) : EInt) ≅
            (horizontalTotalHomologyFiltration K ((p + 1) + q)).obj
              ((((p + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt) :=
        eqToIso (congrArg
          (fun i : EInt ↦
            (horizontalTotalHomologyFiltration K ((p + 1) + q)).obj i)
          hindex)
      have hstep : IsIso
          (horizontalTotalHomologyFiltrationStepMap K (p + 1) q) :=
        horizontalTotalHomologyFiltrationStepMap_isIso_of_secondPage_isZero
          K (p + 1) q (hpos (p + 1) q (by omega))
      let _ := hstep
      exact eTotalZero.symm ≪≫ ih (q + 1) ≪≫ eTotalStage ≪≫
        eIndex ≪≫ asIso
          (horizontalTotalHomologyFiltrationStepMap K (p + 1) q)

/-- Under column-zero concentration, the zeroth filtration stage is all of
total homology. -/
noncomputable def horizontalTotalHomologyFiltrationZeroTotalIso
    (n : ℕ)
    (hpos : ∀ p q : ℕ, 1 ≤ p → IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q))) :
    (horizontalTotalHomologyFiltration K n).obj ((0 : ℤ) : EInt) ≅
      (K.total (ComplexShape.down ℕ)).homology n := by
  have hexhaustive : IsIso
      ((horizontalTotalHomologyFiltration K n).ι.app
        (((n : ℕ) : ℤ) : EInt)) :=
    horizontalTotalHomologyFiltration_exhaustive K n
  let _ := hexhaustive
  exact horizontalTotalHomologyFiltrationZeroStageIso K hpos n 0 ≪≫
    asIso ((horizontalTotalHomologyFiltration K n).ι.app
      (((n : ℕ) : ℤ) : EInt))

/-- If the second page is concentrated in horizontal degree zero, its
surviving term in bidegree `(0,n)` is canonically isomorphic to degree-`n`
homology of the total complex. -/
noncomputable def horizontalSecondPageZeroColumnTotalHomologyIso
    (n : ℕ)
    (hpos : ∀ p q : ℕ, 1 ≤ p → IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q))) :
    ((horizontalFirstQuadrantSpectralSequence K).page 2).X (0, n) ≅
      (K.total (ComplexShape.down ℕ)).homology n :=
  horizontalSecondPageZeroColumnStableIso K n hpos ≪≫
    horizontalStablePageGradedIsoAtIndex K 0 n ≪≫
    horizontalTotalHomologyGradedPieceZeroIsoFiltrationZero K n ≪≫
    horizontalTotalHomologyFiltrationZeroTotalIso K n hpos

end HomologicalComplex₂

end
