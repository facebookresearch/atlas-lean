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
# The zero-column edge isomorphism of a collapsed second page

Let K be a bicomplex in an abelian category, with both differentials
lowering nonnegative degrees. Its horizontal spectral sequence has
d^r of bidegree (−r,r−1). If E²_(p,q) is zero for every p ≥ 1 and
q ≥ 0, the zero-column term E²_(0,n) is unchanged on every later page.

At the stable page it is gr_0 H_n(Tot(K)). The preceding filtration
stage F_(−1)H_n is zero, so this graded piece is F_0 H_n.
The positive filtration steps on the total-degree diagonal are
isomorphisms; finite exhaustiveness gives F_0 H_n ≅ H_n(Tot(K)).
Their composite is the edge isomorphism
E²_(0,n) ≅ H_n(Tot(K)) for every n ≥ 0.
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

/-- For a nonnegative homological bicomplex K in an abelian
category and an integer r ≥ 2, assume E^r_(p,q) is zero for every
p ≥ 1 and q ≥ 0. Then E^r_(0,n) is isomorphic to its homology
as an object of page r, for every n ≥ 0.
The outgoing differential has no nonnegative horizontal target,
and each possible incoming source is a zero positive-column object. -/
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

/-- For a nonnegative homological bicomplex K in an abelian
category, r ≥ 2 and E^r_(p,q) zero whenever p ≥ 1,
the page homology comparison gives
E^r_(0,n) ≅ E^(r+1)_(0,n) for every n ≥ 0. -/
noncomputable def horizontalZeroColumnPageSuccIso
    (r : ℤ) (hr : 2 ≤ r) (n : ℕ)
    (hpos : ∀ p q : ℕ, 1 ≤ p → IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page r).X (p, q))) :
    ((horizontalFirstQuadrantSpectralSequence K).page r).X (0, n) ≅
      ((horizontalFirstQuadrantSpectralSequence K).page (r + 1)).X (0, n) :=
  horizontalZeroColumnPageHomologyIso K r hr n hpos ≪≫
    (horizontalFirstQuadrantSpectralSequence K).iso r (r + 1) (0, n)
      rfl (by omega)

/-- For a nonnegative homological bicomplex K in an abelian
category, assume E²_(p,q) is zero for p ≥ 1 and all q ≥ 0.
For n,m ≥ 0, successive page homology comparisons give
E²_(0,n) ≅ E^(m+2)_(0,n).
The comparison stays on the same bidegree (0,n). -/
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

/-- For a nonnegative homological bicomplex K in an abelian
category with E²_(p,q) zero for every positive horizontal degree,
there is an isomorphism E²_(0,n) ≅ E^(n+2)_(0,n).
The index n+2 is the canonical stable-page index at (0,n). -/
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

/-- For a nonnegative homological bicomplex K in an abelian
category, the induced total-homology filtration has F_(−1)H_n = 0.
Therefore gr_0 H_n(Tot(K)) ≅ F_0 H_n(Tot(K)) for every n ≥ 0,
with no concentration hypothesis needed for this identity. -/
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

/-- For a nonnegative homological bicomplex K in an abelian
category, suppose E²_(a,b) is zero for every a ≥ 1 and b ≥ 0.
For p,q ≥ 0, the filtration transition induces
F_0 H_(p+q)(Tot(K)) ≅ F_p H_(p+q)(Tot(K)).
This statement stays on the fixed total-degree diagonal p+q. -/
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

/-- For a nonnegative homological bicomplex K in an abelian
category with E² zero in positive horizontal degrees,
F_0 H_n(Tot(K)) ≅ H_n(Tot(K)) for every n ≥ 0.
It is the transition to the exhaustive stage F_n H_n followed by
that stage's inclusion in total homology. -/
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

/-- For a nonnegative homological bicomplex K in an abelian
category, if E²_(p,q) is zero for p ≥ 1 and all q ≥ 0, then
E²_(0,n) ≅ H_n(Tot(K)) for every n ≥ 0.
The map combines the stable-page comparison, the zeroth graded-piece
comparison and the exhaustive total-homology filtration inclusion. -/
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
