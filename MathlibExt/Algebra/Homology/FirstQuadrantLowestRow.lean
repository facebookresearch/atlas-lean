/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.FirstQuadrantEdge
import Lean.Elab.Tactic.Omega

/-!
# The lowest nonvanishing row of a first-quadrant spectral sequence

Let C be an abelian category and K a bicomplex of shape (down ℕ,down ℕ). Suppose E²_{a,b}=0
for every a ∈ ℕ and b<q. The zero-column term E²_{0,q} then persists to every page
E^{m+2}_{0,q}. For r≥2 the differential has bidegree (−r,r−1): outgoing arrows from column
zero leave the first quadrant, and incoming arrows originate in lower rows.

If Tot(K) is acyclic, bounded first-quadrant convergence identifies a sufficiently late
zero-column term with a graded piece of zero total homology. Consequently E²_{0,q}=0.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

public section

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))

private theorem lowestRow_page_isZero_of_secondPage (a b : ℕ) (r : ℤ) (hr : 2 ≤ r)
    (h : IsZero (((horizontalFirstQuadrantSpectralSequence K).page 2).X (a, b))) :
    IsZero (((horizontalFirstQuadrantSpectralSequence K).page r (by omega)).X (a, b)) := by
  let m := (r - 2).toNat
  have hm : r = (m : ℤ) + 2 := by
    dsimp only [m]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  exact IsZero.of_iso
    (isZero_horizontalPage_add_two_of_isZero_secondPage K a b m h)
    (CategoryTheory.SpectralSequence.pageXIsoOfEq
      (horizontalFirstQuadrantSpectralSequence K) (a, b) r ((m : ℤ) + 2) hm (by omega))

private theorem lowestRow_outgoing_zero (q : ℕ) (r : ℤ) (hr : 2 ≤ r) (i : ℕ × ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page r (by omega)).d (0, q) i = 0 := by
  apply HomologicalComplex.shape
  intro h
  have hp : (0 : ℤ) + (-r) = (i.1 : ℤ) := h.1
  omega

private theorem lowestRow_incoming_zero (q : ℕ)
    (hBelow : ∀ b : ℕ, b < q → ∀ a : ℕ,
      IsZero (((horizontalFirstQuadrantSpectralSequence K).page 2).X (a, b)))
    (r : ℤ) (hr : 2 ≤ r) (i : ℕ × ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page r (by omega)).d i (0, q) = 0 := by
  let P := (horizontalFirstQuadrantSpectralSequence K).page r
  let c := ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩
  by_cases hrel : c.Rel i (0, q)
  · have hq : (i.2 : ℤ) + (r - 1) = (q : ℤ) := hrel.2
    have hlt : i.2 < q := by omega
    have hz : IsZero (P.X i) :=
      lowestRow_page_isZero_of_secondPage K i.1 i.2 r hr (hBelow i.2 hlt i.1)
    exact hz.eq_of_src _ _
  · exact P.shape i (0, q) hrel

private def lowestRow_pageSuccIso (q : ℕ)
    (hBelow : ∀ b : ℕ, b < q → ∀ a : ℕ,
      IsZero (((horizontalFirstQuadrantSpectralSequence K).page 2).X (a, b)))
    (r : ℤ) (hr : 2 ≤ r) :
    ((horizontalFirstQuadrantSpectralSequence K).page r (by omega)).X (0, q) ≅
      ((horizontalFirstQuadrantSpectralSequence K).page (r + 1) (by omega)).X (0, q) := by
  let S := horizontalFirstQuadrantSpectralSequence K
  let P := S.page r
  let c := ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩
  have hOut : P.d (0, q) (c.next (0, q)) = 0 :=
    lowestRow_outgoing_zero K q r hr _
  have hIn : P.d (c.prev (0, q)) (0, q) = 0 :=
    lowestRow_incoming_zero K q hBelow r hr _
  exact (P.iCyclesIso (0, q) (c.next (0, q)) rfl hOut).symm ≪≫
    P.isoHomologyπ (c.prev (0, q)) (0, q) rfl hIn ≪≫
      S.iso r (r + 1) (0, q) rfl (by omega)

/-- Let C be an abelian category and K a bicomplex of shape (down ℕ,down ℕ). For q,m ∈ ℕ, suppose
E²_{a,b} is a zero object for every a ∈ ℕ and b<q. There is a canonical isomorphism E²_{0,q} ≅
E^{m+2}_{0,q} in the horizontal first-quadrant spectral sequence. The page-r differential has
bidegree (−r,r−1); for r≥2 there is no outgoing arrow from (0,q) within the first quadrant,
while every possible incoming source has second coordinate below q and remains zero. The
isomorphism is the composite of the resulting successor-page homology isomorphisms. -/
def horizontalLowestRowZeroColumnPageIso (q m : ℕ)
    (hBelow : ∀ b : ℕ, b < q → ∀ a : ℕ,
      IsZero (((horizontalFirstQuadrantSpectralSequence K).page 2).X (a, b))) :
    ((horizontalFirstQuadrantSpectralSequence K).page 2).X (0, q) ≅
      ((horizontalFirstQuadrantSpectralSequence K).page ((m : ℤ) + 2)).X (0, q) := by
  induction m with
  | zero => exact Iso.refl _
  | succ m ih =>
      let r : ℤ := (m : ℤ) + 2
      let e := lowestRow_pageSuccIso K q hBelow r (by dsimp only [r]; omega)
      let eIndex := CategoryTheory.SpectralSequence.pageXIsoOfEq
        (horizontalFirstQuadrantSpectralSequence K) (0, q) (r + 1)
        (((m + 1 : ℕ) : ℤ) + 2) (by dsimp only [r]; push_cast; omega) (by omega)
      exact ih ≪≫ e ≪≫ eIndex

/-- Let C be an abelian category and K a bicomplex of shape (down ℕ,down ℕ). Suppose Tot(K) is
acyclic, and for q ∈ ℕ suppose E²_{a,b}=0 for every a ∈ ℕ and b<q in its horizontal
first-quadrant spectral sequence. Then E²_{0,q} is a zero object. The lower-row hypothesis
makes this term persist to later pages, while bounded convergence identifies a late term with
Gr_0H_q(Tot(K)), which vanishes by acyclicity. -/
theorem isZero_horizontalSecondPage_zeroColumn_of_total_acyclic_of_lower_rows
    (q : ℕ) (hTotal : (K.total (ComplexShape.down ℕ)).Acyclic)
    (hBelow : ∀ b : ℕ, b < q → ∀ a : ℕ,
      IsZero (((horizontalFirstQuadrantSpectralSequence K).page 2).X (a, b))) :
    IsZero (((horizontalFirstQuadrantSpectralSequence K).page 2).X (0, q)) := by
  let F := horizontalTotalHomologyFiltration K q
  have hH : IsZero ((K.total (ComplexShape.down ℕ)).homology q) :=
    (hTotal q).isZero_homology
  have hI : F.ι.app ((0 : ℤ) : EInt) = 0 := hH.eq_of_tgt _ _
  have hF : IsZero (F.obj ((0 : ℤ) : EInt)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (cancel_mono (F.ι.app ((0 : ℤ) : EInt))).mp
    simp only [Category.id_comp, zero_comp, hI]
  have hG : IsZero (horizontalTotalHomologyGradedPiece K 0 q) :=
    IsZero.of_iso hF (horizontalTotalHomologyGradedPieceZeroIsoFiltrationZero K q)
  have hLate : IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page ((q : ℤ) + 2)).X (0, q)) :=
    IsZero.of_iso hG (horizontalStablePageGradedIso K ((q : ℤ) + 2) (by omega)
      0 q (by omega) (by omega))
  exact IsZero.of_iso hLate (horizontalLowestRowZeroColumnPageIso K q q hBelow)

end HomologicalComplex₂
