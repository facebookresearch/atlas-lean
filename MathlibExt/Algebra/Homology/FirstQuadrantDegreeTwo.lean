/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.FirstQuadrantConvergence
import Lean.Elab.Tactic.Omega

/-!
# A degree-two consequence of first-quadrant convergence

For the original horizontal-filtration spectral sequence of a first-quadrant
homological bicomplex, zero total H2 and zero E2 at (0, 1) imply zero E2 at
(2, 0). Its only possible outgoing differential is d2 to (0, 1), while every
incoming differential has negative vertical source degree. Page three is
already stable at (2, 0).

This is the abstract low-degree calculation in Weibel, *The K-book*, IV,
Lemma 1.3.1, printed page 262. Identifying these terms with the homology of an
actual fibration or with native group homology is a separate obligation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace HomologicalComplex₂

/-- Zero total H2 and zero E2 at (0, 1) force zero E2 at (2, 0) in the
actual first-quadrant horizontal-filtration spectral sequence. -/
theorem isZero_horizontalSecondPage_two_zero_of_totalH2_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (hTotal : IsZero ((K.total (ComplexShape.down ℕ)).homology 2))
    (h01 : IsZero
      (((horizontalFirstQuadrantSpectralSequence K).page 2).X (0, 1))) :
    IsZero (((horizontalFirstQuadrantSpectralSequence K).page 2).X (2, 0)) := by
  let S := horizontalFirstQuadrantSpectralSequence K
  let P := S.page 2
  let c := ComplexShape.spectralSequenceNat ⟨-(2 : ℤ), (2 : ℤ) - 1⟩
  have hOut (i : ℕ × ℕ) : P.d (2, 0) i = 0 := by
    by_cases hrel : c.Rel (2, 0) i
    · have hp : (2 : ℤ) + (-2) = (i.1 : ℤ) := hrel.1
      have hq : (0 : ℤ) + (2 - 1) = (i.2 : ℤ) := hrel.2
      have hi : i = (0, 1) := by
        apply Prod.ext <;> omega
      subst i
      exact h01.eq_of_tgt _ _
    · exact P.shape (2, 0) i hrel
  have hIn (i : ℕ × ℕ) : P.d i (2, 0) = 0 := by
    apply P.shape
    intro hrel
    have hq : (i.2 : ℤ) + (2 - 1) = (0 : ℤ) := hrel.2
    omega
  let e23 : P.X (2, 0) ≅ (S.page 3).X (2, 0) :=
    (P.iCyclesIso (2, 0) (c.next (2, 0)) rfl (hOut _)).symm ≪≫
      P.isoHomologyπ (c.prev (2, 0)) (2, 0) rfl (hIn _) ≪≫
        S.iso 2 3 (2, 0) rfl (by decide)
  let F := horizontalTotalHomologyFiltration K 2
  let _ : IsIso (F.ι.app ((2 : ℤ) : EInt)) :=
    horizontalTotalHomologyFiltration_exhaustive K 2
  have hUpper : IsZero (F.obj ((2 : ℤ) : EInt)) :=
    hTotal.of_iso (asIso (F.ι.app ((2 : ℤ) : EInt)))
  let d := horizontalTotalHomologyFiltrationStepMap K 2 0
  let _ : Epi d := hUpper.epi d
  have hGraded : IsZero (horizontalTotalHomologyGradedPiece K 2 0) :=
    isZero_cokernel_of_epi d
  exact hGraded.of_iso (e23 ≪≫
    horizontalStablePageGradedIso K 3 (by decide) 2 0 (by decide) (by decide))

end HomologicalComplex₂

end
