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
# A degree-two vanishing consequence of first-quadrant convergence

Let K be a bicomplex in an abelian category, with both differentials
lowering nonnegative degrees. For its horizontal-filtration spectral
sequence, if H_2(Tot(K)) is zero and E²_(0,1) is zero, then E²_(2,0)
is zero.

The only possible outgoing second-page differential from (2,0) is
d² : E²_(2,0) → E²_(0,1); every incoming differential would have
negative vertical source degree. Hence E²_(2,0) ≅ E³_(2,0), and
page three is already gr_2 H_2(Tot(K)).

Reference: Weibel, *The K-book*, IV, Lemma 1.3.1, p. 262.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace HomologicalComplex₂

/-- For a bicomplex K in an abelian category C with both
homological indices in ℕ, suppose H_2(Tot(K)) and E²_(0,1)
of its horizontal spectral sequence are zero objects.
Then E²_(2,0) is also a zero object.
The second-page differential has bidegree (−2,1), and
E³_(2,0) is the stable graded piece of total degree-two homology. -/
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
