/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMiddleQCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBasisExt

/-! The compact cocycle matrix is the full original seven-factor middle Q automorphism. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

private theorem q_ext (q r : Q)
    (h : toAdd q.base = toAdd r.base ∧ toAdd q.coeff = toAdd r.coeff) : q = r :=
  NormalizedCocycleExtension.Extension.ext (toAdd.injective h.1) (toAdd.injective h.2)

private def factor (k : Fin 3) : localFiberSubgroup :=
  if k = 0 then monsterSourcePermutationFiber 0 else
    if k = 1 then monsterSourcePermutationFiber 1 else xiSpinLocalFiber

private def prefixFiber : ℕ → localFiberSubgroup
  | 0 => 1
  | r + 1 => factor
      (generatedSeventhXiMiddleQLetters ⟨r % 7, Nat.mod_lt _ (by decide)⟩) * prefixFiber r

private theorem factor_action (k : Fin 3) (q : Q) :
    generatedSeventhLocalQAction (factor k) q = generatedSeventhQGenerator k q := by
  fin_cases k
  · exact monsterSourcePermutationSpin_conjugation 0 q
  · exact monsterSourcePermutationSpin_conjugation 1 q
  · exact xiSpinHolomorph_conjugation q

private theorem prefix_basis (r : ℕ) (hr : r ≤ 7) (j : Fin 24) :
    generatedSeventhLocalQAction (prefixFiber r) (xiSpinBinaryBasisLift j) =
      generatedSeventhXiMiddleQState ⟨r, by omega⟩ j := by
  induction r with
  | zero =>
      simp only [prefixFiber, map_one, MulAut.one_apply]
      exact (q_ext _ _ (generatedSeventhXiMiddleQ_start j)).symm
  | succ r ih =>
      have hlt : r < 7 := by omega
      rw [prefixFiber, map_mul, MulAut.mul_apply, ih (by omega), factor_action]
      have hm : (⟨r % 7, Nat.mod_lt _ (by decide)⟩ : Fin 7) = ⟨r, hlt⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hlt)
      rw [hm]
      exact q_ext _ _ (generatedSeventhXiMiddleQ_step ⟨r, hlt⟩ j)

/-- Each compact basis image retains the full original preferred-Q central phase. -/
theorem generatedSeventhXiMiddleQ_original_basis (j : Fin 24) :
    generatedSeventhLocalQAction generatedSeventhLocalFiber (xiSpinBinaryBasisLift j) =
      generatedSeventhXiMiddleQState 7 j := by
  have he : prefixFiber 7 = generatedSeventhLocalFiber := by
    have hp : prefixFiber 7 = xiSpinLocalFiber * (monsterSourcePermutationFiber 1 *
        (xiSpinLocalFiber * (monsterSourcePermutationFiber 0 *
          (monsterSourcePermutationFiber 1 * (monsterSourcePermutationFiber 0 *
            (xiSpinLocalFiber * 1)))))) := by rfl
    rw [hp]
    simp only [generatedSeventhLocalFiber, mul_one, mul_assoc]
  rw [← he]
  exact prefix_basis 7 (by decide) j

private theorem hom_central (M N : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hc : ∀ i j, qBeta (M *ᵥ Pi.single i 1) (M *ᵥ Pi.single j 1) =
      qBeta (Pi.single i 1) (Pi.single j 1) + N i j + N j i) (c : ZMod 2) :
    generatedFourthLiftQMatrixHom M N hc (qCentral c) = qCentral c := by
  apply NormalizedCocycleExtension.Extension.ext
  · change ofAdd (M *ᵥ 0) = ofAdd 0
    rw [Matrix.mulVec_zero]
  · change ofAdd (c + generatedFourthLiftQMatrixPhase N 0) = ofAdd c
    simp only [generatedFourthLiftQMatrixPhase, map_zero, add_zero]

/-- Equality on all original preferred lifts and the center identifies the whole homomorphism. -/
theorem generatedSeventhXiMiddleQHom_eq_original :
    generatedSeventhXiMiddleQHom =
      (generatedSeventhLocalQAction generatedSeventhLocalFiber).toMonoidHom := by
  apply generatedFourth_lift_q_hom_ext
  · intro j
    rw [MulEquiv.coe_toMonoidHom, generatedSeventhXiMiddleQ_original_basis]
    exact q_ext _ _ (generatedSeventhXiMiddleQHom_basis j)
  · change generatedSeventhXiMiddleQHom (qCentral 1) = spinConjugation _ (qCentral 1)
    rw [spinConjugation_central]
    exact hom_central _ _ _ 1

/-- The fast matrix formula is the genuine original source Q image on every group element. -/
theorem generatedSeventhXiMiddleQHom_apply (q : Q) :
    generatedSeventhXiMiddleQHom q = generatedSeventhQImage q := by
  have h := DFunLike.congr_fun generatedSeventhXiMiddleQHom_eq_original q
  change generatedSeventhXiMiddleQHom q = spinConjugation generatedSeventhLocalFiber.val.1 q at h
  exact h.trans (generatedSeventh_spin_conjugation q)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
