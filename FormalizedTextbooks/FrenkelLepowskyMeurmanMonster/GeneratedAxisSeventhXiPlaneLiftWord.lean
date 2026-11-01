/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneLiftCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhQWord

/-! The exact original permutation word and its full preferred-basis conjugation images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Each source letter is the original simultaneous spin/Leech lift, with honest inverses. -/
def generatedSeventhXiPlaneFactor (k : Fin 4) : localFiberSubgroup :=
  if h : k.val < 2 then monsterSourcePermutationFiber ⟨k.val, h⟩
  else (monsterSourcePermutationFiber ⟨k.val - 2, by omega⟩)⁻¹

/-- Prefix products retain the stated application order of the thirteen source letters. -/
def generatedSeventhXiPlanePrefix : ℕ → localFiberSubgroup
  | 0 => 1
  | r + 1 => generatedSeventhXiPlaneFactor
      (generatedSeventhXiPlaneLetters ⟨r % 13, Nat.mod_lt _ (by decide)⟩) *
        generatedSeventhXiPlanePrefix r

/-- The original source permutation lift, before conjugating the genuine Xi. -/
def generatedSeventhXiPlanePermutationFiber : localFiberSubgroup :=
  generatedSeventhXiPlanePrefix 13

private theorem q_ext (q r : Q)
    (h : toAdd q.base = toAdd r.base ∧ toAdd q.coeff = toAdd r.coeff) : q = r :=
  NormalizedCocycleExtension.Extension.ext (toAdd.injective h.1) (toAdd.injective h.2)

private theorem inverse_forward (g : MulAut Q) (a b : Q) (h : g b = a) :
    g⁻¹ a = b := by
  rw [← h]
  exact MulAut.inv_apply_self Q g b

/-- Each checked forward/inverse state is the exact original spin-conjugation image. -/
theorem generatedSeventhXiPlaneFactor_state (r : Fin 13) (j : Fin 24) :
    generatedSeventhLocalQAction (generatedSeventhXiPlaneFactor (generatedSeventhXiPlaneLetters r))
      (generatedSeventhXiPlaneQState r.castSucc j) = generatedSeventhXiPlaneQState r.succ j := by
  have h := generatedSeventhXiPlaneQState_step r j
  have hp (k : Fin 2) (q : Q) :
      generatedSeventhLocalQAction (monsterSourcePermutationFiber k) q =
        monsterSourcePermutationImage k q := monsterSourcePermutationSpin_conjugation k q
  by_cases hk : (generatedSeventhXiPlaneLetters r).val < 2
  · simp only [hk, dite_true] at h
    simp only [generatedSeventhXiPlaneFactor, hk, dite_true]
    rw [hp]
    exact q_ext _ _ h
  · simp only [hk, dite_false] at h
    simp only [generatedSeventhXiPlaneFactor, hk, dite_false, map_inv]
    let k : Fin 2 := ⟨(generatedSeventhXiPlaneLetters r).val - 2, by omega⟩
    have hq := q_ext (monsterSourcePermutationImage k
      (generatedSeventhXiPlaneQState r.succ j))
      (generatedSeventhXiPlaneQState r.castSucc j) h
    exact inverse_forward _ _ _ ((hp k _).trans hq)

/-- Every source prefix has its checked whole-Q image on each original basis lift. -/
theorem generatedSeventhXiPlanePrefix_basis (r : ℕ) (hr : r ≤ 13) (j : Fin 24) :
    generatedSeventhLocalQAction (generatedSeventhXiPlanePrefix r) (xiSpinBinaryBasisLift j) =
      generatedSeventhXiPlaneQState ⟨r, by omega⟩ j := by
  induction r with
  | zero =>
      simp only [generatedSeventhXiPlanePrefix, map_one, MulAut.one_apply]
      exact (q_ext _ _ (generatedSeventhXiPlaneQState_start j)).symm
  | succ r ih =>
      have hlt : r < 13 := by omega
      rw [generatedSeventhXiPlanePrefix, map_mul, MulAut.mul_apply,
        ih (by omega)]
      have hmod : (⟨r % 13, Nat.mod_lt _ (by decide)⟩ : Fin 13) = ⟨r, hlt⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hlt)
      rw [hmod]
      exact generatedSeventhXiPlaneFactor_state ⟨r, hlt⟩ j

/-- The thirteen-letter genuine permutation word has all twenty-four full-phase checked images. -/
theorem generatedSeventhXiPlanePermutationFiber_basis (j : Fin 24) :
    spinConjugation generatedSeventhXiPlanePermutationFiber.val.1 (xiSpinBinaryBasisLift j) =
      generatedSeventhXiPlaneQState 13 j :=
  generatedSeventhXiPlanePrefix_basis 13 (by decide) j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
