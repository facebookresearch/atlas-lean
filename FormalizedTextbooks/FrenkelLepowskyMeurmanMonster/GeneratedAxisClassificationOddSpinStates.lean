/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddCoordinates

/-! The actual Pauli action on two-point Hadamard states. These states form a
finite, explicitly indexed family, with no assumed spin-orbit classification. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The eleven lower spin coordinates. -/
def generatedOddSpinLow (t : SpinIndex) : Fin 11 → ZMod 2 := fun j => t j.castSucc

/-- A two-point spin state with specified support, relative sign and global sign. -/
def generatedOddSpinState (a : Fin 11 → ZMod 2) (e c : ZMod 2) : SpinSpace :=
  fun t => if generatedOddSpinLow t = a then qSign (c + e * t 11) else 0

/-- The exact global sign produced by the original Q operator. -/
def generatedOddSpinOutputSign (q : Q) : ZMod 2 :=
  toAdd q.coeff + spinTranslation q 11 +
    ∑ j : Fin 11, spinModulation q j.castSucc * spinTranslation q j.castSucc

private theorem spin_low_eq_iff (t a : SpinIndex) :
    generatedOddSpinLow (t + a) = 0 ↔ generatedOddSpinLow t = generatedOddSpinLow a := by
  constructor
  · intro h
    ext j
    have hj := congrFun h j
    change t j.castSucc + a j.castSucc = 0 at hj
    have ha : a j.castSucc + a j.castSucc = 0 := ZModModule.add_self _
    exact add_right_cancel (hj.trans ha.symm)
  · intro h
    ext j
    have hj := congrFun h j
    change t j.castSucc = a j.castSucc at hj
    change t j.castSucc + a j.castSucc = 0
    rw [hj]
    exact ZModModule.add_self _

private theorem spin_dot_low (q : Q) (t : SpinIndex)
    (ht : generatedOddSpinLow t = generatedOddSpinLow (spinTranslation q)) :
    spinDot (spinModulation q) t =
      (∑ j : Fin 11, spinModulation q j.castSucc * spinTranslation q j.castSucc) +
        spinModulation q 11 * t 11 := by
  unfold spinDot
  rw [Fin.sum_univ_castSucc]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [show t j.castSucc = spinTranslation q j.castSucc from congrFun ht j]

/-- Every actual Q operator sends the distinguished Hadamard state to the explicitly
specified two-point state. -/
theorem generatedOddSpinState_pauli (q : Q) :
    spinOperator q (generatedOddSpinState 0 1 0) =
      generatedOddSpinState (generatedOddSpinLow (spinTranslation q))
        (spinModulation q 11 + 1) (generatedOddSpinOutputSign q) := by
  ext t
  change qSign (spinPhase q t) *
    (if generatedOddSpinLow (t + spinTranslation q) = 0 then
      qSign (0 + 1 * (t + spinTranslation q) 11) else 0) = _
  simp only [spin_low_eq_iff]
  by_cases ht : generatedOddSpinLow t = generatedOddSpinLow (spinTranslation q)
  · simp only [ht, ite_true, zero_add, one_mul, Pi.add_apply, generatedOddSpinState]
    rw [← qSign_add]
    congr 1
    rw [spinPhase, spin_dot_low q t ht]
    dsimp [generatedOddSpinOutputSign]
    ring
  · simp only [generatedOddSpinState, ht, ite_false, mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
