/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Mathlib
import Code.Onsager.ShermanPropIV

namespace StatMech.Onsager

open BigOperators




theorem wpar_odd_ne_zero {m : ℤ} (h : Odd m) : m ≠ 0 := by
  rintro rfl
  rcases h with ⟨k, hk⟩
  omega







theorem wpar_oddWinding_forces_winds (n : ℕ) (d : Fin (n + 1) → Fin 4)
    (m : ℤ) (hm : (∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) = 4 * m)
    (hodd : Odd m) :
    (∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) ≠ 0 := by
  rw [hm]
  have := wpar_odd_ne_zero hodd
  simpa using this




def wpar_dStraight : Fin 3 → Fin 4 := ![0, 0, 0]



def wpar_siteStraight : Fin 3 → ZMod 2 × ZMod 2 := ![((0 : ZMod 2), (0 : ZMod 2)), (1, 0), (0, 0)]


theorem wpar_straight_step :
    ∀ k : Fin 2, wpar_siteStraight k.succ
      = ons_dirStep 2 (wpar_dStraight k.castSucc) (wpar_siteStraight k.castSucc) := by
  decide


theorem wpar_straight_nu :
    ∀ k : Fin 2, wpar_dStraight k.succ ≠ wpar_dStraight k.castSucc + 2 := by
  decide


theorem wpar_straight_closeDir : wpar_dStraight (Fin.last 2) = wpar_dStraight 0 := by
  decide


theorem wpar_straight_closeSite : wpar_siteStraight (Fin.last 2) = wpar_siteStraight 0 := by
  decide


theorem wpar_straight_selfAvoiding : ons_SelfAvoiding wpar_siteStraight := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> revert hab <;> decide


theorem wpar_straight_turnSum :
    (∑ k : Fin 2, ons_turnPow (wpar_dStraight k.castSucc) (wpar_dStraight k.succ)) = 4 * 0 := by
  decide













theorem wpar_umlaufsatzKW_false : ¬ ons_DiscreteUmlaufsatzKW := by
  intro hU
  have hodd : Odd (0 : ℤ) :=
    hU 2 2 wpar_dStraight wpar_siteStraight
      wpar_straight_step wpar_straight_nu wpar_straight_closeDir wpar_straight_closeSite
      wpar_straight_selfAvoiding 0 wpar_straight_turnSum
  rcases hodd with ⟨k, hk⟩
  omega
















































end StatMech.Onsager
