/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all MathlibExt.GameTheory.ExactSlowNimRemoteness

namespace MetaMathlibExt.exactSlowNimBasicValue_of_supports_basicB

-- At k = 1 the two single-token piles form a type (B) vector of value two.
-- A legal move empties a pile.
example : exactSlowNimBasicValue 1 ![0, 1] = 1 := by
  let x : Fin 2 → ℕ := ![1, 1]
  have hb : IsExactSlowNimBasicB 1 2 x := by
    unfold IsExactSlowNimBasicB
    decide
  have hx : exactSlowNimBasicValue 1 x = 2 := by
    classical
    unfold exactSlowNimBasicValue
    rw [show ∑ i, x i = 2 by decide]
    exact Nat.findGreatest_eq ⟨x, le_rfl, Or.inr (Or.inr hb)⟩
  have h := (exactSlowNimBasicValue_of_supports_basicB (by decide : 0 < 1) x x le_rfl
    (hx.symm ▸ hb)).2 ![0, 1] (by decide)
  simpa [hx] using h

-- For three piles of size three, the move playing the outer piles drops the value from four
-- to three. The type (A1) witness beneath the resulting position has one even pile.
example : exactSlowNimBasicValue 2 ![2, 3, 2] = 3 := by
  let x : Fin 3 → ℕ := ![3, 3, 3]
  have hb : IsExactSlowNimBasicB 2 4 x := by
    unfold IsExactSlowNimBasicB
    decide
  have hsum : ∑ i, x i = 9 := by decide
  have hx : exactSlowNimBasicValue 2 x = 4 := by
    classical
    unfold exactSlowNimBasicValue
    rw [hsum, Nat.findGreatest_eq_iff]
    refine ⟨by decide, fun _ => ⟨x, le_rfl, Or.inr (Or.inr hb)⟩, ?_⟩
    rintro n hn _ ⟨y, hyx, ha | ha | hB⟩ <;>
      have hle := (Finset.sum_le_sum fun i _ => hyx i).trans_eq hsum
    · have := ha.1
      omega
    · have := ha.1
      omega
    · have := hB.1
      omega
  have h := (exactSlowNimBasicValue_of_supports_basicB (by decide : 0 < 2) x x le_rfl
    (hx.symm ▸ hb)).2 ![2, 3, 2] (by decide)
  simpa [hx] using h

end MetaMathlibExt.exactSlowNimBasicValue_of_supports_basicB

namespace MetaMathlibExt.exactSlowNimBasicValue_eq_smithRemoteness

-- The type (B) vector (3, 3, 3) has basic-vector value four, so its Smith remoteness in NIM(3, 2)
-- is four, the M-rule length that `exactSlowNimMRuleLength_three_three_three` computes.
example : SpragueGrundy.smithRemoteness (slowANimGame 3 {2}) ![3, 3, 3] =
    exactSlowNimMRuleLength 2 ![3, 3, 3] := by
  let x : Fin 3 → ℕ := ![3, 3, 3]
  have hb : IsExactSlowNimBasicB 2 4 x := by
    unfold IsExactSlowNimBasicB
    decide
  have hsum : ∑ i, x i = 9 := by decide
  have hx : exactSlowNimBasicValue 2 x = 4 := by
    classical
    unfold exactSlowNimBasicValue
    rw [hsum, Nat.findGreatest_eq_iff]
    refine ⟨by decide, fun _ => ⟨x, le_rfl, Or.inr (Or.inr hb)⟩, ?_⟩
    rintro n hn _ ⟨y, hyx, ha | ha | hB⟩ <;>
      have hle := (Finset.sum_le_sum fun i _ => hyx i).trans_eq hsum
    · have := ha.1
      omega
    · have := ha.1
      omega
    · have := hB.1
      omega
  rw [exactSlowNimMRuleLength_three_three_three]
  exact (exactSlowNimBasicValue_eq_smithRemoteness (k := 2) (by decide) x).symm.trans hx

end MetaMathlibExt.exactSlowNimBasicValue_eq_smithRemoteness

namespace MetaMathlibExt.exactSlowNim_critical_of_even

private theorem remoteness_of_singleton_moves (G : SpragueGrundy.ImpartialGame) (p q : G.Pos)
    (h : G.moves p = {q}) :
    SpragueGrundy.smithRemoteness G p = 1 + SpragueGrundy.smithRemoteness G q := by
  classical
  rw [SpragueGrundy.smithRemoteness_eq G p, h]
  simp only [Finset.image_singleton]
  split_ifs with he hv
  · have hmem := Finset.min'_mem _ he
    rw [Finset.mem_singleton.mp (Finset.mem_filter.mp hmem).1]
  · simp
  · exact (hv (Finset.singleton_nonempty _)).elim

-- The empty pile is last. The M-move must leave it, and the sole move is critical.
example : exactSlowNimMRuleMove ![2, 0] = ![1, 0] ∧
    IsExactSlowNimCritical 1 1 ![1, 0] := by
  let G := slowANimGame 2 {1}
  have h0 : SpragueGrundy.smithRemoteness G ![0, 0] = 0 :=
    SpragueGrundy.smithRemoteness_of_moves_eq_empty G _ (by
      change slowANimMoves {1} ![0, 0] = ∅
      decide)
  have h1 : SpragueGrundy.smithRemoteness G ![1, 0] = 1 := by
    have h : slowANimMoves {1} ![1, 0] = {![0, 0]} := by decide
    rw [remoteness_of_singleton_moves G ![1, 0] ![0, 0] h, h0]
  have h2 : SpragueGrundy.smithRemoteness G ![2, 0] = 2 := by
    have h : slowANimMoves {1} ![2, 0] = {![1, 0]} := by decide
    rw [remoteness_of_singleton_moves G ![2, 0] ![1, 0] h, h1]
  have hx : IsExactSlowNimCritical 1 2 ![2, 0] := by
    refine ⟨h2, ?_⟩
    intro y hy
    have hfirst : y 0 ≤ 2 := hy.le 0
    have hlast : y 1 = 0 := Nat.eq_zero_of_le_zero (hy.le 1)
    have same_piles (a : ℕ) (ha : y 0 = a) : y = ![a, 0] := by
      rw [funext_iff, Fin.forall_fin_two]
      exact ⟨ha, hlast⟩
    have hlt : y 0 < 2 := lt_of_le_of_ne hfirst (fun h => hy.ne (same_piles 2 h))
    obtain h | h : y 0 = 0 ∨ y 0 = 1 := by omega
    · rw [same_piles 0 h]
      change SpragueGrundy.smithRemoteness G ![0, 0] ≠ 2
      simp [h0]
    · rw [same_piles 1 h]
      change SpragueGrundy.smithRemoteness G ![1, 0] ≠ 2
      simp [h1]
  have hm := (exactSlowNim_critical_of_even (k := 1) (m := 2)
    (by decide) (by decide) (by decide) ![2, 0] hx).2 (by decide)
  have hmove : exactSlowNimMRuleMove ![2, 0] = ![1, 0] := by decide
  exact ⟨hmove, hmove ▸ hm.2.2.2⟩

end MetaMathlibExt.exactSlowNim_critical_of_even

namespace MetaMathlibExt

open exactSlowNim_critical_of_even (critical_of_a1)

-- At m = 1 the legal M-move goes to the empty position.
example : IsExactSlowNimCritical 2 0 (exactSlowNimMRuleMove ![1, 0, 1]) := by
  have hx : IsExactSlowNimBasicA1 2 1 ![1, 0, 1] := by
    refine ⟨by decide, by decide, by decide, 1, by decide, ?_⟩
    rw [Fin.forall_fin_succ, Fin.forall_fin_two]
    decide
  obtain ⟨i, -, -, hmove, hcrit, hM⟩ := exactSlowNim_critical_of_odd (by decide) (by decide)
    ![1, 0, 1] (critical_of_a1 (by decide) hx)
  rw [hM]
  exact (hcrit _ hmove).2 rfl

-- With three legal options, the critical one keeps the even pile rather than the largest pile.
example : IsExactSlowNimCritical 2 2 ![2, 0, 2] ∧ ¬ IsExactSlowNimCritical 2 2 ![1, 0, 3] := by
  have hx : IsExactSlowNimBasicA1 2 3 ![2, 1, 3] := by
    refine ⟨by decide, by decide, by decide, 0, by decide, ?_⟩
    rw [Fin.forall_fin_succ, Fin.forall_fin_two]
    decide
  obtain ⟨i, -, hu, -, hcrit, -⟩ := exactSlowNim_critical_of_odd (by decide) (by decide)
    ![2, 1, 3] (critical_of_a1 (by decide) hx)
  have hi : i = 0 := (hu 0 (by decide)).symm
  subst i
  exact ⟨(hcrit _ (by decide)).2 (by decide), fun h =>
    (show (![1, 0, 3] : Fin 3 → ℕ) ≠ slowANimAfter ![2, 1, 3] (Finset.univ.erase 0) by
      decide) ((hcrit _ (by decide)).1 h)⟩

end MetaMathlibExt
