/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecificLimits.Basic










open Filter Set

namespace StatMech.FrontierA


def QuantumIsingAlmostAdditive (u : Nat -> Real) (c : Real) : Prop :=
  ∀ m n, |u (m + n) - u m - u n| ≤ c

namespace QuantumIsingAlmostAdditive

variable {u : Nat -> Real} {c : Real}

theorem nonneg (h : QuantumIsingAlmostAdditive u c) : 0 ≤ c := by
  exact (abs_nonneg (u (0 + 0) - u 0 - u 0)).trans (h 0 0)

theorem lower (h : QuantumIsingAlmostAdditive u c) (m n : Nat) :
    u m + u n - c ≤ u (m + n) := by
  have := (abs_le.mp (h m n)).1
  linarith

theorem upper (h : QuantumIsingAlmostAdditive u c) (m n : Nat) :
    u (m + n) ≤ u m + u n + c := by
  have := (abs_le.mp (h m n)).2
  linarith

theorem shift_subadditive (h : QuantumIsingAlmostAdditive u c) :
    Subadditive (fun n => u n + c) := by
  intro m n
  have := h.upper m n
  linarith

theorem neg (h : QuantumIsingAlmostAdditive u c) :
    QuantumIsingAlmostAdditive (fun n => -u n) c := by
  intro m n
  have heq : -u (m + n) - -u m - -u n =
      -(u (m + n) - u m - u n) := by ring
  rw [heq, abs_neg]
  exact h m n

private theorem linear_lower (h : QuantumIsingAlmostAdditive u c) :
    ∀ n : Nat, 0 < n -> (n : Real) * (u 1 - c) ≤ u n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        simpa using sub_le_self (u 1) h.nonneg
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hind := ih hnpos
        have hadd := h.lower n 1
        norm_num only [Nat.cast_add, Nat.cast_one]
        linarith

theorem shift_bddBelow (h : QuantumIsingAlmostAdditive u c) :
    BddBelow (Set.range fun n => (u n + c) / n) := by
  refine ⟨min 0 (u 1 - c), ?_⟩
  rintro x ⟨n, rfl⟩
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · refine (min_le_right _ _).trans ?_
    rw [le_div_iff₀ (by exact_mod_cast hn)]
    calc
      (u 1 - c) * (n : Real) = (n : Real) * (u 1 - c) := by ring
      _ ≤ u n := linear_lower h n hn
      _ ≤ u n + c := le_add_of_nonneg_right h.nonneg



noncomputable def limit (h : QuantumIsingAlmostAdditive u c) : Real :=
  (h.shift_subadditive).lim


theorem tendsto_limit (h : QuantumIsingAlmostAdditive u c) :
    Tendsto (fun n => u n / n) atTop (nhds h.limit) := by
  have hshift := h.shift_subadditive.tendsto_lim h.shift_bddBelow
  have hc : Tendsto (fun n : Nat => c / n) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat c
  have hsub := hshift.sub hc
  convert hsub using 1
  · funext n
    ring
  · simp [limit]



theorem abs_limit_sub_div_le (h : QuantumIsingAlmostAdditive u c)
    {L : Nat} (hL : L ≠ 0) :
    |h.limit - u L / L| ≤ c / L := by
  let hplus := h.shift_subadditive
  have hbplus := h.shift_bddBelow
  have hupp : h.limit ≤ (u L + c) / L := by
    exact hplus.lim_le_div hbplus hL
  let hneg := h.neg
  have hnegLim : hneg.limit = -h.limit := by
    have hconv : Tendsto (fun n : Nat => (-u n) / n)
        atTop (nhds (-h.limit)) := by
      convert h.tendsto_limit.neg using 1
      funext n
      ring
    exact tendsto_nhds_unique hneg.tendsto_limit hconv
  have hlowRaw : hneg.limit ≤ ((-u L) + c) / L := by
    exact hneg.shift_subadditive.lim_le_div hneg.shift_bddBelow hL
  rw [hnegLim] at hlowRaw
  rw [abs_le]
  constructor
  · rw [add_div] at hlowRaw
    have hnegdiv : (-u L) / (L : Real) = -(u L / L) := by ring
    rw [hnegdiv] at hlowRaw
    linarith
  · rw [add_div] at hupp
    linarith

end QuantumIsingAlmostAdditive

end StatMech.FrontierA
