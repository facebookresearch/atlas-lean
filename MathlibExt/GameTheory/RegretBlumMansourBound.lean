/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.RegretBlumMansour

set_option autoImplicit false

@[expose] public section

/-!
# Blum-Mansour swap-regret bound

Instantiation of the Blum-Mansour decomposition
(`swapRegret_le_sum_externalRegret_scaled`) with an abstract per-copy
external-regret bound: if every copy's external regret against its
scaled loss sequence is at most `R`, the master's swap regret is at
most `|K| * R`, and the same bound holds in the averaged
(`1 / T`-scaled) form of the source theorem. Combined with stationary
existence (`exists_isStationaryPlay`), this is the quantitative content
of the black-box reduction from swap regret to external regret.

## References

* A. Blum and Y. Mansour, "From external to internal regret", *Journal of
  Machine Learning Research* 8 (2007), 1307-1324.
* T. Roughgarden, CS364A Lecture 18, "From External Regret to Swap Regret
  and the Minimax Theorem" (Stanford, 2013), Theorem 2.1 and the summed
  inequality (6) of its proof.
-/

namespace MathlibExt.GameTheory.Regret

open scoped BigOperators

variable {K : Type*} [Fintype K] [DecidableEq K] [Nonempty K]
variable {T : ℕ}

/-- **Blum–Mansour bound, uniform form.** If every copy's external regret
against its scaled loss sequence is at most `R`, then the master's swap
regret is at most `|K| * R`. -/
theorem swapRegret_le_card_mul_of_externalRegret_le (q : Fin T → K → K → ℝ)
    (p loss : Fin T → K → ℝ) (hp : IsStationaryPlay q p) (R : ℝ)
    (hR : ∀ j, externalRegret (fun t => q t j) (scaledLoss p loss j) ≤ R) :
    swapRegret p loss ≤ (Fintype.card K : ℝ) * R := by
  calc swapRegret p loss
      ≤ ∑ j, externalRegret (fun t => q t j) (scaledLoss p loss j) :=
        swapRegret_le_sum_externalRegret_scaled q p loss hp
    _ ≤ ∑ _j : K, R := Finset.sum_le_sum fun j _ => hR j
    _ = (Fintype.card K : ℝ) * R := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Blum–Mansour bound, averaged form.** The `1 / T`-scaled form of the
source theorem: if every copy's average external regret against its
scaled loss sequence is at most `R`, then the master's average swap
regret is at most `|K| * R`. -/
theorem swapRegret_div_le_card_mul_of_averageRegret_le [NeZero T]
    (q : Fin T → K → K → ℝ) (p loss : Fin T → K → ℝ)
    (hp : IsStationaryPlay q p) (R : ℝ)
    (hR : ∀ j, averageRegret (fun t => q t j) (scaledLoss p loss j) ≤ R) :
    swapRegret p loss / (T : ℝ) ≤ (Fintype.card K : ℝ) * R := by
  have hT : (0 : ℝ) < (T : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T)
  have hR' : ∀ j, externalRegret (fun t => q t j) (scaledLoss p loss j)
      ≤ R * (T : ℝ) := by
    intro j
    have h := hR j
    rw [averageRegret, div_le_iff₀ hT] at h
    exact h
  have h1 := swapRegret_le_card_mul_of_externalRegret_le q p loss hp
    (R * (T : ℝ)) hR'
  rw [div_le_iff₀ hT]
  calc swapRegret p loss ≤ (Fintype.card K : ℝ) * (R * (T : ℝ)) := h1
    _ = (Fintype.card K : ℝ) * R * (T : ℝ) := by ring

/-- **Black-box reduction, existence form.** Whenever every copy plays a
distribution at every time, some stationary master play exists, and any
uniform per-copy external-regret bound `R` for that play bounds its swap
regret by `|K| * R`. -/
theorem exists_stationaryPlay_swapRegret_le_card_mul
    (q : Fin T → K → K → ℝ) (loss : Fin T → K → ℝ) (R : ℝ)
    (hq : ∀ t j, IsSimplex (q t j)) :
    ∃ p : Fin T → K → ℝ, IsStationaryPlay q p ∧
      ((∀ j, externalRegret (fun t => q t j) (scaledLoss p loss j) ≤ R) →
        swapRegret p loss ≤ (Fintype.card K : ℝ) * R) := by
  obtain ⟨p, hp⟩ := exists_isStationaryPlay q hq
  exact ⟨p, hp, fun hR =>
    swapRegret_le_card_mul_of_externalRegret_le q p loss hp R hR⟩

end MathlibExt.GameTheory.Regret
