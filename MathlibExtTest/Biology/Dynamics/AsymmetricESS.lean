/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.AsymmetricESS

/-! Tests for `MathlibExt.Biology.Dynamics.AsymmetricESS`:

* **non-vacuity**: in the asymmetric coordination game `A = B = !![2, 0; 0, 1]` with role
  probability `1/2`, the pure pair `(0, 0)` is a strict Nash equilibrium and an evolutionarily
  stable behavior strategy, both checked directly from the definitions (not through Selten's
  theorem); the main theorems then give the ESS of the symmetrized matrix game and rule out a
  completely mixed ESS;
* **mixed equilibria are not ESS**: in matching pennies the completely mixed Nash equilibrium
  `((1/2, 1/2), (1/2, 1/2))` is not an evolutionarily stable behavior strategy, by an explicit
  neutral mutant computed from the definitions;
* **boundary `ρ = 1`**: for `A = B = !![1, 0; 0, 0]`, the pure pair `(0, 0)` is a strict Nash
  equilibrium, but with role probability `ρ = 1` it is not an evolutionarily stable behavior
  strategy (a mutant changing only its role-II behavior is neutral), so the hypothesis `ρ < 1`
  of `isRoleESS_iff_isStrictNash` cannot be dropped. -/

open Matrix

namespace MathlibExtTest.Biology.Dynamics.AsymmetricESS

open MathlibExt.Biology.Dynamics.AsymmetricESS
open MathlibExt.Biology.Dynamics.Replicator (IsESS)

/-! ### Two-strategy helpers -/

/-- A mixed strategy on two strategies with all weight on strategy `0` is the pure strategy `0`. -/
theorem eq_single_zero {p : Fin 2 → ℝ} (hp : IsMixed p) (h0 : p 0 = 1) : p = Pi.single 0 1 := by
  have h := hp.2
  simp only [Fin.sum_univ_two] at h
  funext j
  fin_cases j
  · simp [h0]
  · simp only [Fin.mk_one, Fin.isValue, ne_eq, one_ne_zero, not_false_eq_true,
      Pi.single_eq_of_ne]
    linarith

/-- A mixed strategy on two strategies other than the pure strategy `0` puts weight `< 1` on
strategy `0`. -/
theorem lt_one_of_ne {p : Fin 2 → ℝ} (hp : IsMixed p) (hne : p ≠ Pi.single 0 1) : p 0 < 1 := by
  have h := hp.2
  have h1 := hp.1 1
  simp only [Fin.sum_univ_two] at h
  exact lt_of_le_of_ne (by linarith) fun h0 => hne (eq_single_zero hp h0)

theorem half_isMixed : IsMixed (![1 / 2, 1 / 2] : Fin 2 → ℝ) :=
  ⟨fun i => by fin_cases i <;> norm_num, by norm_num [Fin.sum_univ_two]⟩

/-! ### Non-vacuity: an asymmetric coordination game -/

/-- Coordination payoffs: matching on strategy `0` pays `2`, matching on `1` pays `1`. -/
def coord : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, 1]

theorem coord_payoff (p : Fin 2 → ℝ) : p ⬝ᵥ coord *ᵥ Pi.single 0 1 = 2 * p 0 := by
  simp [coord, dotProduct, mulVec, Fin.sum_univ_two]
  ring

/-- The pure pair `(0, 0)` is a strict Nash equilibrium of `(coord, coord)`, directly from the
definition. -/
theorem coord_isStrictNash : IsStrictNash coord coord (Pi.single 0 1) (Pi.single 0 1) := by
  refine ⟨⟨isMixed_single 0, isMixed_single 0⟩, fun p' hp' hne => ?_, fun q' hq' hne => ?_⟩
  · rw [coord_payoff, coord_payoff]
    have := lt_one_of_ne hp' hne
    simp only [Pi.single_eq_same]
    linarith
  · rw [coord_payoff, coord_payoff]
    have := lt_one_of_ne hq' hne
    simp only [Pi.single_eq_same]
    linarith

/-- The pure pair `(0, 0)` is an evolutionarily stable behavior strategy of the coordination role
game with `ρ = 1/2`, directly from the definition: every other behavior strategy does strictly
worse against it. -/
theorem coord_isRoleESS :
    IsRoleESS (1 / 2) coord coord (Pi.single 0 1, Pi.single 0 1) := by
  refine ⟨⟨isMixed_single 0, isMixed_single 0⟩, fun t ht1 ht2 hne => Or.inl ?_⟩
  simp only [rolePayoff, coord_payoff, Pi.single_eq_same]
  have h1 := ht1.2
  have h2 := ht2.2
  have h10 := ht1.1 1
  have h20 := ht2.1 1
  simp only [Fin.sum_univ_two] at h1 h2
  by_cases ht : t.1 = Pi.single 0 1
  · have hlt := lt_one_of_ne ht2 fun h => hne (Prod.ext ht h)
    linarith
  · have hlt := lt_one_of_ne ht1 ht
    linarith

/-- Selten's theorem recovers the strict Nash property from the directly checked ESS. -/
example : IsStrictNash coord coord (Pi.single 0 1) (Pi.single 0 1) :=
  (isRoleESS_iff_isStrictNash (by norm_num) (by norm_num)).1 coord_isRoleESS

/-- The ESS of the coordination role game is not completely mixed in role I. -/
example : ¬ ∀ i, 0 < (Pi.single 0 1 : Fin 2 → ℝ) i :=
  coord_isRoleESS.not_pos_left (by norm_num) (by norm_num)

/-- The point mass at the pure pair `(0, 0)` is an ESS, in the sense of `Replicator.IsESS`, of the
symmetrized coordination game. -/
example : IsESS (symmetrize (1 / 2) coord coord) (Pi.single (0, 0) 1) :=
  (isESS_symmetrize_iff (by norm_num) (by norm_num) _).2 ⟨0, 0, rfl, coord_isStrictNash⟩

/-- A completely mixed strategy on `Fin 2 × Fin 2` is not an ESS of the symmetrized coordination
game. -/
example : ¬ IsESS (symmetrize (1 / 2) coord coord) (fun _ => 1 / 4) := by
  rw [isESS_symmetrize_iff (by norm_num) (by norm_num)]
  rintro ⟨i, k, h, -⟩
  have := congrFun h (i, k)
  norm_num at this

/-! ### Mixed equilibria are not ESS: matching pennies -/

/-- Role I wants to match. -/
def pennyA : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; -1, 1]

/-- Role II wants to mismatch. -/
def pennyB : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 1; 1, -1]

/-- The completely mixed pair `((1/2, 1/2), (1/2, 1/2))` is not an evolutionarily stable behavior
strategy of matching pennies: the mutant playing pure `0` in role I does equally well against the
resident and against itself. -/
theorem penny_not_isRoleESS (ρ : ℝ) :
    ¬ IsRoleESS ρ pennyA pennyB (![1 / 2, 1 / 2], ![1 / 2, 1 / 2]) := by
  intro h
  have hne : ((Pi.single 0 1, ![1 / 2, 1 / 2]) : (Fin 2 → ℝ) × (Fin 2 → ℝ)) ≠
      (![1 / 2, 1 / 2], ![1 / 2, 1 / 2]) := fun he => by
    have := congrFun (congrArg Prod.fst he) 0
    norm_num at this
  have := h.2 _ (isMixed_single 0) half_isMixed hne
  norm_num [rolePayoff, pennyA, pennyB, dotProduct, mulVec, Fin.sum_univ_two] at this

/-! ### Boundary: role probability `ρ = 1` -/

/-- Strategy `0` is the unique best reply to strategy `0`, paying `1`. -/
def unit00 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

theorem unit00_payoff (p : Fin 2 → ℝ) : p ⬝ᵥ unit00 *ᵥ Pi.single 0 1 = p 0 := by
  simp [unit00, dotProduct, mulVec, Fin.sum_univ_two]

/-- `(0, 0)` is a strict Nash equilibrium of `(unit00, unit00)`, directly from the definition. -/
theorem unit00_isStrictNash : IsStrictNash unit00 unit00 (Pi.single 0 1) (Pi.single 0 1) := by
  refine ⟨⟨isMixed_single 0, isMixed_single 0⟩, fun p' hp' hne => ?_, fun q' hq' hne => ?_⟩
  · rw [unit00_payoff, unit00_payoff, Pi.single_eq_same]
    exact lt_one_of_ne hp' hne
  · rw [unit00_payoff, unit00_payoff, Pi.single_eq_same]
    exact lt_one_of_ne hq' hne

/-- With `ρ = 1` the strict Nash equilibrium `(0, 0)` is **not** an evolutionarily stable
behavior strategy: the mutant that plays `1` in role II, which is never used, does exactly as well
as the resident. So `ρ < 1` is needed in `isRoleESS_iff_isStrictNash`. -/
theorem unit00_not_isRoleESS_one :
    ¬ IsRoleESS 1 unit00 unit00 (Pi.single 0 1, Pi.single 0 1) := by
  intro h
  have hne : ((Pi.single 0 1, Pi.single 1 1) : (Fin 2 → ℝ) × (Fin 2 → ℝ)) ≠
      (Pi.single 0 1, Pi.single 0 1) := fun he => by
    have := congrFun (congrArg Prod.snd he) 1
    simp at this
  have := h.2 _ (isMixed_single 0) (isMixed_single 1) hne
  simp [rolePayoff, unit00, dotProduct, mulVec, Fin.sum_univ_two] at this

end MathlibExtTest.Biology.Dynamics.AsymmetricESS
