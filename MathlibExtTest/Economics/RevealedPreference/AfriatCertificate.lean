/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.RevealedPreference.AfriatCertificate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

@[expose] public section

open MathlibExt.Economics.RevealedPreference

namespace MathlibExtTest.Economics.RevealedPreference.AfriatCertificate

/-- Two goods, two observations at prices `(1, 2)` and `(2, 1)` choosing `(2, 0)` and `(0, 2)`:
expenditures `p⁰·x⁰ = 2, p⁰·x¹ = 4, p¹·x¹ = 2, p¹·x⁰ = 4`, so neither bundle was affordable at
the other's prices. -/
def swap : DemandData (Fin 2) (Fin 2) where
  price := ![![1, 2], ![2, 1]]
  bundle := ![![2, 0], ![0, 2]]

/-- `U = (0, 0)`, `λ = (1, 1)` satisfies Afriat's inequalities for `swap`. -/
theorem swap_certificate : swap.IsAfriatCertificate ![0, 0] ![1, 1] := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i <;> simp
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [swap, dotProduct, Fin.sum_univ_two]

theorem swap_rationalizes : swap.Rationalizes (swap.afriatUtility ![0, 0] ![1, 1]) := by
  have hp : ∀ i g, 0 < swap.price i g := by
    intro i g
    fin_cases i <;> fin_cases g <;> simp [swap]
  obtain ⟨_, _, _, _, _, hrat⟩ :=
    DemandData.IsAfriatCertificate.afriatUtility_spec hp swap_certificate
  exact hrat

/-- The Afriat utility of `swap` at the origin: `min (0 + 1·(-2), 0 + 1·(-2)) = -2`. -/
theorem swap_afriatUtility_zero : swap.afriatUtility ![0, 0] ![1, 1] 0 = -2 := by
  have h0 : ![0, 0] (0 : Fin 2)
      + ![1, 1] (0 : Fin 2) * (swap.price 0 ⬝ᵥ ((0 : Fin 2 → ℝ) - swap.bundle 0)) = -2 := by
    simp [swap, dotProduct, Fin.sum_univ_two]
  unfold DemandData.afriatUtility
  apply le_antisymm
  · calc Finset.univ.inf' Finset.univ_nonempty
          (fun i => ![0, 0] i + ![1, 1] i * (swap.price i ⬝ᵥ ((0 : Fin 2 → ℝ) - swap.bundle i)))
          ≤ ![0, 0] (0 : Fin 2)
            + ![1, 1] (0 : Fin 2) * (swap.price 0 ⬝ᵥ ((0 : Fin 2 → ℝ) - swap.bundle 0)) :=
          Finset.inf'_le _ (Finset.mem_univ 0)
      _ = -2 := h0
  · apply Finset.le_inf'
    intro i _
    fin_cases i <;> simp [swap, dotProduct, Fin.sum_univ_two]

/-- A nonpositive multiplier is not a certificate. -/
theorem swap_not_certificate_zero_lam : ¬ swap.IsAfriatCertificate ![0, 0] ![0, 1] := by
  intro h
  have h0 := h.1 0
  simp at h0

end MathlibExtTest.Economics.RevealedPreference.AfriatCertificate
