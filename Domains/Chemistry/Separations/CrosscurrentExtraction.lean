/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Fixed-volume crosscurrent extraction

Each stage contacts the same raffinate volume with a fresh, solute-free solvent
volume. Under a stipulated linear equilibrium law, solving the stage balance
and iterating gives the remaining raffinate amount.
-/

namespace Domains.Chemistry.Separations.CrosscurrentExtraction

/-- In the fixed-volume crosscurrent model with positive volumes and coefficient, a stage
retains the fraction `(1 + K * (Vs / Vr))⁻¹` of the entering amount. The same factor applies
at each of the `N` contacts. The amount formula includes `N = 0` and zero initial solute;
the fraction of the initial amount is asserted only for positive initial solute.

David Harvey, *Analytical Chemistry 2.1*, §7.7, "Liquid-Liquid Extractions,"
Eqs. (7.6) and (7.7), gives the corresponding one-step and repeated retention
fractions. The fixed-volume linear law here is a hypothesis, not a general
ternary-phase extraction model. -/
public theorem crosscurrent_amounts (N : ℕ) (Vr Vs K : ℝ)
    (hVr : 0 < Vr) (hVs : 0 < Vs) (hK : 0 < K) (q cr cs : ℕ → ℝ)
    (heq : ∀ k < N, cs k = K * cr k)
    (hin : ∀ k < N, q k = Vr * cr k + Vs * cs k)
    (hout : ∀ k < N, q (k + 1) = Vr * cr k) :
    let R := Vs / Vr
    0 < R ∧ (∀ k < N, q (k + 1) = q k / (1 + K * R)) ∧
    (∀ k ≤ N, q k = q 0 * ((1 + K * R)⁻¹) ^ k) ∧
    (0 < q 0 → q N / q 0 = ((1 + K * R)⁻¹) ^ N) ∧
    (q 0 = 0 → q N = 0) := by
  let R := Vs / Vr
  have hR : 0 < R := div_pos hVs hVr
  have hden : 0 < 1 + K * R := add_pos zero_lt_one (mul_pos hK hR)
  have hscale : Vr * (1 + K * R) = Vr + K * Vs := by
    dsimp only [R]
    field_simp [hVr.ne']
  have hstep (k : ℕ) (hk : k < N) : q (k + 1) = q k / (1 + K * R) := by
    apply (eq_div_iff hden.ne').2
    rw [hout k hk, hin k hk, heq k hk]
    calc
      Vr * cr k * (1 + K * R) = (Vr * (1 + K * R)) * cr k := by ring
      _ = Vr * cr k + Vs * (K * cr k) := by rw [hscale]; ring
  have hamount (k : ℕ) : k ≤ N → q k = q 0 * ((1 + K * R)⁻¹) ^ k := by
    induction k with
    | zero => intro; simp
    | succ k ih =>
      intro hk
      rw [hstep k (Nat.lt_of_succ_le hk), ih (Nat.le_of_succ_le hk), div_eq_mul_inv, pow_succ,
        mul_assoc]
  refine ⟨hR, hstep, hamount, ?_, ?_⟩
  · intro hq
    rw [hamount N le_rfl, mul_comm (q 0), mul_div_cancel_right₀ _ hq.ne']
  · intro hq
    rw [hamount N le_rfl, hq, zero_mul]

end Domains.Chemistry.Separations.CrosscurrentExtraction
