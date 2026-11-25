/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Linarith

/-!
# External balance of a countercurrent cascade

The difference between the liquid component flow and the oppositely directed vapour
component flow is unchanged across each stage. The boundary balance follows without
an equilibrium relation.
-/

namespace Domains.Chemistry.Separations.CountercurrentBalance

/-- In a nonempty chain of `N` countercurrent stages with positive carrier flows, the
component balances imply equality of the sum of the two entering component flows and
the sum of the two leaving ones. Stage `k + 1` is indexed by `k < N`. Neither the sign
of the carrier flows nor any equilibrium law is needed for the cancellation.

Lamm and Jarboe, *Chemical Engineering Separations: A Handbook for Students*, LibreTexts,
§1.4, Equation 9.1 gives the absorber operating line for constant solute-free carrier rates.
Subtracting the line at adjacent cuts gives the constant-carrier special case of the stage
balance assumed here. -/
public theorem external_component_balance (N : ℕ) (_hN : 0 < N)
    (L V x y : ℕ → ℝ) (_hL : ∀ k ≤ N, 0 < L k) (_hV : ∀ k ≤ N, 0 < V (k + 1))
    (hstage : ∀ k < N, L k * x k + V (k + 2) * y (k + 2) =
      L (k + 1) * x (k + 1) + V (k + 1) * y (k + 1)) :
    L 0 * x 0 + V (N + 1) * y (N + 1) = L N * x N + V 1 * y 1 := by
  let net (k : ℕ) : ℝ := L k * x k - V (k + 1) * y (k + 1)
  have hstep (k : ℕ) (hk : k < N) : net k = net (k + 1) := by
    dsimp only [net]
    linarith only [hstage k hk]
  have hnet (k : ℕ) : k ≤ N → net k = net 0 := by
    induction k with
    | zero => intro; rfl
    | succ k ih =>
      intro hk
      exact (hstep k (Nat.lt_of_succ_le hk)).symm.trans (ih (Nat.le_of_succ_le hk))
  have h := hnet N le_rfl
  dsimp only [net] at h
  linarith only [h]

end Domains.Chemistry.Separations.CountercurrentBalance
