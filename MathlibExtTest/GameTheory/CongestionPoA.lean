/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.CongestionPoA

/-- Boundary check: the optimal profile itself, when it is a Nash
equilibrium, satisfies the bound with room to spare. -/
example {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (a b : R → ℝ) (ha : ∀ r, 0 ≤ a r) (hb : ∀ r, 0 ≤ b r) (opt : Fin n → R)
    (hNash : ∀ (i : Fin n) (r : R),
      a (opt i) * (loadOf opt (opt i) : ℝ) + b (opt i) ≤
        a r * ((loadOf (Function.update opt i r) r : ℝ)) + b r) :
    socialCost a b opt ≤ (5 / 2) * socialCost a b opt :=
  congestion_poa a b ha hb opt opt hNash

/-- Load computation: with one player, their resource has load `1`. -/
example (r : Fin 2) : loadOf (fun _ : Fin 1 => r) r = 1 := by
  simp [loadOf]
