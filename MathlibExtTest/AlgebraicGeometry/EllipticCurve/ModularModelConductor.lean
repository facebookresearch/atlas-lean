/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ModularModelConductor

@[expose] public section

-- `exactSource` consumer with the original binders.
example {W : WeierstrassCurve ℤ}
    (h : W.IsModularModelOfExactConductorLevel) :
    W.IsModularModelOfConductorLevel :=
  h.isModularModelOfConductorLevel

-- The exact level can be recovered, with its squarefreeness, from the
-- exact-conductor hypothesis.
example {W : WeierstrassCurve ℤ}
    (h : W.IsModularModelOfExactConductorLevel) :
    ∃ N : ℕ, 0 < N ∧ Squarefree N ∧ W.IsModularModelOfLevel N := by
  obtain ⟨N, hN, hsq, -, hmod⟩ := h
  exact ⟨N, hN, hsq, hmod⟩

-- Boundary: conductor level alone does not record squarefreeness or the
-- converse divisibility; the statement below is the exact content used.
example {W : WeierstrassCurve ℤ}
    (h : W.IsModularModelOfConductorLevel) :
    ∃ N : ℕ, 0 < N ∧ W.IsModularModelOfLevel N ∧
      ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ W.Δ → ℓ ∣ N :=
  h

example (W : WeierstrassCurve ℤ) (p : ℕ) :
    W.apOfModel p = (W.reductionMod p).traceOfFrobenius :=
  W.apOfModel_def p
