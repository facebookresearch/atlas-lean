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

-- `apOfModel` is the Frobenius trace of the reduction over the finite field
-- `ZMod p`, taken from the shared point-count API.
example (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] :
    W.apOfModel p = (W.reductionMod p).toAffine.frobeniusTrace :=
  rfl

-- The point count behind `apOfModel` includes the point at infinity:
-- `#W(𝔽_p) = p + 1 - a_p`.
example (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] :
    (Nat.card (W.reductionMod p).toAffine.Point : ℤ) = p + 1 - W.apOfModel p := by
  rw [show W.apOfModel p = (W.reductionMod p).toAffine.frobeniusTrace from rfl,
    (W.reductionMod p).toAffine.natCard_point_eq_natCard_add_one_sub_frobeniusTrace,
    Nat.card_zmod]

-- A modular model gives the trace at a good prime outside the level, with the
-- primality instance supplied by the caller.
example {W : WeierstrassCurve ℤ} {N : ℕ} (h : W.IsModularModelOfLevel N)
    (p : ℕ) [hp : Fact p.Prime] (hgood : W.IsGoodPrimeFor p) (hpN : ¬ p ∣ N) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform ∧
      ModularFormClass.qCoeff f p = (W.apOfModel p : ℂ) := by
  obtain ⟨f, hf, hcoeff⟩ := h
  exact ⟨f, hf, hcoeff p hp.out hgood hpN⟩
