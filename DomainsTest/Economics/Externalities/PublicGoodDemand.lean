/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Economics.Externalities.PublicGoodDemand

/-! Boundary and uniqueness tests for public-good demand. -/

open Set MathlibExt.Economics.PublicGood

variable {v d : ℝ → ℝ} (h : CommonBenefit v d)

-- At the right marginal price at zero there cannot be a positive marginal-price root.
example {G : ℝ} (hG : 0 < G) : d G ≠ d 0 :=
  (h.strictAntiOn_marginal (show (0 : ℝ) ∈ Ici 0 from le_rfl) hG.le hG).ne

-- The larger of two admissible prices has a strictly smaller, positive demand total.
example {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < d 0) :
    ∃ A B : ℝ, 0 < A ∧ A < B ∧ d A = q ∧ d B = p := by
  obtain ⟨A, hA, hqA, _⟩ := h.exists_peak (hp.trans hpq) hq
  obtain ⟨B, hB, hpB, _⟩ := h.exists_peak hp (hpq.trans hq)
  refine ⟨A, B, hA, ?_, hqA, hpB⟩
  by_contra! hle
  have := h.strictAntiOn_marginal.antitoneOn hB.le hA.le hle
  linarith
