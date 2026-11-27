/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.BranchNearRoot

@[expose] public section

open Polynomial

-- Exact-source consumer, with the original binders.
private theorem exactSource {n w : ℕ} (F : Polynomial (Polynomial ℂ)) (hF : F.natDegree ≤ n)
    (hwt : ∀ k j : ℕ, w * (n - k) < j → (F.coeff k).coeff j = 0) (c : ℂ) (hc : c ≠ 0)
    (hlead : F.coeff n = C c) (P : Fin n → Polynomial ℂ)
    (hP : ∀ i, (P i).natDegree ≤ w)
    (hPinj : Function.Injective fun i => (P i).coeff w)
    (hR : ∀ k j : ℕ, w * (n - k) ≤ j + w →
      ((F - C (C c) * ∏ i, (X - C (P i))).coeff k).coeff j = 0) :
    ∃ C₀ T : ℝ, 0 < C₀ ∧ ∀ t : ℂ, T ≤ ‖t‖ → ∀ x : ℂ,
      (F.map (Polynomial.evalRingHom t)).IsRoot x →
      ∃ i, ‖x - (P i).eval t‖ ≤ C₀ / ‖t‖ :=
  Polynomial.exists_branch_near_root F hF hwt c hc hlead P hP hPinj hR

-- Boundary: with no branches (`n = 0`), there is no index to witness the
-- conclusion, so for all sufficiently large `t` the specialization has no root.
example (F : Polynomial (Polynomial ℂ)) (hF : F.natDegree ≤ 0)
    (hwt : ∀ k j : ℕ, 0 * (0 - k) < j → (F.coeff k).coeff j = 0)
    (c : ℂ) (hc : c ≠ 0) (hlead : F.coeff 0 = C c)
    (P : Fin 0 → Polynomial ℂ) (hP : ∀ i, (P i).natDegree ≤ 0)
    (hPinj : Function.Injective fun i => (P i).coeff 0)
    (hR : ∀ k j : ℕ, 0 * (0 - k) ≤ j + 0 →
      ((F - C (C c) * ∏ i, (X - C (P i))).coeff k).coeff j = 0) :
    ∃ T : ℝ, ∀ t : ℂ, T ≤ ‖t‖ → ∀ x : ℂ,
      ¬ (F.map (Polynomial.evalRingHom t)).IsRoot x := by
  obtain ⟨C₀, T, _hC₀, h⟩ := exactSource F hF hwt c hc hlead P hP hPinj hR
  refine ⟨T, fun t ht x hx => ?_⟩
  obtain ⟨i, _hi⟩ := h t ht x hx
  exact i.elim0
