/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AffineLogThresholds

/-!
# Tests for local thresholds of affine hypersurfaces

A coordinate function vanishes to order one at the origin, and a nonvanishing polynomial has
infinite threshold, its density being bounded near every point.
-/

open MathlibExt.AlgebraicGeometry.AffineLogThresholds MeasureTheory

example : orderAt (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℂ) 0 = 1 := by
  have h : {m : ℕ | ∃ a : Fin 1 →₀ ℕ,
      (translated (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℂ) 0).coeff a ≠ 0 ∧
        (∑ i, a i) = m} = {1} := by
    ext m
    simp only [translated, MvPolynomial.eval₂_X, Pi.zero_apply, map_zero, add_zero,
      MvPolynomial.coeff_X, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not,
      Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, rfl, rfl⟩
      simp
    · rintro rfl
      exact ⟨Finsupp.single 0 1, rfl, by simp⟩
  rw [orderAt, h, csInf_singleton]

example (n : ℕ) (p : Fin n → ℂ) : localThreshold (1 : MvPolynomial (Fin n) ℂ) p = ⊤ := by
  have hint (r : ℝ) : IntegrableNear (1 : MvPolynomial (Fin n) ℂ) r p := by
    refine ⟨Metric.ball p 1, Metric.ball_mem_nhds p one_pos, ?_⟩
    have hd : density (1 : MvPolynomial (Fin n) ℂ) r = fun _ ↦ 1 := by
      funext z
      simp [density]
    rw [hd]
    exact integrableOn_const measure_ball_lt_top.ne
  unfold localThreshold
  split_ifs with h
  · exact absurd h one_ne_zero
  refine ENNReal.eq_top_of_forall_nnreal_le fun x ↦ le_sSup ?_
  exact ⟨x, x.2, ENNReal.ofReal_coe_nnreal.symm, hint x⟩
