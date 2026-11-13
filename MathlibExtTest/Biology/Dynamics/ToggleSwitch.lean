/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.ToggleSwitch
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! Tests for the Gardner–Cantor–Collins toggle switch.

* Symmetric switch `α₁ = α₂ = 10`, `β = γ = 2`: exactly three equilibria `(2, 2)` and
  `(5 ± 2√6, 5 ∓ 2√6)`, computed from the equilibrium equations; the symmetric one is a saddle with
  eigenvalues `3/5, -13/5`, the other two are stable with eigenvalues `-4/5, -6/5`.
* `β = 1`, `γ = 2`, `a = 6`, `b = 10`: three equilibria `(1, 5)`, `(2, 2)`, `(3, 1)`
  (stable, saddle, stable).
* `a = 6`, `b = 55/4` (past the upper saddle-node): the single equilibrium `(1/2, 11)`, stable.
* `a = 16/3`: the nullcline-tangency condition forces `u = 2, b = 25/3` (or `u = (1 + √13)/3`);
  at `b = 25/3` the equilibria are `(2, 5/3)` (tangent, eigenvalue `0`) and `(4/3, 3)`.
* The Jacobian predicates look only at the Jacobian: at the non-equilibrium `(0, 0)` the
  Jacobian can be Hurwitz or have saddle spectrum, and the nullcline directions can be parallel
  without the nullclines being tangent there.
-/

open Set

namespace MathlibExtTest.Biology.Dynamics.ToggleSwitch

open MathlibExt.Biology.Dynamics.ToggleSwitch

/-! ### Symmetric switch `α₁ = α₂ = 10`, `β = γ = 2` -/

section Symmetric

lemma sqrt6_sq : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)

lemma two_sqrt6_lt_five : 2 * √6 < 5 := by
  nlinarith [Real.sqrt_nonneg 6, sqrt6_sq]

/-- The three equilibria of the symmetric switch, computed from the equilibrium equations
`u (1 + v²) = 10`, `v (1 + u²) = 10`, i.e. `(u - v)(1 - u v) = 0`. -/
theorem symmetric_equilibria :
    equilibria 10 10 2 2 =
      {(2, 2), (5 + 2 * √6, 5 - 2 * √6), (5 - 2 * √6, 5 + 2 * √6)} := by
  have h6 := sqrt6_sq
  have h5 := two_sqrt6_lt_five
  have hs0 := Real.sqrt_nonneg 6
  ext ⟨u, v⟩
  simp only [equilibria, IsEquilibrium, uDot, vDot, hill, mem_ofPred_eq, mem_insert_iff,
    mem_singleton_iff, Prod.mk.injEq, sub_eq_zero]
  constructor
  · rintro ⟨hu, hv, h1, h2⟩
    have hv2 : 0 < 1 + v ^ 2 := by positivity
    have hu2 : 0 < 1 + u ^ 2 := by positivity
    rw [div_eq_iff hv2.ne'] at h1
    rw [div_eq_iff hu2.ne'] at h2
    have hfac : (u - v) * (1 - u * v) = 0 := by linear_combination h2 - h1
    rcases mul_eq_zero.1 hfac with h | h
    · have huv : u = v := sub_eq_zero.1 h
      subst huv
      have : (u - 2) * (u ^ 2 + 2 * u + 5) = 0 := by linear_combination -h1
      have hq : u ^ 2 + 2 * u + 5 ≠ 0 := by positivity
      have : u = 2 := sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hq)
      exact Or.inl ⟨this, this⟩
    · have hsum : u + v = 10 := by linear_combination -h1 + v * h
      have : (u - (5 + 2 * √6)) * (u - (5 - 2 * √6)) = 0 := by
        linear_combination h + u * hsum - 4 * h6
      rcases mul_eq_zero.1 this with h' | h'
      · have hu' : u = 5 + 2 * √6 := sub_eq_zero.1 h'
        exact Or.inr (Or.inl ⟨hu', by linarith⟩)
      · have hu' : u = 5 - 2 * √6 := sub_eq_zero.1 h'
        exact Or.inr (Or.inr ⟨hu', by linarith⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · norm_num
    · refine ⟨by positivity, by linarith, ?_, ?_⟩
      · rw [div_eq_iff (by positivity)]; linear_combination (20 - 8 * √6) * h6
      · rw [div_eq_iff (by positivity)]; linear_combination (20 + 8 * √6) * h6
    · refine ⟨by linarith, by positivity, ?_, ?_⟩
      · rw [div_eq_iff (by positivity)]; linear_combination (20 + 8 * √6) * h6
      · rw [div_eq_iff (by positivity)]; linear_combination (20 - 8 * √6) * h6

theorem symmetric_ncard : (equilibria 10 10 2 2).ncard = 3 := by
  have h5 := two_sqrt6_lt_five
  have hs0 : 0 < √6 := Real.sqrt_pos.2 (by norm_num)
  rw [symmetric_equilibria, ncard_eq_three]
  refine ⟨_, _, _, ?_, ?_, ?_, rfl⟩ <;> simp only [ne_eq, Prod.mk.injEq, not_and] <;>
    intro h <;> nlinarith

/-- `3/5` is an eigenvalue at `(2, 2)`: `det (J - 3/5) = 0`, straight from the Jacobian. -/
example : (3 / 5 : ℂ) ∈ eigenvalues 10 10 2 2 2 2 := by
  rw [eigenvalues, Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_fin_two]
  simp [jacobian, hillDeriv, Matrix.trace_fin_two, Matrix.det_fin_two]
  norm_num

theorem symmetric_loopGain_center : loopGain 10 10 2 2 2 2 = 64 / 25 := by
  norm_num [loopGain, hillDeriv]

/-- The symmetric equilibrium `(2, 2)` has eigenvalues `3/5` and `-13/5`: a saddle. -/
theorem symmetric_eigenvalues_center :
    eigenvalues 10 10 2 2 2 2 = {(3 / 5 : ℂ), (-13 / 5 : ℂ)} := by
  rw [eigenvalues_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    symmetric_loopGain_center, show √(64 / 25 : ℝ) = 8 / 5 by
      rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]; norm_num]
  push_cast
  norm_num

example : HasSaddleSpectrum 10 10 2 2 2 2 := by
  rw [hasSaddleSpectrum_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    symmetric_loopGain_center]
  norm_num

/-- Off-diagonal Jacobian entries at `(5 + 2√6, 5 - 2√6)`, using `1 + (5 ∓ 2√6)² = 10 (5 ∓ 2√6)`. -/
theorem symmetric_loopGain_side :
    loopGain 10 10 2 2 (5 + 2 * √6) (5 - 2 * √6) = 1 / 25 := by
  have h6 := sqrt6_sq
  have h5 := two_sqrt6_lt_five
  have hp : 1 + (5 + 2 * √6) ^ 2 = 10 * (5 + 2 * √6) := by linear_combination 4 * h6
  have hm : 1 + (5 - 2 * √6) ^ 2 = 10 * (5 - 2 * √6) := by linear_combination 4 * h6
  have hpm : (5 + 2 * √6) * (5 - 2 * √6) = 1 := by linear_combination -4 * h6
  have hm0 : 0 < 5 - 2 * √6 := by linarith
  have hp0 : 0 < 5 + 2 * √6 := by positivity
  simp only [loopGain, hillDeriv, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, hp, hm]
  field_simp
  linear_combination (4 * (5 + 2 * √6) * (5 - 2 * √6) + 4) * hpm + (-64 * √6 ^ 2 + 816) * h6

/-- The two asymmetric equilibria are stable with eigenvalues `-4/5` and `-6/5`. -/
theorem symmetric_eigenvalues_side :
    eigenvalues 10 10 2 2 (5 + 2 * √6) (5 - 2 * √6) = {(-4 / 5 : ℂ), (-6 / 5 : ℂ)} := by
  have h5 := two_sqrt6_lt_five
  rw [eigenvalues_eq (by norm_num) (by norm_num) (by positivity) (by linarith),
    symmetric_loopGain_side, show √(1 / 25 : ℝ) = 1 / 5 by
      rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]; norm_num]
  push_cast
  norm_num

example : (jacobian 10 10 2 2 (5 + 2 * √6) (5 - 2 * √6)).IsHurwitz := by
  have h5 := two_sqrt6_lt_five
  rw [isHurwitz_jacobian_iff (by norm_num) (by norm_num) (by positivity) (by linarith),
    symmetric_loopGain_side]
  norm_num

/-- By the `u ↔ v` symmetry the mirror equilibrium has the same loop gain. -/
example : (jacobian 10 10 2 2 (5 - 2 * √6) (5 + 2 * √6)).IsHurwitz := by
  have h5 := two_sqrt6_lt_five
  rw [isHurwitz_jacobian_iff (by norm_num) (by norm_num) (by linarith) (by positivity),
    loopGain, mul_comm, ← loopGain, symmetric_loopGain_side]
  norm_num

end Symmetric

/-! ### `β = 1`, `γ = 2`: three equilibria at `a = 6`, `b = 10` -/

section Three

/-- Computed from the equilibrium equations: `u (1 + v) = 6`, `v (1 + u²) = 10` reduce to
`(u - 1)(u - 2)(u - 3) = 0`. -/
theorem three_example : equilibria 6 10 1 2 = {(1, 5), (2, 2), (3, 1)} := by
  ext ⟨u, v⟩
  simp only [equilibria, IsEquilibrium, uDot, vDot, hill, mem_ofPred_eq, mem_insert_iff,
    mem_singleton_iff, Prod.mk.injEq, sub_eq_zero, pow_one]
  constructor
  · rintro ⟨hu, hv, h1, h2⟩
    have hv1 : 0 < 1 + v := by linarith
    have hu2 : 0 < 1 + u ^ 2 := by positivity
    rw [div_eq_iff hv1.ne'] at h1
    rw [div_eq_iff hu2.ne'] at h2
    have : (u - 1) * (u - 2) * (u - 3) = 0 := by
      linear_combination (-(u ^ 2) - 1) * h1 + u * h2
    have hv' : v = 10 / (1 + u ^ 2) := by rw [eq_div_iff hu2.ne']; linarith
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · have : u = 1 := by linarith
        subst this; norm_num at hv' ⊢; exact hv'
      · have : u = 2 := by linarith
        subst this; norm_num at hv' ⊢; exact hv'
    · have : u = 3 := by linarith
      subst this; norm_num at hv' ⊢; exact hv'
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

example : (equilibria 6 10 1 2).ncard = 3 := by
  rw [three_example, ncard_eq_three]
  exact ⟨_, _, _, by norm_num, by norm_num, by norm_num, rfl⟩

/-- Loop gains from the definition: `5/6`, `16/15`, `9/10`. -/
example : loopGain 6 10 1 2 1 5 = 5 / 6 := by norm_num [loopGain, hillDeriv]
example : loopGain 6 10 1 2 2 2 = 16 / 15 := by norm_num [loopGain, hillDeriv]
example : loopGain 6 10 1 2 3 1 = 9 / 10 := by norm_num [loopGain, hillDeriv]

/-- The three equilibria are stable, saddle, stable. -/
example : (jacobian 6 10 1 2 1 5).IsHurwitz ∧ HasSaddleSpectrum 6 10 1 2 2 2 ∧
    (jacobian 6 10 1 2 3 1).IsHurwitz := by
  refine ⟨?_, ?_, ?_⟩
  · rw [isHurwitz_jacobian_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num [loopGain, hillDeriv]
  · rw [hasSaddleSpectrum_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num [loopGain, hillDeriv]
  · rw [isHurwitz_jacobian_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num [loopGain, hillDeriv]

/-- The bistability theorems apply to this parameter set. -/
example : ∃ u₁ v₁ u₂ v₂, IsEquilibrium 6 10 1 2 u₁ v₁ ∧ IsEquilibrium 6 10 1 2 u₂ v₂ ∧
    u₁ ≠ u₂ ∧ (jacobian 6 10 1 2 u₁ v₁).IsHurwitz ∧ (jacobian 6 10 1 2 u₂ v₂).IsHurwitz :=
  (ncard_equilibria_eq_three_iff_bistable (by norm_num) (by norm_num)).1 (by
    rw [three_example, ncard_eq_three]
    exact ⟨_, _, _, by norm_num, by norm_num, by norm_num, rfl⟩)

end Three

/-! ### Past the threshold: one equilibrium at `a = 6`, `b = 55/4` -/

section One

/-- Computed from the equilibrium equations: the cubic is
`(u - 1/2)(u² - 11/2 u + 12)` and the quadratic factor has no real root. -/
theorem one_example : equilibria 6 (55 / 4) 1 2 = {(1 / 2, 11)} := by
  ext ⟨u, v⟩
  simp only [equilibria, IsEquilibrium, uDot, vDot, hill, mem_ofPred_eq, mem_singleton_iff,
    Prod.mk.injEq, sub_eq_zero, pow_one]
  constructor
  · rintro ⟨hu, hv, h1, h2⟩
    have hv1 : 0 < 1 + v := by linarith
    have hu2 : 0 < 1 + u ^ 2 := by positivity
    rw [div_eq_iff hv1.ne'] at h1
    rw [div_eq_iff hu2.ne'] at h2
    have : (u - 1 / 2) * (u ^ 2 - 11 / 2 * u + 12) = 0 := by
      linear_combination (-(u ^ 2) - 1) * h1 + u * h2
    have hq : u ^ 2 - 11 / 2 * u + 12 ≠ 0 := by nlinarith [sq_nonneg (u - 11 / 4)]
    have hu' : u = 1 / 2 := by linarith [(mul_eq_zero.1 this).resolve_right hq]
    subst hu'
    refine ⟨rfl, ?_⟩
    linarith
  · rintro ⟨rfl, rfl⟩
    norm_num

example : (equilibria 6 (55 / 4) 1 2).ncard = 1 := by
  rw [one_example, ncard_singleton]

example : loopGain 6 (55 / 4) 1 2 (1 / 2) 11 = 11 / 30 := by norm_num [loopGain, hillDeriv]

example : (jacobian 6 (55 / 4) 1 2 (1 / 2) 11).IsHurwitz := by
  rw [isHurwitz_jacobian_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num [loopGain, hillDeriv]

end One

/-! ### The saddle-node point at `a = 16/3` -/

section SaddleNode

/-- The bifurcation point from the tangency condition: an equilibrium with tangent nullclines at
`a = 16/3` has `2u³ - a u² + a = 0`, i.e. `(u - 2)(3u² - 2u - 4) = 0`, and `u = 2` forces
`b = 25/3`. -/
theorem tangency_point {b u v : ℝ} (hb : 0 < b) (he : IsEquilibrium (16 / 3) b 1 2 u v)
    (ht : NullclinesTangent (16 / 3) b 1 2 u v) :
    (u = 2 ∧ b = 25 / 3 ∧ v = 5 / 3) ∨ u = (1 + √13) / 3 := by
  have ha : (0 : ℝ) < 16 / 3 := by norm_num
  obtain ⟨hc, hv⟩ := (isEquilibrium_iff ha hb).1 he
  have hD := (nullclinesTangent_iff_cubicDeriv ha hb he).1 ht
  have hu := pos_of_cubic_eq_zero ha hb hc
  unfold cubic at hc
  unfold cubicDeriv at hD
  have h13 : √13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have : (u - 2) * (u - (1 + √13) / 3) * (u - (1 - √13) / 3) = 0 := by
    linear_combination (u * hD - hc) / 2 - (u - 2) / 9 * h13
  rcases mul_eq_zero.1 this with h | h
  · rcases mul_eq_zero.1 h with h | h
    · have hu2 : u = 2 := sub_eq_zero.1 h
      subst hu2
      have hb' : b = 25 / 3 := by linarith
      subst hb'
      exact Or.inl ⟨rfl, rfl, by rw [hv]; norm_num⟩
    · exact Or.inr (sub_eq_zero.1 h)
  · exfalso
    have : u = (1 - √13) / 3 := sub_eq_zero.1 h
    have : (1 : ℝ) < √13 := by
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith

/-- At `b = 25/3` the point `(2, 5/3)` is an equilibrium with tangent nullclines, computed from
the definitions: the tangent slopes are `-3/4` and `-4/3`. -/
example : IsEquilibrium (16 / 3) (25 / 3) 1 2 2 (5 / 3) := by
  norm_num [IsEquilibrium, uDot, vDot, hill]

example : hillDeriv (16 / 3) 1 (5 / 3) = -3 / 4 := by norm_num [hillDeriv]
example : hillDeriv (25 / 3) 2 2 = -4 / 3 := by norm_num [hillDeriv]

theorem tangent_example : NullclinesTangent (16 / 3) (25 / 3) 1 2 2 (5 / 3) := by
  norm_num [NullclinesTangent, NullclineTangentsParallel, uDot, vDot, hill, Matrix.det_fin_two_of,
    hillDeriv]

/-- A zero eigenvalue at the saddle-node point. -/
example : (0 : ℂ) ∈ eigenvalues (16 / 3) (25 / 3) 1 2 2 (5 / 3) := by
  rw [eigenvalues, Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_fin_two]
  simp [jacobian, hillDeriv, Matrix.trace_fin_two, Matrix.det_fin_two]
  norm_num

/-- Computed from the equilibrium equations: the cubic is `(u - 2)² (u - 4/3)`. -/
theorem two_example : equilibria (16 / 3) (25 / 3) 1 2 = {(2, 5 / 3), (4 / 3, 3)} := by
  ext ⟨u, v⟩
  simp only [equilibria, IsEquilibrium, uDot, vDot, hill, mem_ofPred_eq, mem_insert_iff,
    mem_singleton_iff, Prod.mk.injEq, sub_eq_zero, pow_one]
  constructor
  · rintro ⟨hu, hv, h1, h2⟩
    have hv1 : 0 < 1 + v := by linarith
    have hu2 : 0 < 1 + u ^ 2 := by positivity
    rw [div_eq_iff hv1.ne'] at h1
    rw [div_eq_iff hu2.ne'] at h2
    have : (u - 2) ^ 2 * (u - 4 / 3) = 0 := by
      linear_combination (-(u ^ 2) - 1) * h1 + u * h2
    have hv' : v = 25 / 3 / (1 + u ^ 2) := by rw [eq_div_iff hu2.ne']; linarith
    rcases mul_eq_zero.1 this with h | h
    · have : u = 2 := by nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 h]
      subst this; norm_num at hv' ⊢; exact hv'
    · have : u = 4 / 3 := by linarith
      subst this; norm_num at hv' ⊢; exact hv'
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

example : (equilibria (16 / 3) (25 / 3) 1 2).ncard = 2 := by
  rw [two_example, ncard_pair (by norm_num)]

/-- The two-equilibrium characterization applies. -/
example : (equilibria (16 / 3) (25 / 3) 1 2).ncard = 2 :=
  (ncard_equilibria_eq_two_iff (by norm_num) (by norm_num)).2
    ⟨2, 5 / 3, by norm_num [IsEquilibrium, uDot, vDot, hill], tangent_example, by norm_num⟩

/-- The collision theorem applies at `(u₀, b₀) = (2, 25/3)`; here `3 u₀ - a = 2/3 > 0`, so the
two colliding equilibria exist for `b < 25/3`, one on each side of `u₀ = 2`. -/
example : ∀ δ > 0, ∃ ε > 0, ∀ b, 0 < b → |b - 25 / 3| < ε → 0 < (25 / 3 - b) * (3 * 2 - 16 / 3) →
    ∃ u₁ u₂, u₁ < 2 ∧ 2 < u₂ ∧ |u₁ - 2| < δ ∧ |u₂ - 2| < δ ∧
      IsEquilibrium (16 / 3) b 1 2 u₁ (b / (1 + u₁ ^ 2)) ∧
      IsEquilibrium (16 / 3) b 1 2 u₂ (b / (1 + u₂ ^ 2)) :=
  (saddleNode_collision (by norm_num) (by norm_num)
    (by norm_num [IsEquilibrium, uDot, vDot, hill]) tangent_example (by norm_num)).2

end SaddleNode

/-! ### The Jacobian predicates do not require an equilibrium -/

section NonEquilibrium

/-- At `(0, 0)` with `α₁ = α₂ = 1/2`, `β = γ = 1` the Jacobian is Hurwitz (`P = 1/4`), but the
vector field there is `(1/2, 1/2)`, so the point is not an equilibrium. -/
example :
    (jacobian (1 / 2) (1 / 2) 1 1 0 0).IsHurwitz ∧ ¬ IsEquilibrium (1 / 2) (1 / 2) 1 1 0 0 := by
  refine ⟨?_, fun h => ?_⟩
  · rw [isHurwitz_jacobian_iff (by norm_num) (by norm_num) le_rfl le_rfl]
    norm_num [loopGain, hillDeriv]
  · have := h.2.2.1
    norm_num [uDot, hill] at this

/-- With `α₁ = α₂ = 2` the Jacobian at `(0, 0)` has saddle spectrum (`P = 4`), again at a point
that is not an equilibrium. -/
example : HasSaddleSpectrum 2 2 1 1 0 0 ∧ ¬ IsEquilibrium 2 2 1 1 0 0 := by
  refine ⟨?_, fun h => ?_⟩
  · rw [hasSaddleSpectrum_iff (by norm_num) (by norm_num) le_rfl le_rfl]
    norm_num [loopGain, hillDeriv]
  · have := h.2.2.1
    norm_num [uDot, hill] at this

/-- With `α₁ = α₂ = 1`, `β = γ = 1` the nullcline directions at `(0, 0)` are parallel (both
slopes are `-1`), but `(0, 0)` lies on neither nullcline, so they are not tangent there. -/
example : NullclineTangentsParallel 1 1 1 1 0 0 ∧ ¬ NullclinesTangent 1 1 1 1 0 0 := by
  refine ⟨?_, fun h => ?_⟩
  · norm_num [NullclineTangentsParallel, Matrix.det_fin_two_of, hillDeriv]
  · have := h.1
    norm_num [uDot, hill] at this

end NonEquilibrium

end MathlibExtTest.Biology.Dynamics.ToggleSwitch
