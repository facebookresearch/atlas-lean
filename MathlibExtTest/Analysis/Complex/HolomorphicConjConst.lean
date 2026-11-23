/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.HolomorphicConjConst
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Group.Basic

/-! # Tests for `MathlibExt.Analysis.Complex.HolomorphicConjConst` -/

set_option autoImplicit false

open scoped ComplexConjugate

namespace MathlibExtTest.HolomorphicConjConst

open MathlibExt.Analysis.Complex.HolomorphicConjConstWanted

-- Test section: complex conjugation is not holomorphic on the unit disc, since otherwise the
-- identity, whose conjugate it is, would be constant there.
example : ¬ DifferentiableOn ℂ (fun z : ℂ => conj z) (Metric.ball 0 1) := fun h => by
  obtain ⟨c, hc⟩ := exists_eqOn_const_of_differentiableOn_conj Metric.isOpen_ball
    ((convex_ball 0 1).isConnected (Metric.nonempty_ball.2 one_pos)) id differentiableOn_id h
  have h0 : (0 : ℂ) = c := hc (Metric.mem_ball_self one_pos)
  have h1 : (1 / 2 : ℂ) = c := hc (by rw [mem_ball_zero_iff]; norm_num)
  norm_num [← h0] at h1

-- Test section: a holomorphic function with real values on a connected open set is constant,
-- since it equals its conjugate there.
example {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f U) (hreal : ∀ z ∈ U, (f z).im = 0) :
    ∃ c : ℂ, Set.EqOn f (fun _ => c) U :=
  exists_eqOn_const_of_differentiableOn_conj hU hUc f hf
    (hf.congr fun z hz => Complex.conj_eq_iff_im.2 (hreal z hz))

-- Test section: on `U = ℂ`, an entire function whose conjugate is entire is a constant function.
example (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hconj : Differentiable ℂ fun z => conj (f z)) :
    ∃ c : ℂ, f = fun _ => c := by
  obtain ⟨c, hc⟩ := exists_eqOn_const_of_differentiableOn_conj isOpen_univ isConnected_univ f
    hf.differentiableOn hconj.differentiableOn
  exact ⟨c, funext fun z => hc (Set.mem_univ z)⟩

-- Test section: connectedness cannot be dropped. Off the imaginary axis, the function equal to
-- `0` on the left half-plane and to `1` on the right half-plane is holomorphic and equal to its
-- conjugate, but it is not constant.
example :
    let U : Set ℂ := {z | z.re < 0} ∪ {z | 0 < z.re}
    let f : ℂ → ℂ := fun z => if z.re < 0 then 0 else 1
    IsOpen U ∧ DifferentiableOn ℂ f U ∧ DifferentiableOn ℂ (fun z => conj (f z)) U ∧
      ¬∃ c : ℂ, Set.EqOn f (fun _ => c) U := by
  intro U f
  have hleft : IsOpen {z : ℂ | z.re < 0} := isOpen_lt Complex.continuous_re continuous_const
  have hright : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : DifferentiableOn ℂ f U := by
    rintro z (hz | hz)
    · refine ((differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hleft.mem_nhds hz] with w (hw : w.re < 0)
      simp [f, hw]
    · refine ((differentiableAt_const (1 : ℂ)).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hright.mem_nhds hz] with w (hw : 0 < w.re)
      simp [f, not_lt.2 hw.le]
  have hconj : (fun z => conj (f z)) = f := by
    funext z
    by_cases hz : z.re < 0 <;> simp [f, hz]
  refine ⟨hleft.union hright, hf, by rw [hconj]; exact hf, ?_⟩
  rintro ⟨c, hc⟩
  have h0 : f (-1) = c := hc (Or.inl (by norm_num))
  have h1 : f 1 = c := hc (Or.inr (by norm_num))
  norm_num [f] at h0 h1
  exact zero_ne_one (h0.trans h1.symm)

end MathlibExtTest.HolomorphicConjConst
