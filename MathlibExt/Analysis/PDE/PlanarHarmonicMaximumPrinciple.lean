/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Harmonic.Analytic
public import Mathlib.Analysis.Complex.AbsMax

/-!
# Strong maximum principle for harmonic functions in the plane

A real harmonic function on a connected open subset of `ℂ` that attains its maximum at a point of
the set is constant there. The proof bridges Mathlib's planar harmonic-function API to its maximum
modulus principle: on a ball, a harmonic `u` is the real part of a holomorphic `F`
(`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`), so `‖exp F‖ = exp u` attains
its maximum at the centre and `exp F` is constant
(`Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`). Hence the set where `u` attains its maximum is
open; it is relatively closed by continuity, so it is the whole connected set.

This is the two-dimensional case of the strong maximum principle recorded as wanted in
`WantedExt.Analysis.PDE.LaplaceMeanValueWanted` (which assumes in addition that the set is bounded
and the maximum is taken over its closure).

## References

* M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025,
  Chapter 3 (Laplace equation),
  https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_3.pdf: Strong
  Maximum Principle 3.10 (proved there from the mean-value property in `ℝⁿ`).
* L. C. Evans, *Entropy and Partial Differential Equations*, lecture notes,
  https://math.berkeley.edu/~evans/entropy.and.PDE.pdf, Chapter IV.A.3, Corollary.
-/

@[expose] public section

open InnerProductSpace Metric Set

namespace MathlibExt.Analysis.PDE.PlanarHarmonicMaximumPrinciple

/-- **A planar harmonic function is constant near an interior maximum.** If `u : ℂ → ℝ` is
harmonic on an open set `U` and attains its maximum over `U` at `z ∈ U`, then `u` is constant on
some ball around `z` contained in `U`. This is the local step of the proof of Strong Maximum
Principle 3.10 in M. Schmidt, *Partial Differential Equations*, lecture notes, Universität
Mannheim, HWS 2025, Chapter 3, obtained here from the maximum modulus principle for `exp F` with
`u = Re F` instead of the mean-value property. -/
theorem exists_ball_eqOn_of_isMaxOn_complex {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u U) {z : ℂ} (hz : z ∈ U) (hmax : IsMaxOn u U z) :
    ∃ r > 0, ball z r ⊆ U ∧ EqOn u (fun _ => u z) (ball z r) := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z hz
  refine ⟨r, hr, hrU, ?_⟩
  obtain ⟨F, hFan, hFre⟩ := (hu.mono hrU).exists_analyticOnNhd_ball_re_eq
  have hnorm : ∀ w ∈ ball z r, ‖Complex.exp (F w)‖ = Real.exp (u w) := fun w hw => by
    rw [Complex.norm_exp]
    exact congrArg Real.exp (hFre hw)
  have hd : DifferentiableOn ℂ (fun w => Complex.exp (F w)) (ball z r) :=
    hFan.differentiableOn.cexp
  have hm : IsMaxOn (norm ∘ fun w => Complex.exp (F w)) (ball z r) z := by
    intro w hw
    simp only [mem_ofPred_eq, Function.comp_apply]
    rw [hnorm w hw, hnorm z (mem_ball_self hr)]
    exact Real.exp_le_exp.mpr (hmax (hrU hw))
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball z r).isPreconnected
    isOpen_ball hd (mem_ball_self hr) hm
  intro w hw
  have h1 := congrArg norm (heq hw)
  simp only [Function.const_apply] at h1
  rw [hnorm w hw, hnorm z (mem_ball_self hr)] at h1
  exact Real.exp_injective h1

/-- **Strong maximum principle for planar harmonic functions.** Let `U ⊆ ℂ` be open and
(pre)connected and let `u : ℂ → ℝ` be harmonic on `U`. If `u` attains its maximum over `U` at a
point `x₀ ∈ U`, then `u = u x₀` on `U`. This is Strong Maximum Principle 3.10 of M. Schmidt,
*Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025, Chapter 3, in
dimension two (stated there for path-connected open subsets of `ℝⁿ`); no boundedness of `U` is
needed. -/
theorem eqOn_of_isMaxOn_complex {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U) {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u U) {x₀ : ℂ} (hx₀ : x₀ ∈ U) (hmax : IsMaxOn u U x₀) :
    EqOn u (fun _ => u x₀) U := by
  set A := {z | z ∈ U ∧ u z = u x₀} with hA
  set B := U ∩ u ⁻¹' Iio (u x₀) with hB
  have hAo : IsOpen A := by
    refine Metric.isOpen_iff.mpr fun z ⟨hzU, hzM⟩ => ?_
    have hzmax : IsMaxOn u U z := fun w hw => hzM ▸ hmax hw
    obtain ⟨r, hr, hrU, heq⟩ := exists_ball_eqOn_of_isMaxOn_complex hU hu hzU hzmax
    exact ⟨r, hr, fun w hw => ⟨hrU hw, (heq hw).trans hzM⟩⟩
  have hBo : IsOpen B := hu.continuousOn.isOpen_inter_preimage hU isOpen_Iio
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro z ⟨_, hz⟩ ⟨_, hz'⟩
    simp only [mem_preimage, mem_Iio] at hz'
    exact lt_irrefl _ (hz ▸ hz')
  have hcover : U ⊆ A ∪ B := fun z hz => by
    rcases (hmax hz : u z ≤ u x₀).eq_or_lt with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  have hsub := hconn.subset_left_of_subset_union hAo hBo hdisj hcover ⟨x₀, hx₀, hx₀, rfl⟩
  exact fun z hz => (hsub hz).2

end MathlibExt.Analysis.PDE.PlanarHarmonicMaximumPrinciple
