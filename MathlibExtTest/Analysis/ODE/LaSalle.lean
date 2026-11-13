/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.LaSalle
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Tests for LaSalle's invariance principle for ODEs.

* `x' = -x, y' = 0` on `ℝ × ℝ` with `V = x² + y²` on the square `K = closedBall 0 r`: the
  orbital derivative is `-2x² ≤ 0` (only semidefinite), the set `{V' = 0}` is the segment
  `{0} × [-r, r]`, computed by hand to be its own largest forward-invariant subset (every point of
  it is an equilibrium). The explicit solution `(x₀ e^{-t}, y₀)` is a non-vacuity witness for
  every hypothesis of `lasalle_of_hasFDerivAt`, and the theorem gives `x(t) → 0`, which is checked
  against the explicit formula.
* The damped oscillator `x' = y, y' = -x - y` with `{V' = 0} = {y = 0}`: the largest
  forward-invariant subset of `{y = 0}` is `{0}` (hand computation), strictly smaller than
  `{y = 0}`.
* A noncompact case where LaSalle is not claimed: `x' = 1` on `K = [0, ∞)` with `V = e^{-x}`.
  Every hypothesis holds except compactness, `V' < 0` so the largest invariant subset of
  `{V' = 0}` is empty, and the conclusion fails: the ω-limit set of `x(t) = t` is empty.
* Reversible Michaelis–Menten with all rate constants `1` and initial state
  `(s, c, e, p) = (1, 0, 1, 0)` on the boundary of the orthant: the solution is positive for
  `t > 0` and converges to the equilibrium
  `((√3 - 1)/2, 2 - √3, √3 - 1, (√3 - 1)/2)`, computed by hand. -/

open Set Filter Metric
open scoped Topology

namespace MathlibExtTest.Analysis.ODE.LaSalle

open MathlibExt.Analysis.ODE

/-! ### `x' = -x, y' = 0`: the LaSalle set is a segment -/

/-- The field `(x, y) ↦ (-x, 0)`, as a continuous linear map. -/
noncomputable def decayX : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  (-(ContinuousLinearMap.fst ℝ ℝ ℝ)).prod 0

@[simp] theorem decayX_apply (q : ℝ × ℝ) : decayX q = (-q.1, 0) := rfl

/-- `V (x, y) = x² + y²`. -/
def sqNorm (q : ℝ × ℝ) : ℝ := q.1 * q.1 + q.2 * q.2

/-- The derivative of `sqNorm` at `q`: `(u, v) ↦ 2 q₁ u + 2 q₂ v`. -/
noncomputable def sqNorm' (q : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (2 * q.1) • ContinuousLinearMap.fst ℝ ℝ ℝ + (2 * q.2) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem hasFDerivAt_sqNorm (q : ℝ × ℝ) : HasFDerivAt sqNorm (sqNorm' q) q := by
  have hf : HasFDerivAt (fun p : ℝ × ℝ => p.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) q :=
    hasFDerivAt_fst
  have hs : HasFDerivAt (fun p : ℝ × ℝ => p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
    hasFDerivAt_snd
  refine ((hf.mul hf).add (hs.mul hs)).congr_fderiv ?_
  ext <;> simp [sqNorm'] <;> ring

/-- The orbital derivative is `-2x²`: negative semidefinite, not definite. -/
theorem sqNorm'_decayX (q : ℝ × ℝ) : sqNorm' q (decayX q) = -2 * q.1 ^ 2 := by
  simp [sqNorm']; ring

/-- The explicit solution `(x₀ e^{-t}, y₀)`. -/
noncomputable def decaySol (q : ℝ × ℝ) (t : ℝ) : ℝ × ℝ := (q.1 * Real.exp (-t), q.2)

theorem isIntegralCurveOn_decaySol (q : ℝ × ℝ) :
    IsIntegralCurveOn (decaySol q) (fun _ => decayX) (Ici 0) := by
  intro t _
  have h1 : HasDerivAt (fun τ => q.1 * Real.exp (-τ)) (-(q.1 * Real.exp (-t))) t := by
    have := ((hasDerivAt_neg t).exp).const_mul q.1
    convert this using 1; ring
  exact (h1.prodMk (hasDerivAt_const t q.2)).hasDerivWithinAt

theorem decaySol_mem {r : ℝ} {q : ℝ × ℝ} (hq : q ∈ closedBall (0 : ℝ × ℝ) r) {t : ℝ}
    (ht : 0 ≤ t) : decaySol q t ∈ closedBall (0 : ℝ × ℝ) r := by
  rw [mem_closedBall_zero_iff, Prod.norm_def] at hq ⊢
  refine le_trans (max_le_max ?_ le_rfl) hq
  simp only [decaySol, norm_mul, Real.norm_eq_abs, Real.abs_exp]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.2 (by linarith))

theorem isForwardInvariant_closedBall (r : ℝ) :
    IsForwardInvariant decayX (closedBall (0 : ℝ × ℝ) r) := fun q hq =>
  ⟨decaySol q, isIntegralCurveOn_decaySol q, by simp [decaySol], fun _ ht => decaySol_mem hq ht⟩

/-- **The LaSalle set, by hand.** The largest forward-invariant subset of
`{q ∈ K | V' q (f q) = 0}` is the whole segment `{0} × [-r, r]` of `K = closedBall 0 r`: every
point of it is an equilibrium. -/
theorem largestForwardInvariantSubset_decayX (r : ℝ) :
    largestForwardInvariantSubset decayX
        {q | q ∈ closedBall (0 : ℝ × ℝ) r ∧ sqNorm' q (decayX q) = 0} =
      {q | q ∈ closedBall (0 : ℝ × ℝ) r ∧ q.1 = 0} := by
  have hZ : {q | q ∈ closedBall (0 : ℝ × ℝ) r ∧ sqNorm' q (decayX q) = 0} =
      {q | q ∈ closedBall (0 : ℝ × ℝ) r ∧ q.1 = 0} := by
    ext q
    exact and_congr_right fun _ => by rw [sqNorm'_decayX]; simp
  rw [hZ]
  refine Subset.antisymm largestForwardInvariantSubset_subset
    (subset_largestForwardInvariantSubset le_rfl fun q hq => ?_)
  refine ⟨fun _ => q, fun t _ => ?_, rfl, fun _ _ => hq⟩
  have : decayX q = 0 := by simp [hq.2]
  simpa [this] using (hasDerivAt_const t q).hasDerivWithinAt

/-- **Convergence from LaSalle.** For every initial point in `closedBall 0 r`, the solution
eventually enters every open set containing the segment `{0} × [-r, r]`; in particular its first
coordinate tends to `0`. -/
theorem decaySol_fst_tendsto {r : ℝ} {q : ℝ × ℝ} (hq : q ∈ closedBall (0 : ℝ × ℝ) r) :
    Tendsto (fun t => (decaySol q t).1) atTop (𝓝 0) := by
  have hL := lasalle_of_hasFDerivAt (isCompact_closedBall (0 : ℝ × ℝ) r)
    (decayX.lipschitzWith.lipschitzOnWith) (isForwardInvariant_closedBall r)
    (isIntegralCurveOn_decaySol q) (fun _ ht => decaySol_mem hq ht)
    (fun x _ => hasFDerivAt_sqNorm x)
    (fun x _ => by rw [sqNorm'_decayX]; nlinarith [sq_nonneg x.1])
  rw [largestForwardInvariantSubset_decayX] at hL
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hU : IsOpen {p : ℝ × ℝ | |p.1| < ε} :=
    isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  filter_upwards [hL.2.2 _ hU fun p hp => by simp [hp.2, hε]] with t ht
  simpa [Real.dist_eq] using ht

/-- The LaSalle conclusion agrees with the explicit formula `x₀ e^{-t} → 0`. -/
example (q : ℝ × ℝ) : Tendsto (fun t => (decaySol q t).1) atTop (𝓝 0) := by
  simpa [decaySol] using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul q.1)

/-- The theorem applies to a concrete starting point: `(1, 1) ∈ closedBall 0 1`. -/
example : Tendsto (fun t => (decaySol (1, 1) t).1) atTop (𝓝 0) :=
  decaySol_fst_tendsto (r := 1) (by simp [Prod.norm_def])

/-! ### The damped oscillator: `M ⊊ {V' = 0}` -/

/-- The damped oscillator `x' = y, y' = -x - y`; for `V = x² + y²` the orbital derivative is
`-2y²`, vanishing on the line `{y = 0}`. -/
def damped (q : ℝ × ℝ) : ℝ × ℝ := (q.2, -q.1 - q.2)

theorem sqNorm'_damped (q : ℝ × ℝ) : sqNorm' q (damped q) = -2 * q.2 ^ 2 := by
  simp [sqNorm', damped]; ring

/-- **The LaSalle set of the damped oscillator, by hand.** The largest forward-invariant subset
of `{V' = 0} = {y = 0}` is `{0}`: a solution staying on `{y = 0}` has `y' = -x = 0`. -/
theorem largestForwardInvariantSubset_damped :
    largestForwardInvariantSubset damped {q | sqNorm' q (damped q) = 0} = {0} := by
  have hZ : {q : ℝ × ℝ | sqNorm' q (damped q) = 0} = {q | q.2 = 0} := by
    ext q
    change sqNorm' q (damped q) = 0 ↔ q.2 = 0
    rw [sqNorm'_damped]
    simp
  rw [hZ]
  refine Subset.antisymm ?_ (subset_largestForwardInvariantSubset (by simp) fun q hq => ?_)
  · intro q hq
    obtain ⟨φ, hφ, hφ0, hφZ⟩ := isForwardInvariant_largestForwardInvariantSubset q hq
    have hZsub : ∀ t, 0 ≤ t → φ t ∈ {q : ℝ × ℝ | q.2 = 0} := fun t ht =>
      largestForwardInvariantSubset_subset (hφZ t ht)
    have hd : HasDerivAt φ (damped (φ 1)) 1 := (hφ 1 zero_le_one).hasDerivAt (Ici_mem_nhds one_pos)
    -- `φ.2 ≡ 0` near `t = 1`, so `(φ 1).1 = -(φ.2)'(1) = 0`
    have h2 : HasDerivAt (fun t => (φ t).2) (-(φ 1).1 - (φ 1).2) 1 := hd.snd
    have h2' : HasDerivAt (fun t => (φ t).2) 0 1 :=
      (hasDerivAt_const (1 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
        (Filter.eventually_of_mem (Ioi_mem_nhds zero_lt_one) fun t ht =>
          (hZsub t (le_of_lt ht) : (φ t).2 = 0))
    have hy1 : (φ 1).2 = 0 := hZsub 1 zero_le_one
    have hx1 : (φ 1).1 = 0 := by linarith [h2.unique h2']
    -- the same argument at `t = 0`, within `[0, ∞)`, pins `q` itself
    have hq2 : q.2 = 0 := by simpa [hφ0] using hZsub 0 le_rfl
    have h0 : HasDerivWithinAt (fun t => (φ t).2) (-(φ 0).1 - (φ 0).2) (Ici 0) 0 :=
      (hφ 0 le_rfl).snd
    have h0' : HasDerivWithinAt (fun t => (φ t).2) 0 (Ici 0) 0 :=
      (hasDerivWithinAt_const (0 : ℝ) (Ici 0) (0 : ℝ)).congr
        (fun t ht => (hZsub t ht : (φ t).2 = 0)) (hZsub 0 le_rfl : (φ 0).2 = 0)
    have := (uniqueDiffWithinAt_Ici 0).eq_deriv _ h0 h0'
    rw [hφ0] at this
    have hq1 : q.1 = 0 := by linarith
    exact Prod.ext hq1 hq2
  · rw [mem_singleton_iff] at hq
    subst hq
    refine ⟨fun _ => 0, fun t _ => ?_, rfl, fun _ _ => rfl⟩
    convert (hasDerivAt_const t (0 : ℝ × ℝ)).hasDerivWithinAt using 1
    ext <;> simp [damped]

/-- The line `{y = 0}` itself is not forward invariant (it strictly contains the LaSalle set). -/
example : ({0} : Set (ℝ × ℝ)) ⊂ {q | sqNorm' q (damped q) = 0} := by
  refine ⟨fun q hq => by rw [mem_singleton_iff] at hq; simp [hq, sqNorm'_damped], fun h => ?_⟩
  have := h (show ((1 : ℝ), (0 : ℝ)) ∈ {q : ℝ × ℝ | sqNorm' q (damped q) = 0} by
    simp [sqNorm'_damped])
  simp [Prod.ext_iff] at this

/-! ### A noncompact set: LaSalle is not claimed -/

/-- `x' = 1` on `ℝ`, with `V x = e^{-x}` and `V' x = -e^{-x}`. -/
noncomputable def expNeg' (x : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.toSpanSingleton ℝ (-Real.exp (-x))

theorem hasFDerivAt_expNeg (x : ℝ) : HasFDerivAt (fun y => Real.exp (-y)) (expNeg' x) x := by
  have := ((hasDerivAt_neg x).exp).hasFDerivAt
  convert this using 1
  ext; simp [expNeg']

/-- **Every hypothesis but compactness, and the conclusion fails.** On `K = [0, ∞)` (closed,
forward invariant, not compact) the field `x' = 1` is Lipschitz, `x(t) = t` stays in `K`, and
`V' x (f x) = -e^{-x} ≤ 0`. The set `{V' = 0}` is empty, so LaSalle would claim that `x(t)`
eventually enters the empty set; instead its ω-limit set is empty. -/
theorem noncompact_counterexample :
    ¬ IsCompact (Ici (0 : ℝ)) ∧
    IsForwardInvariant (fun _ : ℝ => (1 : ℝ)) (Ici 0) ∧
    LipschitzOnWith 0 (fun _ : ℝ => (1 : ℝ)) (Ici 0) ∧
    IsIntegralCurveOn (fun t : ℝ => t) (fun _ _ => (1 : ℝ)) (Ici 0) ∧
    (∀ x ∈ Ici (0 : ℝ), HasFDerivAt (fun y => Real.exp (-y)) (expNeg' x) x) ∧
    (∀ x ∈ Ici (0 : ℝ), expNeg' x 1 ≤ 0) ∧
    {x | x ∈ Ici (0 : ℝ) ∧ expNeg' x 1 = 0} = ∅ ∧
    {y : ℝ | MapClusterPt y atTop fun t : ℝ => t} = ∅ := by
  have hcurve : ∀ a : ℝ, IsIntegralCurveOn (fun t : ℝ => a + t) (fun _ _ => (1 : ℝ)) (Ici 0) :=
    fun a t _ => ((hasDerivAt_id t).const_add a).hasDerivWithinAt
  refine ⟨fun h => not_bddAbove_Ici (0 : ℝ) h.bddAbove, fun a ha => ?_, ?_,
    by simpa using hcurve 0, fun x _ => hasFDerivAt_expNeg x,
    fun x _ => by simp [expNeg', (Real.exp_pos _).le], ?_, ?_⟩
  · exact ⟨fun t => a + t, hcurve a, by simp, fun t ht => by simp only [mem_Ici] at ha ⊢; linarith⟩
  · exact LipschitzWith.lipschitzOnWith (LipschitzWith.const' 1 (K := 0))
  · ext x; simp [expNeg', (Real.exp_pos _).ne']
  · ext y
    simp only [mem_empty_iff_false, iff_false]
    intro hy
    have := (mapClusterPt_iff_frequently.1 hy _ (Iio_mem_nhds (lt_add_one y))).and_eventually
      (eventually_ge_atTop (y + 1))
    obtain ⟨t, ht1, ht2⟩ := this.exists
    exact absurd ht1 (not_lt.2 ht2)

/-! ### Reversible Michaelis–Menten: convergence from a boundary state -/

section MichaelisMenten

open MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten
open MathlibExt.Biology.Dynamics.MichaelisMenten (mmCurve)

/-- The equilibrium of the class `e + c = 1`, `s + c + p = 1` for rate constants `1, 1, 1, 1`,
computed by hand: detailed balance `e s = c = e p` gives `s = p = (1 - c)/2` and
`c² - 4c + 1 = 0`, so `c = 2 - √3`. -/
noncomputable def mmEq : Fin 4 → ℝ :=
  ![(√3 - 1) / 2, 2 - √3, √3 - 1, (√3 - 1) / 2]

theorem mmEq_spec : (∀ i, 0 ≤ mmEq i) ∧ mmEq 2 + mmEq 1 = 1 ∧ mmEq 0 + mmEq 1 + mmEq 3 = 1 ∧
    revField 1 1 1 1 mmEq = 0 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h1 : 1 < √3 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h2 : √3 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine ⟨fun i => ?_, ?_, ?_, revField_eq_zero_iff.2 ⟨?_, ?_⟩⟩
  · fin_cases i <;> simp [mmEq] <;> linarith
  all_goals simp only [mmEq, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  · ring
  · ring
  · nlinarith
  · nlinarith

/-- The orbital derivative of the pseudo-Helmholtz function relative to `mmEq` vanishes at
`mmEq` and is `< 0` at the positive non-equilibrium state `(2, 1, 1, 1)`. -/
example : mmNetwork.helmholtzRate (mmRates 1 1 1 1) mmEq mmEq = 0 ∧
    mmNetwork.helmholtzRate (mmRates 1 1 1 1) mmEq ![2, 1, 1, 1] < 0 := by
  obtain ⟨h0, hE, hS, hf⟩ := mmEq_spec
  have hpos := pos_of_equilibrium (k₁ := 1) (kb := 1) (k₂ := 1) (kb₂ := 1) one_pos one_pos
    one_pos one_pos one_pos one_pos h0 hE hS hf
  have H := fun x hx => helmholtzRate_mmNetwork_nonpos (k₁ := 1) (kb := 1) (k₂ := 1)
    (kb₂ := 1) one_pos one_pos one_pos one_pos (x := x) hpos hf hx
  have h2 : ∀ i, 0 < (![2, 1, 1, 1] : Fin 4 → ℝ) i := fun i => by fin_cases i <;> norm_num
  refine ⟨(H mmEq hpos).2.2 hf, lt_of_le_of_ne (H _ h2).1 fun h => ?_⟩
  have := congrFun ((H _ h2).2.1 h) 0
  norm_num [revField, MathlibExt.Biology.Dynamics.MichaelisMenten.substrateRate] at this

/-- **Non-vacuity and the hand-computed limit.** With all rate constants `1`, the solution from
the boundary state `(1, 0, 1, 0)` (no complex, no product) is strictly positive at `t = 1` and
converges to `mmEq = ((√3 - 1)/2, 2 - √3, √3 - 1, (√3 - 1)/2)`. -/
theorem mm_boundary_start :
    ∃ s c e p : ℝ → ℝ, IsSolution 1 1 1 1 s c e p ∧ s 0 = 1 ∧ c 0 = 0 ∧ e 0 = 1 ∧ p 0 = 0 ∧
      (0 < s 1 ∧ 0 < c 1 ∧ 0 < e 1 ∧ 0 < p 1) ∧ Tendsto (mmCurve s c e p) atTop (𝓝 mmEq) := by
  obtain ⟨s, c, e, p, h, hs, hc, he, hp, -, -, -⟩ :=
    exists_isSolution_nonneg (k₁ := 1) (kb := 1) (k₂ := 1) (kb₂ := 1) zero_le_one zero_le_one
      zero_le_one zero_le_one zero_le_one le_rfl zero_le_one le_rfl
  have hpos := h.pos one_pos one_pos one_pos one_pos (by rw [hs]; exact zero_le_one)
    (by rw [hc]) (by rw [he]; exact zero_le_one) (by rw [hp]) (by rw [he, hc]; norm_num)
    (by rw [hs, hc, hp]; norm_num) one_pos
  obtain ⟨xs, hxs, hxsE, hxsS, hxsf, hlim⟩ := h.tendsto_equilibrium one_pos one_pos one_pos
    one_pos (by rw [hs]; exact zero_le_one) (by rw [hc]) (by rw [he]; exact zero_le_one)
    (by rw [hp]) (by rw [he, hc]; norm_num) (by rw [hs, hc, hp]; norm_num)
  have hxs_eq : xs = mmEq := (existsUnique_equilibrium (k₁ := 1) (kb := 1) (k₂ := 1)
      (kb₂ := 1) one_pos one_pos one_pos one_pos (eT := 1) (sT := 1) one_pos one_pos).unique
    ⟨fun i => (hxs i).le, by rw [hxsE, he, hc]; norm_num, by rw [hxsS, hs, hc, hp]; norm_num,
      hxsf⟩ mmEq_spec
  exact ⟨s, c, e, p, h, hs, hc, he, hp, hpos, hxs_eq ▸ hlim⟩

end MichaelisMenten

end MathlibExtTest.Analysis.ODE.LaSalle
