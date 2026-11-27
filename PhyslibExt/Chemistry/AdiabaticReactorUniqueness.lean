/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.AdiabaticReactor
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniqueness of the dimensionless adiabatic steady state

An interval for every steady temperature and a sufficient condition for a unique balance pair.

## i. Overview

Write `k(T) = exp (a - b / T)`. Eliminating the concentration from the two balances gives
`T = 1 + β * k(T) / (1 + k(T))`. The factor `k(T) / (1 + k(T))` is strictly between zero and one.
For `b > 0` and `T ≥ 1`, its derivative is at most `b / 4`, since `4 * k ≤ (1 + k)²`.
Thus for `β ≥ 0` and `β * b < 4`, the residual is strictly decreasing on `[1, ∞)`.
Its endpoint signs give existence even when `β = 0` and the interval reduces to a point.

## ii. Key results

- `steady_state_interval_and_uniqueness`: bounds the temperature without a smallness assumption,
  and gives existence and uniqueness of the entire steady state when `β * b < 4`.

## iii. Table of contents

- A. Steady pairs and the scalar response
- B. Interval and uniqueness

## iv. References

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*,
  2nd ed., 7th printing, §6.3.1, pp. 288–289, equations (6.37)–(6.38), for the balances and
  the possibility of multiplicity. The sufficient inequality here is deduced for the
  dimensionless model. It asserts neither necessity nor dynamical stability.
-/

namespace Chemistry.AdiabaticReactor

/-! ## A. Steady pairs and the scalar response -/

/-- For real parameters `a`, `b`, `β`, the pair `p = (c, T)` solves both dimensionless
steady balances if `1 - c - k*c = 0` and `1 - T + β*k*c = 0`, with `k = exp (a - b/T)`.
This algebraic predicate uses real division, including at `T = 0`. -/
@[expose] public def IsSteadyState (a b β : ℝ) (p : ℝ × ℝ) : Prop :=
  1 - p.1 - Real.exp (a - b / p.2) * p.1 = 0 ∧
    1 - p.2 + β * Real.exp (a - b / p.2) * p.1 = 0

/-- The fraction `k(T)/(1+k(T))` in the scalar temperature equation. -/
private noncomputable def fraction (a b T : ℝ) : ℝ :=
  Real.exp (a - b / T) / (1 + Real.exp (a - b / T))

private lemma fraction_mem_Ioo (a b T : ℝ) : fraction a b T ∈ Set.Ioo 0 1 := by
  have hk := Real.exp_pos (a - b / T)
  have hd : 0 < 1 + Real.exp (a - b / T) := by linarith
  exact ⟨div_pos hk hd, (div_lt_one hd).2 (by linarith)⟩

private lemma hasDerivAt_fraction (a b : ℝ) {T : ℝ} (hT : 0 < T) :
    HasDerivAt (fraction a b)
      (b / T ^ 2 * (Real.exp (a - b / T) / (1 + Real.exp (a - b / T)) ^ 2)) T := by
  let k (t : ℝ) := Real.exp (a - b / t)
  have he : HasDerivAt (fun t : ℝ ↦ a - b / t) (b / T ^ 2) T := by
    apply (((hasDerivAt_const T b).fun_div (hasDerivAt_id' T) hT.ne').const_sub a).congr_deriv
    simp [neg_div]
  have hk : HasDerivAt k (k T * (b / T ^ 2)) T := he.exp
  have hd : 1 + k T ≠ 0 := by dsimp [k]; positivity
  apply (hk.fun_div (hk.const_add 1) hd).congr_deriv
  dsimp [k]
  ring

private lemma deriv_fraction_le {a b T : ℝ} (hb : 0 < b) (hT : 1 ≤ T) :
    deriv (fraction a b) T ≤ b / 4 := by
  have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
  rw [(hasDerivAt_fraction a b hT₀).deriv]
  set k := Real.exp (a - b / T)
  have hk : 0 < k := Real.exp_pos _
  have hTsq : 1 ≤ T ^ 2 := by nlinarith [sq_nonneg (T - 1)]
  have hscale : b / T ^ 2 ≤ b := (div_le_iff₀ (sq_pos_of_pos hT₀)).2 (by
    nlinarith only [mul_nonneg hb.le (sub_nonneg.mpr hTsq)])
  have hshape : k / (1 + k) ^ 2 ≤ 1 / 4 := (div_le_iff₀ (by positivity)).2 (by
    nlinarith only [sq_nonneg (k - 1)])
  calc
    _ ≤ b * (1 / 4) := mul_le_mul hscale hshape (by positivity) hb.le
    _ = _ := by ring

/-! ## B. Interval and uniqueness -/

/-- For any real `a`, positive `b` and nonnegative `β`, every pair `(c,T)` solving
`1 - c - k*c = 0` and `1 - T + β*k*c = 0`, with `k = exp (a - b/T)`, has
`1 ≤ T ≤ 1 + β`. In particular `T = 1` when `β = 0`. If also `β * b < 4`, exactly one
such pair exists among all real pairs: its temperature is a root of the scalar equation
and its concentration is `1/(1+k)`. The strict inequality is sufficient, not asserted
necessary. -/
public lemma steady_state_interval_and_uniqueness (a : ℝ) {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) :
    (∀ p : ℝ × ℝ, IsSteadyState a b β p → p.2 ∈ Set.Icc 1 (1 + β)) ∧
    (β * b < 4 → ∃! p : ℝ × ℝ, IsSteadyState a b β p) := by
  let g (T : ℝ) := 1 + β * fraction a b T - T
  have hchar (p : ℝ × ℝ) : IsSteadyState a b β p ↔
      p.1 = 1 / (1 + Real.exp (a - b / p.2)) ∧ g p.2 = 0 := by
    simpa only [IsSteadyState, g, fraction, ← mul_div_assoc] using
      (steady_states_and_energy_invariant a hb hβ).1 p.1 p.2
  have hterm (T : ℝ) : β * fraction a b T ∈ Set.Icc 0 β := by
    obtain ⟨h₀, h₁⟩ := fraction_mem_Ioo a b T
    exact ⟨mul_nonneg hβ h₀.le, (mul_le_mul_of_nonneg_left h₁.le hβ).trans_eq (mul_one β)⟩
  have hbounds (p : ℝ × ℝ) (hp : IsSteadyState a b β p) : p.2 ∈ Set.Icc 1 (1 + β) := by
    have he := ((hchar p).mp hp).2
    dsimp only [g] at he
    obtain ⟨hl, hu⟩ := hterm p.2
    constructor <;> linarith
  refine ⟨hbounds, fun hsmall ↦ ?_⟩
  have hg (T : ℝ) (hT : 1 ≤ T) : HasDerivAt g (β * deriv (fraction a b) T - 1) T := by
    have hf := (hasDerivAt_fraction a b (lt_of_lt_of_le zero_lt_one hT)).differentiableAt
    exact ((hf.hasDerivAt.const_mul β).const_add 1).sub (hasDerivAt_id' T)
  have hcont : ContinuousOn g (Set.Ici 1) := fun T hT ↦ (hg T hT).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn g (Set.Ici 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici _) hcont
    intro T hT
    have hT₁ : 1 ≤ T := interior_subset hT
    rw [(hg T hT₁).deriv]
    linarith only [mul_le_mul_of_nonneg_left (deriv_fraction_le (a := a) hb hT₁) hβ, hsmall]
  have hleft : 0 ≤ g 1 := by dsimp only [g]; linarith only [(hterm 1).1]
  have hright : g (1 + β) ≤ 0 := by dsimp only [g]; linarith only [(hterm (1 + β)).2]
  obtain ⟨T, hT, hz⟩ := intermediate_value_Icc' (show 1 ≤ 1 + β by linarith)
    (hcont.mono fun _ h ↦ h.1) (show (0 : ℝ) ∈ Set.Icc (g (1 + β)) (g 1) from ⟨hright, hleft⟩)
  refine ⟨(1 / (1 + Real.exp (a - b / T)), T), (hchar _).mpr ⟨rfl, hz⟩, ?_⟩
  intro p hp
  obtain ⟨hc, hgp⟩ := (hchar p).mp hp
  have htemp : p.2 = T := hanti.injOn (hbounds p hp).1 hT.1 (hgp.trans hz.symm)
  exact Prod.ext (hc.trans (by rw [htemp])) htemp

end Chemistry.AdiabaticReactor
