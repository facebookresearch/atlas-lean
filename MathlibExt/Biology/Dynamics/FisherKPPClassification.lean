/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.FisherKPP
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Classification of Fisher–KPP traveling-front speeds

For the Fisher–KPP equation `∂u/∂t = D ∂²u/∂x² + r u (1 - u)` with `D, r > 0`, and fronts in
the normalization of `MathlibExt.Biology.Dynamics.FisherKPP.IsFront` (`0 < U < 1`, `U → 1` at
`-∞`, `U → 0` at `+∞`), the set of front speeds is exactly `[2 √(r D), ∞)`.

## Main results

* `not_isFront_of_nonpos`: **no front of speed `c ≤ 0`**. Along a wave profile the energy
  `E = D U'² / 2 + F(U)`, with `F(u) = r (u² / 2 - u³ / 3)` an antiderivative of `r u (1 - u)`,
  satisfies `E' = -c U'²`, so it is nondecreasing when `c ≤ 0`. Since `F(U) → F(1) = r / 6` at
  `-∞`, `E ≥ r / 6` everywhere; since `F(U) → 0` at `+∞`, `D U'² / 2 ≥ r / 12` eventually, which
  contradicts `U(z + 1) - U(z) → 0` by the mean value theorem. This closes the negative-speed
  gap left by `not_isFront_of_sq_lt`, which only excludes `c² < 4 r D`.
* `not_isFront_of_lt`, `two_mul_sqrt_le_of_isFront`: **no front of speed `c < 2 √(r D)`**, for
  every real `c`; unconditional.
* `strictAnti_azWave`, `azSpeed_mem_frontSpeeds`: the Ablowitz–Zeppetella explicit front is
  strictly decreasing, so it is a front in the strongest (strictly monotone) sense at the speed
  `5 √(r D / 6)`, consistent with the bound.
* `exists_isFront_iff`, `exists_isFront_strictAnti_iff`, `frontSpeeds_eq_Ici`,
  `isLeast_frontSpeeds`: **the full classification**: a front of speed `c` exists iff
  `2 √(r D) ≤ c`, and `2 √(r D)` is the minimal front speed.

## Existence is a hypothesis

The existence half (Kolmogorov–Petrovsky–Piskunov 1937: a strictly decreasing front exists at
every speed `c ≥ 2 √(r D)`) is the statement of the wanted theorem
`MathlibExt.Biology.Dynamics.FisherKPP.exists_isFront_of_le` in
`WantedExt/Biology/Dynamics/FisherKPPWanted.lean`, proved in a separate development. The
classification theorems take it as the explicit hypothesis

  `hKPP : ∀ c, 2 * √(r * D) ≤ c → ∃ U U' : ℝ → ℝ, IsFront D r c U U' ∧ StrictAnti U`,

which is that theorem with `hD` and `hr` fixed; it is discharged by
`fun c hc => exists_isFront_of_le hD hr hc` once that theorem is available.

## References

* A. Kolmogorov, I. Petrovsky and N. Piskunov, *Étude de l'équation de la diffusion avec
  croissance de la quantité de matière et son application à un problème biologique*, Bull.
  Univ. État Moscou Sér. Int. A 1 (1937), 1–26.
* M. J. Ablowitz and A. Zeppetella, *Explicit solutions of Fisher's equation for a special wave
  speed*, Bull. Math. Biol. 41 (1979), 835–840.
* J. D. Murray, *Mathematical Biology I: An Introduction*, 3rd ed., Springer, 2002, Section 13.2.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Biology.Dynamics.FisherKPP

open Real Filter Topology

/-- **No wave of nonpositive speed connects `1` to `0`**: for `D, r > 0` and `c ≤ 0`, a wave
profile cannot tend to `1` at `-∞` and to `0` at `+∞`. No sign condition on `U` is needed. -/
theorem not_tendsto_of_nonpos {D r c : ℝ} {U U' : ℝ → ℝ} (hD : 0 < D) (hr : 0 < r)
    (hc : c ≤ 0) (hU : IsWaveProfile D r c U U') (hbot : Tendsto U atBot (𝓝 1))
    (htop : Tendsto U atTop (𝓝 0)) : False := by
  -- the potential `F` and the energy `E`
  let F : ℝ → ℝ := fun u => r * (u ^ 2 / 2 - u ^ 3 / 3)
  let E : ℝ → ℝ := fun z => D * U' z ^ 2 / 2 + F (U z)
  have hF : Continuous F := by fun_prop
  have hE : ∀ z, HasDerivAt E (-c * U' z ^ 2) z := fun z => by
    have h1 := (hU z).1
    have h2 := (hU z).2
    have hsq := (h2.pow 2).const_mul D |>.div_const 2
    have hpot : HasDerivAt (fun z => F (U z))
        (r * (2 * U z ^ 1 * U' z / 2 - 3 * U z ^ 2 * U' z / 3)) z := by
      have := (((h1.pow 2).div_const 2).sub ((h1.pow 3).div_const 3)).const_mul r
      simpa [F] using this
    convert hsq.add hpot using 1
    field_simp
    ring
  have hmono : Monotone E := monotone_of_hasDerivAt_nonneg hE fun z => by
    have := sq_nonneg (U' z)
    simp only [Pi.zero_apply]
    nlinarith
  -- `E ≥ r / 6` everywhere, from the limit at `-∞`
  have hFbot : Tendsto (fun z => F (U z)) atBot (𝓝 (r / 6)) := by
    have := (hF.tendsto 1).comp hbot
    have h1 : F 1 = r / 6 := by simp only [F]; ring
    rwa [h1] at this
  have hElow : ∀ z, r / 6 ≤ E z := fun z => by
    refine le_of_tendsto hFbot ?_
    filter_upwards [eventually_le_atBot z] with y hy
    have h := hmono hy
    have : 0 ≤ D * U' y ^ 2 / 2 := by positivity
    simp only [E] at h ⊢
    linarith
  -- near `+∞`, `D U'² / 2 > r / 12`
  have hFtop : Tendsto (fun z => F (U z)) atTop (𝓝 0) := by
    have := (hF.tendsto 0).comp htop
    have h0 : F 0 = 0 := by simp [F]
    rwa [h0] at this
  obtain ⟨Z, hZ⟩ := eventually_atTop.1 (hFtop.eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < r / 12)))
  have hU'big : ∀ z, Z ≤ z → r / 12 < D * U' z ^ 2 / 2 := fun z hz => by
    have := hElow z
    have := hZ z hz
    simp only [E] at *
    linarith
  -- but `U (z + 1) - U z → 0`
  have hdiff : Tendsto (fun z => D * (U (z + 1) - U z) ^ 2 / 2) atTop (𝓝 0) := by
    have hshift : Tendsto (fun z => U (z + 1)) atTop (𝓝 0) :=
      htop.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)
    have := ((hshift.sub htop).pow 2).const_mul D |>.div_const 2
    simpa using this
  obtain ⟨Z', hZ'⟩ := eventually_atTop.1 (hdiff.eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < r / 12)))
  set z := max Z Z' with hz
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope U U' (lt_add_one z)
    (fun y _ => (hU y).1.continuousAt.continuousWithinAt) fun y _ => (hU y).1
  rw [add_sub_cancel_left, div_one] at hξeq
  have h1 := hU'big ξ (le_trans (le_max_left _ _) hξ.1.le)
  have h2 := hZ' z (le_max_right _ _)
  rw [← hξeq] at h2
  linarith

/-- **No front of nonpositive speed**: for `D, r > 0` and `c ≤ 0`, `IsFront D r c` is empty. -/
theorem not_isFront_of_nonpos {D r c : ℝ} {U U' : ℝ → ℝ} (hD : 0 < D) (hr : 0 < r)
    (hc : c ≤ 0) : ¬ IsFront D r c U U' := fun h =>
  not_tendsto_of_nonpos hD hr hc h.1 h.2.2.1 h.2.2.2

/-- **No front below the minimal speed**: for `D, r > 0` and every real `c < 2 √(r D)`,
`IsFront D r c` is empty. Combines `not_isFront_of_nonpos` (`c ≤ 0`) with
`not_isFront_of_sq_lt` (`0 < c < 2 √(r D)`). -/
theorem not_isFront_of_lt {D r c : ℝ} {U U' : ℝ → ℝ} (hD : 0 < D) (hr : 0 < r)
    (hc : c < 2 * √(r * D)) : ¬ IsFront D r c U U' := by
  rcases le_or_gt c 0 with h0 | h0
  · exact not_isFront_of_nonpos hD hr h0
  · refine not_isFront_of_sq_lt hD hr ?_
    have hs := Real.sq_sqrt (by positivity : 0 ≤ r * D)
    have := pow_lt_pow_left₀ hc h0.le two_ne_zero
    nlinarith

/-- Every front speed is at least the minimal speed `2 √(r D)`. -/
theorem two_mul_sqrt_le_of_isFront {D r c : ℝ} {U U' : ℝ → ℝ} (hD : 0 < D) (hr : 0 < r)
    (h : IsFront D r c U U') : 2 * √(r * D) ≤ c :=
  not_lt.1 fun hc => not_isFront_of_lt hD hr hc h

/-- The Ablowitz–Zeppetella profile `(1 + C exp (κ z))⁻²` is strictly decreasing for `C > 0`
and `D, r > 0`. -/
theorem strictAnti_azWave {D r C : ℝ} (hD : 0 < D) (hr : 0 < r) (hC : 0 < C) :
    StrictAnti (azWave D r C) := by
  have hs : 0 < azRate D r := by rw [azRate]; positivity
  intro x y hxy
  have hexp : exp (azRate D r * x) < exp (azRate D r * y) :=
    exp_lt_exp.2 (mul_lt_mul_of_pos_left hxy hs)
  have hx : 0 < 1 + C * exp (azRate D r * x) := by positivity
  have hlt : 1 + C * exp (azRate D r * x) < 1 + C * exp (azRate D r * y) := by
    have := mul_lt_mul_of_pos_left hexp hC
    linarith
  unfold azWave
  exact pow_lt_pow_left₀ ((inv_lt_inv₀ (hx.trans hlt) hx).2 hlt) (by positivity) two_ne_zero

/-- The Ablowitz–Zeppetella speed is a front speed, witnessed by a strictly decreasing front;
this needs no existence hypothesis. -/
theorem azSpeed_mem_frontSpeeds {D r : ℝ} (hD : 0 < D) (hr : 0 < r) :
    azSpeed D r ∈ {c | ∃ U U' : ℝ → ℝ, IsFront D r c U U' ∧ StrictAnti U} :=
  ⟨azWave D r 1, azWaveDeriv D r 1, isFront_azWave hD hr one_pos,
    strictAnti_azWave hD hr one_pos⟩

/-- Front speeds lie in `[2 √(r D), ∞)`, unconditionally. -/
theorem frontSpeeds_subset_Ici {D r : ℝ} (hD : 0 < D) (hr : 0 < r) :
    {c | ∃ U U' : ℝ → ℝ, IsFront D r c U U'} ⊆ Set.Ici (2 * √(r * D)) := fun _ ⟨_, _, h⟩ =>
  two_mul_sqrt_le_of_isFront hD hr h

/-- **Classification of Fisher–KPP front speeds**: given the KPP existence theorem `hKPP`
(fronts, strictly decreasing, at every speed `c ≥ 2 √(r D)`), a front of speed `c` exists iff
`2 √(r D) ≤ c`, for every real `c`. -/
theorem exists_isFront_iff {D r : ℝ} (hD : 0 < D) (hr : 0 < r)
    (hKPP : ∀ c, 2 * √(r * D) ≤ c → ∃ U U' : ℝ → ℝ, IsFront D r c U U' ∧ StrictAnti U)
    (c : ℝ) : (∃ U U' : ℝ → ℝ, IsFront D r c U U') ↔ 2 * √(r * D) ≤ c := by
  refine ⟨fun ⟨_, _, h⟩ => two_mul_sqrt_le_of_isFront hD hr h, fun hc => ?_⟩
  obtain ⟨U, U', h, -⟩ := hKPP c hc
  exact ⟨U, U', h⟩

/-- **Classification, strictly monotone fronts**: given `hKPP`, a strictly decreasing front of
speed `c` exists iff `2 √(r D) ≤ c`. -/
theorem exists_isFront_strictAnti_iff {D r : ℝ} (hD : 0 < D) (hr : 0 < r)
    (hKPP : ∀ c, 2 * √(r * D) ≤ c → ∃ U U' : ℝ → ℝ, IsFront D r c U U' ∧ StrictAnti U)
    (c : ℝ) : (∃ U U' : ℝ → ℝ, IsFront D r c U U' ∧ StrictAnti U) ↔ 2 * √(r * D) ≤ c :=
  ⟨fun ⟨_, _, h, _⟩ => two_mul_sqrt_le_of_isFront hD hr h, hKPP c⟩

/-- **The set of front speeds is `[2 √(r D), ∞)`**, given `hKPP`. -/
theorem frontSpeeds_eq_Ici {D r : ℝ} (hD : 0 < D) (hr : 0 < r)
    (hKPP : ∀ c, 2 * √(r * D) ≤ c → ∃ U U' : ℝ → ℝ, IsFront D r c U U' ∧ StrictAnti U) :
    {c | ∃ U U' : ℝ → ℝ, IsFront D r c U U'} = Set.Ici (2 * √(r * D)) :=
  Set.ext fun c => exists_isFront_iff hD hr hKPP c

/-- **`2 √(r D)` is the minimal front speed**, given `hKPP`. -/
theorem isLeast_frontSpeeds {D r : ℝ} (hD : 0 < D) (hr : 0 < r)
    (hKPP : ∀ c, 2 * √(r * D) ≤ c → ∃ U U' : ℝ → ℝ, IsFront D r c U U' ∧ StrictAnti U) :
    IsLeast {c | ∃ U U' : ℝ → ℝ, IsFront D r c U U'} (2 * √(r * D)) := by
  rw [frontSpeeds_eq_Ici hD hr hKPP]
  exact isLeast_Ici

end MathlibExt.Biology.Dynamics.FisherKPP
