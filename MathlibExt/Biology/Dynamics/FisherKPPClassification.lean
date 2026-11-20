/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.FisherKPP
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.Gronwall
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
* `IsClosedFront`, `isFront_of_isClosedFront`: the same results for fronts with the
  closed bounds `0 ≤ U ≤ 1`; by uniqueness at the equilibria a closed front is a
  strict front, so it inherits the speed bound, the nonpositive-speed exclusion, and
  the subcritical oscillation statement with its exact complex characteristic roots.

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

/-- A closed traveling front of speed `c`: a wave profile with `0 ≤ U ≤ 1`,
`U → 1` at `-∞` and `U → 0` at `+∞`. This is `IsFront` with the strict
inequalities relaxed to the closed interval. -/
def IsClosedFront (D r c : ℝ) (U U' : ℝ → ℝ) : Prop :=
  IsWaveProfile D r c U U' ∧ (∀ z, 0 ≤ U z ∧ U z ≤ 1) ∧ Tendsto U atBot (𝓝 1) ∧
    Tendsto U atTop (𝓝 0)

/-- Uniqueness at an equilibrium for the profile ODE: a profile bounded by `2`
in absolute value that agrees with the equilibrium state `(e, 0)`, `e ∈ {0, 1}`,
at one point is the constant equilibrium `U ≡ e`. -/
theorem eq_const_of_isWaveProfile_of_apply_eq {D r c e : ℝ} {U U' : ℝ → ℝ}
    (hD : 0 < D) (he : e = 0 ∨ e = 1) (hU : IsWaveProfile D r c U U')
    (hbound : ∀ z, |U z| ≤ 2) {z₀ : ℝ} (h0 : U z₀ = e) (h0' : U' z₀ = 0) :
    ∀ z, U z = e ∧ U' z = 0 := by
  have he01 : e * (1 - e) = 0 := by rcases he with rfl | rfl <;> norm_num
  have heabs : |e| ≤ 1 := by rcases he with rfl | rfl <;> norm_num
  have hnl : ∀ z, |U z * (1 - U z)| ≤ 4 * |U z - e| := by
    intro z
    have hfact : U z * (1 - U z) = (U z - e) * (1 - U z - e) := by
      linear_combination he01
    have hfac : |1 - U z - e| ≤ 4 := by
      have h3 : (1 : ℝ) - U z - e = (1 - U z) + (-e) := by ring
      have h4 : |(1 : ℝ) - U z| ≤ 1 + |U z| := by
        have h := abs_sub (1 : ℝ) (U z)
        simpa using h
      have h5 := abs_add_le (1 - U z) (-e)
      rw [← h3] at h5
      simp only [abs_neg] at h5
      linarith [h4, h5, hbound z, heabs]
    rw [hfact, abs_mul]
    exact (mul_le_mul_of_nonneg_left hfac (abs_nonneg _)).trans_eq (mul_comm _ _)
  set f : ℝ → ℝ × ℝ := fun z => (U z - e, U' z) with hf_def
  set f' : ℝ → ℝ × ℝ := fun z => (U' z, (-(c * U' z) - r * U z * (1 - U z)) / D) with hf'_def
  have hfderiv : ∀ z, HasDerivAt f (f' z) z := by
    intro z
    have h1 : HasDerivAt (fun z => U z - e) (U' z) z := (hU z).1.sub_const e
    exact h1.prodMk (hU z).2
  have hfcont : Continuous f :=
    continuous_iff_continuousAt.mpr fun z => (hfderiv z).continuousAt
  set K : ℝ := max 1 ((|c| + 4 * |r|) / D) with hK_def
  have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
  have hbound' : ∀ z, ‖f' z‖ ≤ K * ‖f z‖ := by
    intro z
    have hfn : ‖f z‖ = max |U z - e| |U' z| := by
      change ‖(U z - e, U' z)‖ = max |U z - e| |U' z|
      rw [Prod.norm_mk]; simp [Real.norm_eq_abs]
    have hf'n : ‖f' z‖ = max |U' z| (|-(c * U' z) - r * U z * (1 - U z)| / |D|) := by
      change ‖(U' z, (-(c * U' z) - r * U z * (1 - U z)) / D)‖ = _
      rw [Prod.norm_mk]; simp [Real.norm_eq_abs]
    have hw : |U z - e| ≤ ‖f z‖ := hfn.symm ▸ le_max_left _ _
    have ha : |U' z| ≤ ‖f z‖ := hfn.symm ▸ le_max_right _ _
    have hnum : |-(c * U' z) - r * U z * (1 - U z)| ≤ (|c| + 4 * |r|) * ‖f z‖ := by
      calc |-(c * U' z) - r * U z * (1 - U z)|
          ≤ |c| * |U' z| + |r| * |U z * (1 - U z)| := by
            have h := abs_add_le (-(c * U' z)) (-(r * U z * (1 - U z)))
            have e1 : -(c * U' z) + -(r * U z * (1 - U z))
                = -(c * U' z) - r * U z * (1 - U z) := by ring
            rw [e1] at h
            simpa [abs_neg, abs_mul, mul_assoc] using h
        _ ≤ |c| * ‖f z‖ + |r| * (4 * |U z - e|) :=
            add_le_add (mul_le_mul_of_nonneg_left ha (abs_nonneg _))
              (mul_le_mul_of_nonneg_left (hnl z) (abs_nonneg _))
        _ ≤ (|c| + 4 * |r|) * ‖f z‖ := by
            have h2 : |r| * (4 * |U z - e|) ≤ 4 * |r| * ‖f z‖ := by
              have h3 := mul_le_mul_of_nonneg_left hw (by positivity : (0:ℝ) ≤ 4 * |r|)
              linarith [h3]
            rw [add_mul]
            linarith [h2]
    have hsecond : |-(c * U' z) - r * U z * (1 - U z)| / |D| ≤ K * ‖f z‖ := by
      rw [abs_of_pos hD, div_le_iff₀ hD]
      calc |-(c * U' z) - r * U z * (1 - U z)| ≤ (|c| + 4 * |r|) * ‖f z‖ := hnum
        _ ≤ (K * D) * ‖f z‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            have hle : (|c| + 4 * |r|) / D ≤ K := le_max_right _ _
            rwa [div_le_iff₀ hD] at hle
        _ = K * ‖f z‖ * D := by ring
    rw [hf'n]
    refine max_le ?_ hsecond
    calc |U' z| ≤ ‖f z‖ := ha
      _ ≤ K * ‖f z‖ := le_mul_of_one_le_left (norm_nonneg _) hK1
  have hz0 : f z₀ = 0 := by
    change (U z₀ - e, U' z₀) = (0, 0)
    rw [h0, h0']; simp
  intro z
  have hfz : f z = 0 := by
    rcases le_total z₀ z with hle | hle
    · exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hfcont.continuousOn
        (fun x _ => (hfderiv x).hasDerivWithinAt) hz0 (fun x _ => hbound' x)
        z ⟨hle, le_rfl⟩
    · have hgderiv : ∀ t, HasDerivAt (fun t => f (-t)) (- f' (-t)) t := by
        intro t
        have h1 : HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℝ (f' (-t))) (-t) :=
          hasDerivAt_iff_hasFDerivAt.mp (hfderiv (-t))
        have h2 : HasFDerivAt Neg.neg (ContinuousLinearMap.toSpanSingleton ℝ (-1 : ℝ)) t :=
          hasDerivAt_iff_hasFDerivAt.mp (hasDerivAt_neg t)
        have h3 := h1.comp t h2
        rw [hasDerivAt_iff_hasFDerivAt]
        convert h3 using 1
        · funext s
          rfl
        · apply ContinuousLinearMap.ext
          intro v
          simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
            smul_eq_mul, smul_neg, mul_neg, mul_one, neg_smul]
      have hg := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
        (a := -z₀) (b := -z) (f := fun t => f (-t)) (f' := fun t => - f' (-t))
        (hfcont.comp continuous_neg).continuousOn (fun x _ => (hgderiv x).hasDerivWithinAt)
        (by simpa using hz0)
        (fun x _ => by change ‖- f' (-x)‖ ≤ K * ‖f (-x)‖; rw [norm_neg]; exact hbound' (-x))
        (-z) ⟨by linarith, le_rfl⟩
      simpa using hg
  have h1 : U z - e = 0 := congrArg Prod.fst hfz
  have h2 : U' z = 0 := congrArg Prod.snd hfz
  exact ⟨sub_eq_zero.mp h1, h2⟩

/-- **A closed front is a strict front.** The values `0` and `1` cannot be
attained at any finite point. -/
theorem isFront_of_isClosedFront {D r c : ℝ} {U U' : ℝ → ℝ} (hD : 0 < D)
    (h : IsClosedFront D r c U U') : IsFront D r c U U' := by
  obtain ⟨hprof, h01, hbot, htop⟩ := h
  have hbound : ∀ z, |U z| ≤ 2 := fun z => by
    rw [abs_of_nonneg (h01 z).1]; linarith [(h01 z).2]
  refine ⟨hprof, fun z => ⟨?_, ?_⟩, hbot, htop⟩
  · refine (h01 z).1.lt_of_ne (fun hz0 => ?_)
    -- hz0 : 0 = U z
    have hz0' : U z = 0 := hz0.symm
    have hder0 : U' z = 0 := by
      have hmin : IsLocalMin U z :=
        Filter.Eventually.of_forall fun x => by rw [hz0']; exact (h01 x).1
      exact IsLocalExtr.hasDerivAt_eq_zero (Or.inl hmin) (hprof z).1
    have hconst := eq_const_of_isWaveProfile_of_apply_eq hD (Or.inl rfl) hprof
      hbound hz0' hder0
    have hU0 : U = fun _ => 0 := funext fun t => (hconst t).1
    rw [hU0] at hbot
    exact one_ne_zero (tendsto_nhds_unique hbot tendsto_const_nhds)
  · refine (h01 z).2.lt_of_ne (fun hz1 => ?_)
    have hz1' : U z = 1 := hz1
    have hder0 : U' z = 0 := by
      have hmax : IsLocalMax U z :=
        Filter.Eventually.of_forall fun x => by rw [hz1']; exact (h01 x).2
      exact IsLocalExtr.hasDerivAt_eq_zero (Or.inr hmax) (hprof z).1
    have hconst := eq_const_of_isWaveProfile_of_apply_eq hD (Or.inr rfl) hprof
      hbound hz1' hder0
    have hU1 : U = fun _ => 1 := funext fun t => (hconst t).1
    rw [hU1] at htop
    exact one_ne_zero (tendsto_nhds_unique htop tendsto_const_nhds).symm

/-- **Positivity forces `c ≥ 2 √(r D)`, closed-interval form.** Every closed
front speed is at least the minimal speed. -/
theorem two_mul_sqrt_le_of_isClosedFront {D r c : ℝ} {U U' : ℝ → ℝ} (hD : 0 < D)
    (hr : 0 < r) (h : IsClosedFront D r c U U') : 2 * √(r * D) ≤ c :=
  two_mul_sqrt_le_of_isFront hD hr (isFront_of_isClosedFront hD h)

/-- **No closed front of nonpositive speed** (the energy argument). -/
theorem not_isClosedFront_of_nonpos {D r c : ℝ} {U U' : ℝ → ℝ} (hD : 0 < D)
    (hr : 0 < r) (hc : c ≤ 0) : ¬ IsClosedFront D r c U U' := fun h =>
  not_tendsto_of_nonpos hD hr hc h.1 h.2.2.1 h.2.2.2

/-- **Oscillation below the minimal speed.** If `c² < 4 r D`, a wave profile
tending to `0` at `+∞` takes a nonpositive value arbitrarily far out. -/
theorem exists_le_forall_of_sq_lt {D r c : ℝ} {U U' : ℝ → ℝ} (hD : 0 < D)
    (hr : 0 < r) (hc : c ^ 2 < 4 * r * D) (hU : IsWaveProfile D r c U U')
    (hlim : Tendsto U atTop (𝓝 0)) : ∀ Z : ℝ, ∃ z ≥ Z, U z ≤ 0 := by
  have h := not_eventually_pos_of_sq_lt hD hr hc hU hlim
  rw [Filter.not_eventually, frequently_atTop] at h
  intro Z
  obtain ⟨z, hz, hzU⟩ := h Z
  exact ⟨z, hz, le_of_not_gt hzU⟩

/-- **Linearization roots at `U = 0`.** When `c² < 4 r D`, the characteristic
polynomial `D w² + c w + r` of the linearized profile equation has exactly the
two complex roots `(-c ± i √(4 r D - c²)) / (2 D)`. -/
theorem charRoot_iff_of_sq_lt {D r c : ℝ} (hD : 0 < D) (hr : 0 < r)
    (hc : c ^ 2 < 4 * r * D) (w : ℂ) :
    (D : ℂ) * w ^ 2 + (c : ℂ) * w + (r : ℂ) = 0 ↔
      w = (-(c : ℂ) + (Real.sqrt (4 * r * D - c ^ 2) : ℂ) * Complex.I) / (2 * (D : ℂ)) ∨
        w = (-(c : ℂ) - (Real.sqrt (4 * r * D - c ^ 2) : ℂ) * Complex.I) / (2 * (D : ℂ)) := by
  set s : ℝ := Real.sqrt (4 * r * D - c ^ 2) with hs
  have hs2 : s ^ 2 = 4 * r * D - c ^ 2 := Real.sq_sqrt (by have h := mul_pos hr hD; linarith)
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hfact : (D : ℂ) * w ^ 2 + (c : ℂ) * w + (r : ℂ)
      = (D : ℂ) * (w - (-(c : ℂ) + (s : ℂ) * Complex.I) / (2 * (D : ℂ)))
          * (w - (-(c : ℂ) - (s : ℂ) * Complex.I) / (2 * (D : ℂ))) := by
    have hs2c : (s : ℂ) ^ 2 = 4 * (r : ℂ) * (D : ℂ) - (c : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, hs2]; push_cast; ring
    have hI : Complex.I ^ 2 = -1 := by rw [pow_two]; exact Complex.I_mul_I
    field_simp
    linear_combination -hs2c + (s : ℂ) ^ 2 * hI
  rw [hfact]
  simp [hD0, sub_eq_zero]

/-- Non-vacuity: the Ablowitz–Zeppetella front is a closed front, and the bound
is respected by its speed. -/
theorem isClosedFront_azWave {D r C : ℝ} (hD : 0 < D) (hr : 0 < r) (hC : 0 < C) :
    IsClosedFront D r (azSpeed D r) (azWave D r C) (azWaveDeriv D r C) := by
  have h := isFront_azWave hD hr hC
  exact ⟨h.1, fun z => ⟨(h.2.1 z).1.le, (h.2.1 z).2.le⟩, h.2.2.1, h.2.2.2⟩

/-- A strict front is a closed front. -/
theorem isClosedFront_of_isFront {D r c : ℝ} {U U' : ℝ → ℝ}
    (h : IsFront D r c U U') : IsClosedFront D r c U U' :=
  ⟨h.1, fun z => ⟨(h.2.1 z).1.le, (h.2.1 z).2.le⟩, h.2.2.1, h.2.2.2⟩

/-- **Closed-front speeds are exactly `[2 √(r D), ∞)`**: a closed front of
speed `c` exists iff `2 √(r D) ≤ c`, given `hKPP`. -/
theorem exists_isClosedFront_iff {D r : ℝ} (hD : 0 < D) (hr : 0 < r)
    (hKPP : ∀ c, 2 * √(r * D) ≤ c → ∃ U U' : ℝ → ℝ, IsFront D r c U U' ∧ StrictAnti U)
    (c : ℝ) : (∃ U U' : ℝ → ℝ, IsClosedFront D r c U U') ↔ 2 * √(r * D) ≤ c := by
  refine ⟨fun ⟨_, _, h⟩ => two_mul_sqrt_le_of_isClosedFront hD hr h, fun hc => ?_⟩
  obtain ⟨U, U', h, -⟩ := hKPP c hc
  exact ⟨U, U', isClosedFront_of_isFront h⟩

/-- **The set of closed-front speeds is `[2 √(r D), ∞)`**, given `hKPP`. -/
theorem closedFrontSpeeds_eq_Ici {D r : ℝ} (hD : 0 < D) (hr : 0 < r)
    (hKPP : ∀ c, 2 * √(r * D) ≤ c → ∃ U U' : ℝ → ℝ, IsFront D r c U U' ∧ StrictAnti U) :
    {c | ∃ U U' : ℝ → ℝ, IsClosedFront D r c U U'} = Set.Ici (2 * √(r * D)) :=
  Set.ext fun c => exists_isClosedFront_iff hD hr hKPP c

/-- **`2 √(r D)` is the minimal closed-front speed**, given `hKPP`. -/
theorem isLeast_closedFrontSpeeds {D r : ℝ} (hD : 0 < D) (hr : 0 < r)
    (hKPP : ∀ c, 2 * √(r * D) ≤ c → ∃ U U' : ℝ → ℝ, IsFront D r c U U' ∧ StrictAnti U) :
    IsLeast {c | ∃ U U' : ℝ → ℝ, IsClosedFront D r c U U'} (2 * √(r * D)) := by
  rw [closedFrontSpeeds_eq_Ici hD hr hKPP]
  exact isLeast_Ici

end MathlibExt.Biology.Dynamics.FisherKPP
