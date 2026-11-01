/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Traveling waves of the Fisher–KPP equation

Fisher's equation for the spread of an advantageous allele (Fisher 1937; Kolmogorov, Petrovsky
and Piskunov 1937) is the reaction–diffusion equation

  `∂u/∂t = D ∂²u/∂x² + r u (1 - u)`,

with diffusion coefficient `D > 0` and growth rate `r > 0`. A traveling wave of speed `c` is a
solution `u(x, t) = U(x - c t)`; its profile satisfies the ODE

  `D U'' + c U' + r U (1 - U) = 0`,

and a *front* is a profile with `0 < U < 1`, `U → 1` at `-∞` and `U → 0` at `+∞`.

## Main results

* `hasDerivAt_wave_t`, `hasDerivAt_wave_x`, `hasDerivAt_wave_xx`: a wave profile gives a
  solution `u(x, t) = U(x - c t)` of the PDE.
* `not_eventually_pos_of_sq_lt`: **no front with `c² < 4 r D`** (Murray, *Mathematical
  Biology I*, Section 13.2): if `c² < 4 r D`, a profile that tends to `0` at `+∞` cannot stay
  positive near `+∞`. The proof writes `U = e^{-c z / (2D)} w`, so that
  `D w'' + (r (1 - U) - c² / (4 D)) w = 0`, and compares `w` with a sine (Sturm), which forces a
  sign change of `w`. Hence `not_isFront_of_sq_lt`: fronts of nonnegative speed need
  `c ≥ 2 √(r D)`. The squared bound alone only gives `|c| ≥ 2 √(r D)`; negative speeds are
  not addressed here.
* `isFront_azWave`: **the Ablowitz–Zeppetella explicit front**: for every `C > 0`,
  `U(z) = (1 + C exp (z √(r / (6 D))))⁻²` is a front of speed `c = 5 √(r D / 6)`, which exceeds
  the minimal speed `2 √(r D)`. With `D = r = 1` this is the wave `(1 + C e^{z/√6})⁻²` of speed
  `5/√6` of Ablowitz and Zeppetella (1979); the general case follows by rescaling `z`.

Existence of a front for every `c ≥ 2 √(r D)` (Kolmogorov–Petrovsky–Piskunov 1937) is recorded as
a wanted theorem in `WantedExt/Biology/Dynamics/FisherKPPWanted.lean`.

## References

* R. A. Fisher, *The wave of advance of advantageous genes*, Ann. Eugenics 7 (1937), 355–369.
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

/-- `U` is a traveling-wave profile of speed `c` for `∂u/∂t = D ∂²u/∂x² + r u (1 - u)`: it is
twice differentiable with first derivative `U'` and `U'' = -(c U' + r U (1 - U)) / D`, which for
`D ≠ 0` is the profile equation `D U'' + c U' + r U (1 - U) = 0`. -/
def IsWaveProfile (D r c : ℝ) (U U' : ℝ → ℝ) : Prop :=
  ∀ z, HasDerivAt U (U' z) z ∧
    HasDerivAt U' ((-(c * U' z) - r * U z * (1 - U z)) / D) z

/-- A traveling front of speed `c`: a wave profile with `0 < U < 1`, `U → 1` at `-∞` and
`U → 0` at `+∞`. -/
def IsFront (D r c : ℝ) (U U' : ℝ → ℝ) : Prop :=
  IsWaveProfile D r c U U' ∧ (∀ z, 0 < U z ∧ U z < 1) ∧ Tendsto U atBot (𝓝 1) ∧
    Tendsto U atTop (𝓝 0)

section PDE

variable {D r c : ℝ} {U U' : ℝ → ℝ}

/-- Time derivative of the wave `u(x, t) = U(x - c t)`: `∂u/∂t = -c U'(x - c t)`. -/
theorem hasDerivAt_wave_t (h : IsWaveProfile D r c U U') (x t : ℝ) :
    HasDerivAt (fun s => U (x - c * s)) (-c * U' (x - c * t)) t := by
  have hl : HasDerivAt (fun s => x - c * s) (-c) t := by
    simpa using ((hasDerivAt_id t).const_mul c).const_sub x
  have h' := (h (x - c * t)).1.comp t hl
  rw [Function.comp_def] at h'
  convert h' using 1
  ring

/-- Space derivative of the wave: `∂u/∂x = U'(x - c t)`. -/
theorem hasDerivAt_wave_x (h : IsWaveProfile D r c U U') (x t : ℝ) :
    HasDerivAt (fun y => U (y - c * t)) (U' (x - c * t)) x := by
  exact HasDerivAt.comp_sub_const x (c * t) (h (x - c * t)).1

/-- Second space derivative of the wave; with `hD : D ≠ 0` it gives the PDE
`-c U' = D U'' + r U (1 - U)`, i.e. `∂u/∂t = D ∂²u/∂x² + r u (1 - u)`. -/
theorem hasDerivAt_wave_xx (h : IsWaveProfile D r c U U') (hD : D ≠ 0) (x t : ℝ) :
    ∃ U'' : ℝ, HasDerivAt (fun y => U' (y - c * t)) U'' x ∧
      -c * U' (x - c * t) = D * U'' + r * U (x - c * t) * (1 - U (x - c * t)) := by
  refine ⟨_, HasDerivAt.comp_sub_const x (c * t) (h (x - c * t)).2, ?_⟩
  field_simp
  ring

end PDE

/-- **No traveling wave with `c² < 4 r D`**: if `D, r > 0` and `c² < 4 r D`, a wave profile
tending to `0` at `+∞` is not eventually positive. (This excludes `|c| < 2 √(r D)`, not
`c < 2 √(r D)` for negative `c`.) -/
theorem not_eventually_pos_of_sq_lt {D r c : ℝ} {U U' : ℝ → ℝ} (hD : 0 < D) (hr : 0 < r)
    (hc : c ^ 2 < 4 * r * D) (hU : IsWaveProfile D r c U U') (hlim : Tendsto U atTop (𝓝 0)) :
    ¬ ∀ᶠ z in atTop, 0 < U z := by
  intro hpos
  set δ := 4 * r * D - c ^ 2 with hδ
  have hδpos : 0 < δ := by linarith
  set ε := δ / (8 * r * D) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨Z, hZ⟩ := eventually_atTop.1
    (hpos.and (hlim.eventually (gt_mem_nhds hεpos)))
  -- the comparison frequency
  set k := √(δ / (8 * D ^ 2)) with hk
  have hkpos : 0 < k := Real.sqrt_pos.2 (by positivity)
  have hk2 : k ^ 2 = δ / (8 * D ^ 2) := Real.sq_sqrt (by positivity)
  -- the Liouville transform `w = e^{c z / (2D)} U`
  set μ := c / (2 * D) with hμ
  let w : ℝ → ℝ := fun z => exp (μ * z) * U z
  let w' : ℝ → ℝ := fun z => exp (μ * z) * (μ * U z + U' z)
  let q : ℝ → ℝ := fun z => (r * (1 - U z) - c ^ 2 / (4 * D)) / D
  have hexp : ∀ z, HasDerivAt (fun z => exp (μ * z)) (exp (μ * z) * μ) z := fun z => by
    simpa using ((hasDerivAt_id z).const_mul μ).exp
  have hw : ∀ z, HasDerivAt w (w' z) z := fun z => by
    convert (hexp z).mul (hU z).1 using 1
    simp only [w']
    ring
  have hw' : ∀ z, HasDerivAt w' (-(q z) * w z) z := fun z => by
    convert (hexp z).mul ((((hU z).1).const_mul μ).fun_add (hU z).2) using 1
    simp only [q, w, hμ]
    field_simp
    ring
  -- the comparison sine `s(z) = sin (k (z - Z))`
  let sn : ℝ → ℝ := fun z => sin (k * (z - Z))
  let cs : ℝ → ℝ := fun z => k * cos (k * (z - Z))
  have hlin : ∀ z, HasDerivAt (fun z => k * (z - Z)) k z := fun z => by
    simpa using ((hasDerivAt_id z).sub_const Z).const_mul k
  have hsn : ∀ z, HasDerivAt sn (cs z) z := fun z => by
    convert (hlin z).sin using 1
    simp only [cs]
    ring
  have hcs : ∀ z, HasDerivAt cs (-(k ^ 2) * sn z) z := fun z => by
    convert ((hlin z).cos).const_mul k using 1
    simp only [sn]
    ring
  -- the Wronskian
  let W : ℝ → ℝ := fun z => w' z * sn z - w z * cs z
  have hW : ∀ z, HasDerivAt W ((k ^ 2 - q z) * w z * sn z) z := fun z => by
    convert ((hw' z).mul (hsn z)).sub ((hw z).mul (hcs z)) using 1
    ring
  set b := Z + π / k with hb
  have hZb : Z ≤ b := by rw [hb]; have := div_pos pi_pos hkpos; linarith
  have hanti : AntitoneOn W (Set.Icc Z b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc Z b)
      (fun z _ => (hW z).continuousAt.continuousWithinAt)
      (fun z _ => (hW z).differentiableAt.differentiableWithinAt) fun z hz => ?_
    rw [interior_Icc] at hz
    rw [(hW z).deriv]
    have hzZ : Z ≤ z := hz.1.le
    have hUz := hZ z hzZ
    have hwpos : 0 < w z := mul_pos (exp_pos _) hUz.1
    have hsnn : 0 ≤ sn z := by
      refine sin_nonneg_of_nonneg_of_le_pi (by nlinarith [hz.1]) ?_
      have : z - Z ≤ π / k := by linarith [hz.2]
      calc k * (z - Z) ≤ k * (π / k) := mul_le_mul_of_nonneg_left this hkpos.le
        _ = π := by field_simp
    have hq : k ^ 2 ≤ q z := by
      rw [hk2]
      simp only [q]
      rw [div_le_div_iff₀ (by positivity) hD]
      have : r * U z ≤ r * ε := mul_le_mul_of_nonneg_left hUz.2.le hr.le
      rw [hε] at this
      field_simp at this
      have hD4 : (0 : ℝ) < 4 * D := by positivity
      rw [show r * (1 - U z) - c ^ 2 / (4 * D) = (4 * D * r * (1 - U z) - c ^ 2) / (4 * D) by
        field_simp]
      rw [div_mul_eq_mul_div, le_div_iff₀ hD4]
      nlinarith
    have := mul_nonneg (mul_nonneg (sub_nonneg.2 hq) hwpos.le) hsnn
    nlinarith
  have hWle := hanti ⟨le_rfl, hZb⟩ ⟨hZb, le_rfl⟩ hZb
  have hWZ : W Z = -(w Z * k) := by simp [W, sn, cs]
  have hWb : W b = w b * k := by
    have : k * (b - Z) = π := by rw [hb]; field_simp; ring
    simp [W, sn, cs, this]
  have hwZ : 0 < w Z := mul_pos (exp_pos _) (hZ Z le_rfl).1
  have hwb : 0 < w b := mul_pos (exp_pos _) (hZ b hZb).1
  rw [hWZ, hWb] at hWle
  nlinarith [mul_pos hkpos hwZ, mul_pos hkpos hwb]

/-- A front of speed `c` needs `c² ≥ 4 r D`; for `c ≥ 0` this is `c ≥ 2 √(r D)`. -/
theorem not_isFront_of_sq_lt {D r c : ℝ} {U U' : ℝ → ℝ} (hD : 0 < D) (hr : 0 < r)
    (hc : c ^ 2 < 4 * r * D) : ¬ IsFront D r c U U' := fun h =>
  not_eventually_pos_of_sq_lt hD hr hc h.1 h.2.2.2 (Eventually.of_forall fun z => (h.2.1 z).1)

/-- The rate `κ = √(r / (6 D))` of the Ablowitz–Zeppetella wave. -/
noncomputable def azRate (D r : ℝ) : ℝ := √(r / (6 * D))

/-- The Ablowitz–Zeppetella speed `c = 5 √(r D / 6)` (`5 / √6` when `D = r = 1`). -/
noncomputable def azSpeed (D r : ℝ) : ℝ := 5 * √(r * D / 6)

/-- The Ablowitz–Zeppetella profile `U(z) = (1 + C exp (κ z))⁻²`. -/
noncomputable def azWave (D r C : ℝ) (z : ℝ) : ℝ := (1 + C * exp (azRate D r * z))⁻¹ ^ 2

/-- The derivative of the Ablowitz–Zeppetella profile, `-2 κ C e^{κ z} (1 + C e^{κ z})⁻³`. -/
noncomputable def azWaveDeriv (D r C : ℝ) (z : ℝ) : ℝ :=
  -2 * azRate D r * C * exp (azRate D r * z) * (1 + C * exp (azRate D r * z))⁻¹ ^ 3

private lemma az_hasDerivAt (s C z : ℝ) (hC : 0 < C) :
    HasDerivAt (fun z => (1 + C * exp (s * z))⁻¹ ^ 2)
      (-2 * s * C * exp (s * z) * (1 + C * exp (s * z))⁻¹ ^ 3) z := by
  have hE : 0 < 1 + C * exp (s * z) := by positivity
  have hE0 := hE.ne'
  have h1 : HasDerivAt (fun z => 1 + C * exp (s * z)) (C * (exp (s * z) * s)) z := by
    simpa using (((hasDerivAt_id z).const_mul s).exp.const_mul C).const_add 1
  have h2 := (h1.inv hE0).pow 2
  convert h2 using 1
  norm_num
  field_simp

private lemma az_hasDerivAt2 (s C z : ℝ) (hC : 0 < C) :
    HasDerivAt (fun z => -2 * s * C * exp (s * z) * (1 + C * exp (s * z))⁻¹ ^ 3)
      (-2 * s ^ 2 * (C * exp (s * z)) * (1 + C * exp (s * z))⁻¹ ^ 3 +
        6 * s ^ 2 * (C * exp (s * z)) ^ 2 * (1 + C * exp (s * z))⁻¹ ^ 4) z := by
  have hE : 0 < 1 + C * exp (s * z) := by positivity
  have hE0 := hE.ne'
  have h1 : HasDerivAt (fun z => 1 + C * exp (s * z)) (C * (exp (s * z) * s)) z := by
    simpa using (((hasDerivAt_id z).const_mul s).exp.const_mul C).const_add 1
  have he : HasDerivAt (fun z => -2 * s * C * exp (s * z))
      (-2 * s * C * (exp (s * z) * s)) z := by
    simpa using ((hasDerivAt_id z).const_mul s).exp.const_mul (-2 * s * C)
  have h2 := he.mul ((h1.inv hE0).pow 3)
  simp only [Pi.pow_apply, Pi.inv_apply] at h2
  convert h2 using 1
  norm_num
  field_simp
  ring

/-- **The Ablowitz–Zeppetella front**: for `D, r, C > 0`, `(1 + C exp (z √(r / (6 D))))⁻²` is a
front of speed `5 √(r D / 6)`. -/
theorem isFront_azWave {D r C : ℝ} (hD : 0 < D) (hr : 0 < r) (hC : 0 < C) :
    IsFront D r (azSpeed D r) (azWave D r C) (azWaveDeriv D r C) := by
  unfold IsFront IsWaveProfile azWave azWaveDeriv
  set s := azRate D r with hs_def
  clear_value s
  have hs : 0 < s := by rw [hs_def, azRate]; positivity
  have hs2 : s ^ 2 = r / (6 * D) := by rw [hs_def, azRate, Real.sq_sqrt (by positivity)]
  have hr6 : r = 6 * D * s ^ 2 := by rw [hs2]; field_simp
  have hc : azSpeed D r = 5 * D * s := by
    rw [azSpeed, show r * D / 6 = (D * s) ^ 2 by rw [hr6]; ring, Real.sqrt_sq (by positivity)]
    ring
  have hw : ∀ z, 1 < 1 + C * exp (s * z) := fun z => by
    have := exp_pos (s * z); nlinarith
  refine ⟨fun z => ⟨az_hasDerivAt s C z hC, ?_⟩, fun z => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hc]
    convert az_hasDerivAt2 s C z hC using 1
    have hE0 := (zero_lt_one.trans (hw z)).ne'
    rw [hr6]
    field_simp
    ring
  · exact pow_pos (inv_pos.2 (zero_lt_one.trans (hw z))) 2
  · exact pow_lt_one₀ (inv_nonneg.2 (zero_lt_one.trans (hw z)).le)
      (inv_lt_one_of_one_lt₀ (hw z)) two_ne_zero
  · have h0 : Tendsto (fun z => exp (s * z)) atBot (𝓝 0) :=
      tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hs)
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add (h0.const_mul C)).inv₀ (by norm_num) |>.pow 2
    simpa using this
  · have h0 : Tendsto (fun z => 1 + C * exp (s * z)) atTop atTop :=
      tendsto_atTop_add_const_left _ 1
        ((tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hs)).const_mul_atTop hC)
    simpa using (tendsto_inv_atTop_zero.comp h0).pow 2

/-- The Ablowitz–Zeppetella speed exceeds the minimal speed: `2 √(r D) < 5 √(r D / 6)`. -/
theorem two_mul_sqrt_lt_azSpeed {D r : ℝ} (hD : 0 < D) (hr : 0 < r) :
    2 * √(r * D) < azSpeed D r := by
  have h1 := Real.sq_sqrt (by positivity : 0 ≤ r * D)
  have h2 := Real.sq_sqrt (by positivity : 0 ≤ r * D / 6)
  have hpos : 0 < r * D := by positivity
  refine lt_of_pow_lt_pow_left₀ 2 (by unfold azSpeed; positivity) ?_
  rw [azSpeed, mul_pow, mul_pow, h1, h2]
  linarith

end MathlibExt.Biology.Dynamics.FisherKPP
