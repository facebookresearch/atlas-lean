/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ColoredPartitionsJensen.SmoothClass
public import Mathlib

/-!
# The Bessel-type main term is in `S_{1/2}`

The colored-partition main term is, up to a constant factor and a factor
`1 + O(e^{−c√n})`, the Bessel-type integral

  `besselInt a z = ∫_{−1}^{1} (1 − t²)^a e^{z t} dt`,   `a = (r+1)/2`,
`z = π √(2r/3) · √(n − r/24)`.


Here, for every `a ≥ 0` and `κ > 0`:

* `inS_besselModel`: `log besselInt a (κ √x) ∈ S_{1/2}` to every order;
* `besselModel_concave`: its second derivative is `≤ −(κ/8) x^{−3/2}` far out;
* the same for the shifted colored model `coloredModel r` (`x ↦ x − r/24`), and its consequence
  `eventually_card_roots_of_coloredModel`.

Route. With `s = 1 − t`, `besselInt a z = e^z N₀(z)`,
`N_j(z) = ∫_0^2 s^j (s(2−s))^a e^{−zs} ds`. Then `N_j' = −N_{j+1}`, so the normalised moments
`M_j = N_j/N₀` satisfy `M_j' = M_j M_1 − M_{j+1}`, and the single estimate `M_j(z) ≤ K_j z^{−j}`
(from `s^j e^{−zs/2} ≤ j! (2/z)^j` and the doubling bound `N₀(z/2) ≤ 2·4^a N₀(z)`) gives
`M_j ∈ S_{−j}` to every order by induction with `InS.of_deriv`. Then
`(log besselInt)' = 1 − M_1 ∈ S_0`,
so `log besselInt ∈ S_1` in `z`, and `InS.comp_sqrt` moves it to `S_{1/2}` in `x`.
-/

open Filter Topology Asymptotics Set MeasureTheory
open scoped fwdDiff Nat

namespace MetaMathlibExt.ColoredPartitionsJensen

@[expose] public section

/-! ### Composition with `x ↦ κ √x` -/

/-- Chain rule for `x ↦ h (κ √x)`. -/
theorem hasDerivAt_comp_sqrt {h : ℝ → ℝ} {h' κ x : ℝ} (hx : 0 < x)
    (hh : HasDerivAt h h' (κ * Real.sqrt x)) :
    HasDerivAt (fun y => h (κ * Real.sqrt y)) (h' * (κ / 2 * x ^ (-(1 / 2) : ℝ))) x := by
  have hs : HasDerivAt (fun y => κ * Real.sqrt y) (κ * (1 / (2 * Real.sqrt x))) x :=
    (Real.hasDerivAt_sqrt hx.ne').const_mul κ
  have hc := hh.comp x hs
  refine hc.congr_deriv ?_
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  field_simp

/-- Threshold for `κ √x > z₀`. -/
theorem lt_mul_sqrt_of_gt {κ z₀ x : ℝ} (hκ : 0 < κ) (hz₀ : 0 ≤ z₀) (hx : (z₀ / κ) ^ 2 < x) :
    z₀ < κ * Real.sqrt x := by
  have h1 : z₀ / κ < Real.sqrt x := by
    have := Real.sqrt_lt_sqrt (sq_nonneg _) hx
    rwa [Real.sqrt_sq (div_nonneg hz₀ hκ.le)] at this
  rw [div_lt_iff₀ hκ] at h1
  linarith

/-- The order-`0` bound transported through `κ √x`. -/
theorem abs_comp_sqrt_le {h : ℝ → ℝ} {γ κ z₀ C x : ℝ} (hκ : 0 < κ) (hz₀ : 0 ≤ z₀) (_hC : 0 ≤ C)
    (hb : ∀ z, z₀ < z → |h z| ≤ C * z ^ γ) (hx : (z₀ / κ) ^ 2 + 1 < x) :
    |h (κ * Real.sqrt x)| ≤ C * κ ^ γ * x ^ (γ / 2) := by
  have hxpos : 0 < x := by nlinarith [sq_nonneg (z₀ / κ)]
  refine (hb _ (lt_mul_sqrt_of_gt hκ hz₀ (by linarith))).trans_eq ?_
  rw [Real.mul_rpow hκ.le (Real.sqrt_nonneg x), Real.sqrt_eq_rpow, ← Real.rpow_mul hxpos.le]
  ring_nf

/-- Smoothness transported through `κ √x`. -/
theorem contDiffOn_comp_sqrt {h : ℝ → ℝ} {κ z₀ : ℝ} {n : ℕ} (hκ : 0 < κ) (hz₀ : 0 ≤ z₀)
    (hs : ContDiffOn ℝ n h (Ioi z₀)) :
    ContDiffOn ℝ n (fun x => h (κ * Real.sqrt x)) (Ioi ((z₀ / κ) ^ 2 + 1)) := by
  have hin : ContDiffOn ℝ n (fun y => κ * Real.sqrt y) (Ioi ((z₀ / κ) ^ 2 + 1)) := fun x hx => by
    have hxpos : 0 < x := by have := hx.out; nlinarith [sq_nonneg (z₀ / κ)]
    exact (contDiffAt_const.mul (Real.contDiffAt_sqrt hxpos.ne')).contDiffWithinAt
  exact hs.comp hin fun x hx => lt_mul_sqrt_of_gt hκ hz₀ (by linarith [hx.out])

/-- **Composition with `κ √x`.** `h ∈ S_γ` (in `z`, order `d`) gives `x ↦ h (κ √x) ∈ S_{γ/2}` (order
`d`). -/
theorem InS.comp_sqrt {κ : ℝ} (hκ : 0 < κ) {d : ℕ} :
    ∀ {γ : ℝ} {h : ℝ → ℝ}, InS γ d h → InS (γ / 2) d (fun x => h (κ * Real.sqrt x)) := by
  induction d with
  | zero =>
    intro γ h hh
    obtain ⟨z₀, C, -, hz0, hC, hs, hb⟩ := hh.exists_ge 0
    have hx0 : 0 < (z₀ / κ) ^ 2 + 1 := by positivity
    refine InS.intro (C := C * κ ^ γ) hx0 (contDiffOn_comp_sqrt hκ hz0.le hs) fun k hk x hx => ?_
    obtain rfl : k = 0 := by omega
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero]
    exact abs_comp_sqrt_le hκ hz0.le hC (fun z hz => by
      simpa using hb 0 (Nat.zero_le _) z hz) hx
  | succ d ih =>
    intro γ h hh
    obtain ⟨z₀, C, -, hz0, hC, hs, hb⟩ := hh.exists_ge 0
    have hx0 : 0 < (z₀ / κ) ^ 2 + 1 := by positivity
    have hd : InS ((γ - 1) / 2) d (fun x => deriv h (κ * Real.sqrt x)) := ih hh.deriv_mem
    have hq : InS (-(1 / 2)) d (fun x => κ / 2 * x ^ (-(1 / 2) : ℝ)) :=
      (inS_rpow_self (-(1 / 2)) d).const_mul (κ / 2)
    have hprod := hd.mul hq
    have hder : ∀ x, (z₀ / κ) ^ 2 + 1 < x →
        HasDerivAt (fun y => h (κ * Real.sqrt y))
          (deriv h (κ * Real.sqrt x) * (κ / 2 * x ^ (-(1 / 2) : ℝ))) x := fun x hx => by
      have hxpos : 0 < x := hx0.trans hx
      have hz : z₀ < κ * Real.sqrt x := lt_mul_sqrt_of_gt hκ hz0.le (by linarith)
      exact hasDerivAt_comp_sqrt hxpos
        ((hs.contDiffAt (Ioi_mem_nhds hz)).differentiableAt (by simp)).hasDerivAt
    refine InS.of_deriv (a := (z₀ / κ) ^ 2 + 1) (C₀ := C * κ ^ γ)
      (fun x hx => (hder x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => abs_comp_sqrt_le hκ hz0.le hC (fun z hz => by
        simpa using hb 0 (Nat.zero_le _) z hz) hx) ?_
    refine (hprod.of_eq (by ring)).congr (a := (z₀ / κ) ^ 2 + 1) fun x hx => (hder x hx).deriv.symm

/-! ### A concavity criterion for `a √x + R` -/

/-- `(x^{1/2})'' = −(1/4) x^{−3/2}`. -/
theorem iteratedDeriv_two_sqrt_rpow {x : ℝ} :
    iteratedDeriv 2 (fun x : ℝ => x ^ (1 / 2 : ℝ)) x = -(1 / 4) * x ^ ((1 / 2 : ℝ) - 2) := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  norm_num [descPochhammer_succ_right]

/-- **Concavity from a `√x` main term.** If `Λ = a x^{1/2} + R` on a half-line, `a > 0`, and
`|R''(x)| ≤ C x^{γ−2}` there with `γ < 1/2`, then `Λ''(x) ≤ −(a/8) x^{−3/2}` far out. -/
theorem concave_of_sqrt_main {a γ C x₀ : ℝ} (ha : 0 < a) (hγ : γ < 1 / 2) {Λ R : ℝ → ℝ}
    (hR : ContDiffOn ℝ 2 R (Ioi x₀))
    (hRb : ∀ x, x₀ < x → |iteratedDeriv 2 R x| ≤ C * x ^ (γ - 2))
    (heq : EqOn Λ (fun x => a * x ^ (1 / 2 : ℝ) + R x) (Ioi x₀)) :
    ∀ᶠ x in atTop, iteratedDeriv 2 Λ x ≤ -(a / 8) * x ^ ((1 / 2 : ℝ) - 2) := by
  have ht := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 - γ by linarith)).const_mul C
  rw [mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < a / 8 by linarith)),
    eventually_gt_atTop (max x₀ 0)] with x hsmall hx
  have hx₀ : x₀ < x := lt_of_le_of_lt (le_max_left _ _) hx
  have hxpos : 0 < x := lt_of_le_of_lt (le_max_right _ _) hx
  rw [heq.iteratedDeriv_of_isOpen isOpen_Ioi 2 hx₀]
  have h1 : ContDiffAt ℝ 2 (fun x : ℝ => a * x ^ (1 / 2 : ℝ)) x :=
    contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne hxpos.ne')
  have h2 : ContDiffAt ℝ 2 R x := hR.contDiffAt (Ioi_mem_nhds hx₀)
  rw [iteratedDeriv_fun_add h1 h2,
    iteratedDeriv_const_mul _ (Real.contDiffAt_rpow_const_of_ne hxpos.ne'),
    iteratedDeriv_two_sqrt_rpow]
  have hRx := (abs_le.1 (hRb x hx₀)).2
  have hsplit : C * x ^ (γ - 2) = C * x ^ (-(1 / 2 - γ)) * x ^ ((1 / 2 : ℝ) - 2) := by
    rw [mul_assoc, ← Real.rpow_add hxpos]; ring_nf
  have hP : 0 < x ^ ((1 / 2 : ℝ) - 2) := Real.rpow_pos_of_pos hxpos _
  have := mul_le_mul_of_nonneg_right hsmall.le hP.le
  nlinarith

/-- Concavity survives the shift `x ↦ x − s`, `s ≥ 0`. -/
theorem concave_comp_sub {Λ : ℝ → ℝ} {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s)
    (h : ∀ᶠ x in atTop, iteratedDeriv 2 Λ x ≤ -c * x ^ ((1 / 2 : ℝ) - 2)) :
    ∀ᶠ x in atTop, iteratedDeriv 2 (fun x => Λ (x - s)) x ≤ -c * x ^ ((1 / 2 : ℝ) - 2) := by
  obtain ⟨b, hb⟩ := eventually_atTop.1 h
  filter_upwards [eventually_gt_atTop (max b 0 + s)] with x hx
  have hxs : 0 < x - s := by linarith [le_max_right b 0]
  rw [iteratedDeriv_comp_sub_const]
  refine (hb (x - s) (by linarith [le_max_left b 0])).trans ?_
  have : x ^ ((1 / 2 : ℝ) - 2) ≤ (x - s) ^ ((1 / 2 : ℝ) - 2) :=
    Real.rpow_le_rpow_of_nonpos hxs (by linarith) (by norm_num)
  nlinarith

/-! ### The Laplace-type moments `N_j(z) = ∫_0^2 s^j (s(2−s))^a e^{−zs} ds` -/

/-- The weight `s^a (2 − s)^a` (`= (1 − t²)^a` at `t = 1 − s`). -/
noncomputable def bW (a s : ℝ) : ℝ := s ^ a * (2 - s) ^ a

/-- `N_j(z) = ∫_0^2 s^j (s(2−s))^a e^{−zs} ds`. -/
noncomputable def bN (a : ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..2, (s ^ j * bW a s) * Real.exp (-(z * s))

/-- The normalised moments `M_j = N_j / N_0`. -/
noncomputable def bM (a : ℝ) (j : ℕ) (z : ℝ) : ℝ := bN a j z / bN a 0 z

/-- **The Bessel-type integral** `∫_{−1}^{1} (1 − t²)^a e^{zt} dt`. For `a = ν − 1/2` this is
`√π Γ(ν + 1/2) (z/2)^{−ν} I_ν(z)`. -/
noncomputable def besselInt (a z : ℝ) : ℝ := ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ a * Real.exp (z * t)

section Moments

variable {a : ℝ}

theorem continuous_bW (ha : 0 ≤ a) : Continuous (bW a) := by
  unfold bW
  exact (Real.continuous_rpow_const ha).mul
    ((Real.continuous_rpow_const ha).comp (continuous_const.sub continuous_id))

theorem bW_nonneg {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 2) : 0 ≤ bW a s :=
  mul_nonneg (Real.rpow_nonneg hs.1 _) (Real.rpow_nonneg (by linarith [hs.2]) _)

theorem bW_le (ha : 0 ≤ a) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 2) : bW a s ≤ 2 ^ a * 2 ^ a :=
  mul_le_mul (Real.rpow_le_rpow hs.1 hs.2 ha)
    (Real.rpow_le_rpow (by linarith [hs.2]) (by linarith [hs.1]) ha)
    (Real.rpow_nonneg (by linarith [hs.2]) _) (Real.rpow_nonneg (by norm_num) _)

/-- Differentiation under the integral sign for `z ↦ ∫_0^2 g(s) e^{−zs} ds`. -/
theorem hasDerivAt_laplace {g : ℝ → ℝ} (hg : Continuous g) {G : ℝ}
    (hG : ∀ s ∈ Icc (0 : ℝ) 2, |g s| ≤ G) (z₀ : ℝ) :
    HasDerivAt (fun z => ∫ s in (0 : ℝ)..2, g s * Real.exp (-(z * s)))
      (∫ s in (0 : ℝ)..2, -(s * g s * Real.exp (-(z₀ * s)))) z₀ := by
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG 0 ⟨le_rfl, by norm_num⟩)
  have hcont : ∀ z : ℝ, Continuous fun s => g s * Real.exp (-(z * s)) := fun z => by fun_prop
  have hcont' : ∀ z : ℝ, Continuous fun s => -(s * g s * Real.exp (-(z * s))) := fun z => by
    fun_prop
  have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := 2) (F := fun z s => g s * Real.exp (-(z * s)))
    (F' := fun z s => -(s * g s * Real.exp (-(z * s)))) (x₀ := z₀)
    (bound := fun _ => 2 * G * Real.exp (2 * (|z₀| + 1))) (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (hcont z).aestronglyMeasurable)
    ((hcont z₀).intervalIntegrable 0 2) ((hcont' z₀).aestronglyMeasurable)
    (ae_of_all _ fun s hs z hz => ?_) intervalIntegrable_const
    (ae_of_all _ fun s hs z hz => ?_)
  · exact this.2
  · rw [uIoc_of_le (by norm_num)] at hs
    have hz' : |z| ≤ |z₀| + 1 := by
      have := Metric.mem_ball.1 hz
      rw [Real.dist_eq] at this
      linarith [abs_sub_abs_le_abs_sub z z₀]
    have he : -(z * s) ≤ 2 * (|z₀| + 1) := by
      nlinarith [neg_abs_le z, abs_nonneg z, hs.1, hs.2,
        mul_nonneg (by linarith [neg_abs_le z] : 0 ≤ |z| + z) hs.1.le,
        mul_nonneg (by linarith : 0 ≤ |z₀| + 1 - |z|) hs.1.le,
        mul_nonneg (by linarith [abs_nonneg z₀] : 0 ≤ |z₀| + 1) (by linarith [hs.2] : 0 ≤ 2 - s)]
    rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_mul, abs_of_pos hs.1, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (mul_le_mul hs.2 (hG s ⟨hs.1.le, hs.2⟩) (abs_nonneg _) (by norm_num))
      (Real.exp_le_exp.2 he) (Real.exp_pos _).le (mul_nonneg (by norm_num) hG0)
  · have h1 : HasDerivAt (fun z : ℝ => -(z * s)) (-(1 * s)) z := ((hasDerivAt_id' z).mul_const
      s).neg
    exact (h1.exp.const_mul (g s)).congr_deriv (by ring)

theorem hasDerivAt_bN (ha : 0 ≤ a) (j : ℕ) (z : ℝ) : HasDerivAt (bN a j) (-bN a (j + 1) z) z := by
  have h := hasDerivAt_laplace (g := fun s => s ^ j * bW a s)
    ((continuous_pow j).mul (continuous_bW ha)) (G := 2 ^ j * (2 ^ a * 2 ^ a)) (fun s hs => by
      rw [abs_of_nonneg (mul_nonneg (pow_nonneg hs.1 _) (bW_nonneg hs))]
      exact mul_le_mul (pow_le_pow_left₀ hs.1 hs.2 j) (bW_le ha hs) (bW_nonneg hs)
        (pow_nonneg (by norm_num) _)) z
  refine h.congr_deriv ?_
  rw [bN, ← intervalIntegral.integral_neg]
  congr 1
  funext s
  ring

theorem bN_nonneg (j : ℕ) (z : ℝ) : 0 ≤ bN a j z :=
  intervalIntegral.integral_nonneg (by norm_num) fun s hs =>
    mul_nonneg (mul_nonneg (pow_nonneg hs.1 _) (bW_nonneg hs)) (Real.exp_pos _).le

theorem continuous_bN_integrand (ha : 0 ≤ a) (j : ℕ) (z : ℝ) :
    Continuous fun s : ℝ => (s ^ j * bW a s) * Real.exp (-(z * s)) := by
  have := continuous_bW ha
  fun_prop

theorem bN_zero_pos (ha : 0 ≤ a) (z : ℝ) : 0 < bN a 0 z :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_bN_integrand ha 0 z).intervalIntegrable 0 2) (fun s hs => by
      simp only [pow_zero, one_mul]
      exact mul_pos (mul_pos (Real.rpow_pos_of_pos hs.1 _)
        (Real.rpow_pos_of_pos (by linarith [hs.2]) _)) (Real.exp_pos _)) (by norm_num)

theorem hasDerivAt_bM (ha : 0 ≤ a) (j : ℕ) (z : ℝ) :
    HasDerivAt (bM a j) (bM a j z * bM a 1 z - bM a (j + 1) z) z := by
  have h0 := (bN_zero_pos ha z).ne'
  refine ((hasDerivAt_bN ha j z).div (hasDerivAt_bN ha 0 z) h0).congr_deriv ?_
  simp only [bM, zero_add]
  field_simp
  ring

/-- `s^j e^{−zs} (z/2)^j ≤ j! e^{−(z/2)s}` for `s, z ≥ 0`. -/
theorem pow_mul_exp_le {j : ℕ} {s z : ℝ} (hs : 0 ≤ s) (hz : 0 ≤ z) :
    (z / 2) ^ j * (s ^ j * Real.exp (-(z * s))) ≤ j ! * Real.exp (-(z / 2 * s)) := by
  have h := Real.pow_div_factorial_le_exp (z / 2 * s) (by positivity) j
  have hf : (0 : ℝ) < j ! := by exact_mod_cast Nat.factorial_pos j
  rw [div_le_iff₀ hf] at h
  have hsplit : Real.exp (-(z * s)) = Real.exp (-(z / 2 * s)) * Real.exp (-(z / 2 * s)) := by
    rw [← Real.exp_add]; ring_nf
  calc (z / 2) ^ j * (s ^ j * Real.exp (-(z * s)))
      = (z / 2 * s) ^ j * Real.exp (-(z / 2 * s)) * Real.exp (-(z / 2 * s)) := by
        rw [hsplit, mul_pow]; ring
    _ ≤ (Real.exp (z / 2 * s) * j !) * Real.exp (-(z / 2 * s)) * Real.exp (-(z / 2 * s)) := by
        gcongr
    _ = j ! * Real.exp (-(z / 2 * s)) := by
        rw [mul_comm (Real.exp _) (j ! : ℝ), mul_assoc (j ! : ℝ), ← Real.exp_add]; simp

/-- Step A of the moment bound: `(z/2)^j N_j(z) ≤ j! N_0(z/2)`. -/
theorem bN_le_bN_half (ha : 0 ≤ a) (j : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    (z / 2) ^ j * bN a j z ≤ j ! * bN a 0 (z / 2) := by
  unfold bN
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by norm_num)
    (((continuous_bN_integrand ha j z).const_mul _).intervalIntegrable 0 2)
    (((continuous_bN_integrand ha 0 (z / 2)).const_mul _).intervalIntegrable 0 2) fun s hs => ?_
  have hw := bW_nonneg (a := a) hs
  have := mul_le_mul_of_nonneg_right (pow_mul_exp_le (j := j) hs.1 hz) hw
  calc (z / 2) ^ j * ((s ^ j * bW a s) * Real.exp (-(z * s)))
      = (z / 2) ^ j * (s ^ j * Real.exp (-(z * s))) * bW a s := by ring
    _ ≤ j ! * Real.exp (-(z / 2 * s)) * bW a s := this
    _ = j ! * ((s ^ 0 * bW a s) * Real.exp (-(z / 2 * s))) := by ring

/-- `bW(2u) ≤ 4^a bW(u)` on `[0, 1]`. -/
theorem bW_two_mul_le (ha : 0 ≤ a) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    bW a (2 * u) ≤ 2 ^ a * 2 ^ a * bW a u := by
  unfold bW
  rw [Real.mul_rpow (by norm_num) hu.1, show 2 - 2 * u = 2 * (1 - u) by ring,
    Real.mul_rpow (by norm_num) (by linarith [hu.2])]
  have h1 : (1 - u) ^ a ≤ (2 - u) ^ a :=
    Real.rpow_le_rpow (by linarith [hu.2]) (by linarith) ha
  have h2 : 0 ≤ (2 : ℝ) ^ a * 2 ^ a * u ^ a :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg hu.1 _)
  calc (2 : ℝ) ^ a * u ^ a * (2 ^ a * (1 - u) ^ a) = 2 ^ a * 2 ^ a * u ^ a * (1 - u) ^ a := by ring
    _ ≤ 2 ^ a * 2 ^ a * u ^ a * (2 - u) ^ a := mul_le_mul_of_nonneg_left h1 h2
    _ = 2 ^ a * 2 ^ a * (u ^ a * (2 - u) ^ a) := by ring

/-- Step B, the doubling bound: `N_0(z/2) ≤ 2·4^a N_0(z)` for `z ≥ 0`. -/
theorem bN_half_le (ha : 0 ≤ a) {z : ℝ} (_hz : 0 ≤ z) :
    bN a 0 (z / 2) ≤ 2 * (2 ^ a * 2 ^ a) * bN a 0 z := by
  set D : ℝ := 2 ^ a * 2 ^ a with hD
  have hD0 : 0 ≤ D := mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by
      norm_num) _)
  set f : ℝ → ℝ := fun s => (s ^ 0 * bW a s) * Real.exp (-(z / 2 * s)) with hf
  have hsub : bN a 0 (z / 2) = 2 * ∫ u in (0 : ℝ)..1, f (2 * u) := by
    have := intervalIntegral.smul_integral_comp_mul_left f 2 (a := 0) (b := 1)
    simp only [smul_eq_mul, mul_zero, mul_one] at this
    rw [this]; rfl
  rw [hsub]
  have hstep : ∫ u in (0 : ℝ)..1, f (2 * u) ≤
      ∫ u in (0 : ℝ)..1, D * ((u ^ 0 * bW a u) * Real.exp (-(z * u))) := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((((continuous_bN_integrand ha 0 (z / 2))).comp (continuous_const.mul
          continuous_id)).intervalIntegrable 0 1)
      (((continuous_bN_integrand ha 0 z).const_mul _).intervalIntegrable 0 1) fun u hu => ?_
    simp only [hf, pow_zero, one_mul]
    rw [show z / 2 * (2 * u) = z * u by ring]
    have := mul_le_mul_of_nonneg_right (bW_two_mul_le ha hu) (Real.exp_pos (-(z * u))).le
    linarith
  have hext : ∫ u in (0 : ℝ)..1, (u ^ 0 * bW a u) * Real.exp (-(z * u)) ≤ bN a 0 z :=
    intervalIntegral.integral_mono_interval le_rfl (by norm_num) (by norm_num)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => mul_nonneg (mul_nonneg
        (pow_nonneg hs.1.le _) (bW_nonneg ⟨hs.1.le, hs.2⟩)) (Real.exp_pos _).le)
      ((continuous_bN_integrand ha 0 z).intervalIntegrable 0 2)
  rw [intervalIntegral.integral_const_mul] at hstep
  nlinarith

/-- The moment constant `K_j = j! 2^j · 2·4^a`. -/
noncomputable def bK (a : ℝ) (j : ℕ) : ℝ := j ! * 2 ^ j * (2 * (2 ^ a * 2 ^ a))

theorem bM_nonneg (j : ℕ) (z : ℝ) : 0 ≤ bM a j z := div_nonneg (bN_nonneg j z) (bN_nonneg 0 z)

/-- **The moment bound** `M_j(z) ≤ K_j z^{−j}`, `z > 0`. -/
theorem bM_le (ha : 0 ≤ a) (j : ℕ) {z : ℝ} (hz : 0 < z) : bM a j z ≤ bK a j * z ^ (-(j : ℝ)) := by
  have h0 := bN_zero_pos ha z
  have hD0 : 0 ≤ (2 : ℝ) ^ a * 2 ^ a :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)
  have hf : (0 : ℝ) ≤ j ! := Nat.cast_nonneg _
  have hAB : (z / 2) ^ j * bN a j z ≤ j ! * (2 * (2 ^ a * 2 ^ a) * bN a 0 z) :=
    (bN_le_bN_half ha j hz.le).trans (mul_le_mul_of_nonneg_left (bN_half_le ha hz.le) hf)
  have hzj : 0 < z ^ j := pow_pos hz j
  rw [bM, div_le_iff₀ h0, Real.rpow_neg hz.le, Real.rpow_natCast, bK]
  rw [div_pow] at hAB
  have h2j : (0 : ℝ) < 2 ^ j := pow_pos (by norm_num) j
  have key : bN a j z * z ^ j ≤ j ! * 2 ^ j * (2 * (2 ^ a * 2 ^ a)) * bN a 0 z := by
    have := mul_le_mul_of_nonneg_left hAB h2j.le
    calc bN a j z * z ^ j = 2 ^ j * (z ^ j / 2 ^ j * bN a j z) := by field_simp
      _ ≤ 2 ^ j * (j ! * (2 * (2 ^ a * 2 ^ a) * bN a 0 z)) := this
      _ = _ := by ring
  calc bN a j z = bN a j z * z ^ j * (z ^ j)⁻¹ := by field_simp
    _ ≤ j ! * 2 ^ j * (2 * (2 ^ a * 2 ^ a)) * bN a 0 z * (z ^ j)⁻¹ :=
        mul_le_mul_of_nonneg_right key (inv_nonneg.2 hzj.le)
    _ = _ := by ring

/-- **`M_j ∈ S_{−j}`, to every order.** By induction on the order, from `M_j' = M_j M_1 − M_{j+1}`.
-/
theorem inS_bM (ha : 0 ≤ a) : ∀ (d j : ℕ), InS (-(j : ℝ)) d (bM a j) := by
  intro d
  induction d with
  | zero =>
    intro j
    refine InS.intro (x₀ := 1) (C := bK a j) one_pos ?_ fun k hk x hx => ?_
    · have h : ContDiffOn ℝ 0 (bM a j) (Ioi 1) :=
        contDiffOn_zero.2 fun x _ => (hasDerivAt_bM ha j x).continuousAt.continuousWithinAt
      exact_mod_cast h
    · obtain rfl : k = 0 := by omega
      simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero]
      rw [abs_of_nonneg (bM_nonneg j x)]
      exact bM_le ha j (lt_trans one_pos hx)
  | succ d ih =>
    intro j
    have hprod : InS (-(j : ℝ) - 1) d (fun z => bM a j z * bM a 1 z) :=
      ((ih j).mul (ih 1)).of_eq (by push_cast; ring)
    have hnext : InS (-(j : ℝ) - 1) d (bM a (j + 1)) := (ih (j + 1)).of_eq (by push_cast; ring)
    refine InS.of_deriv (a := 0) (C₀ := bK a j)
      (fun x _ => (hasDerivAt_bM ha j x).differentiableAt.differentiableWithinAt)
      (fun x hx => by rw [abs_of_nonneg (bM_nonneg j x)]; exact bM_le ha j hx) ?_
    exact (hprod.sub hnext).congr (a := 0) fun x _ => (hasDerivAt_bM ha j x).deriv.symm

/-- `besselInt a z = e^z N_0(z)` (substitute `t = 1 − s`). -/
theorem besselInt_eq (_ha : 0 ≤ a) (z : ℝ) : besselInt a z = Real.exp z * bN a 0 z := by
  unfold besselInt bN
  have h := intervalIntegral.integral_comp_sub_left
    (fun t : ℝ => (1 - t ^ 2) ^ a * Real.exp (z * t)) (1 : ℝ) (a := 0) (b := 2)
  simp only [show (1 : ℝ) - 2 = -1 by norm_num, sub_zero] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le (by norm_num)] at hs
  simp only [pow_zero, one_mul, bW]
  rw [show (1 : ℝ) - (1 - s) ^ 2 = s * (2 - s) by ring, Real.mul_rpow hs.1 (by linarith [hs.2]),
    show z * (1 - s) = z + -(z * s) by ring, Real.exp_add]
  ring

theorem besselInt_pos (ha : 0 ≤ a) (z : ℝ) : 0 < besselInt a z := by
  rw [besselInt_eq ha]; exact mul_pos (Real.exp_pos _) (bN_zero_pos ha z)

theorem log_besselInt (ha : 0 ≤ a) (z : ℝ) :
    Real.log (besselInt a z) = z + Real.log (bN a 0 z) := by
  rw [besselInt_eq ha, Real.log_mul (Real.exp_pos _).ne' (bN_zero_pos ha z).ne', Real.log_exp]

theorem bN_zero_le (ha : 0 ≤ a) {z : ℝ} (hz : 0 ≤ z) : bN a 0 z ≤ bN a 0 0 :=
  intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_bN_integrand ha 0 z).intervalIntegrable 0 2)
    ((continuous_bN_integrand ha 0 0).intervalIntegrable 0 2) fun s hs =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hs.1]))
        (mul_nonneg (pow_nonneg hs.1 _) (bW_nonneg hs))

theorem le_bN_zero (ha : 0 ≤ a) {z : ℝ} (hz : 0 ≤ z) :
    Real.exp (-(2 * z)) * bN a 0 0 ≤ bN a 0 z := by
  unfold bN
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by norm_num)
    (((continuous_bN_integrand ha 0 0).const_mul _).intervalIntegrable 0 2)
    ((continuous_bN_integrand ha 0 z).intervalIntegrable 0 2) fun s hs => ?_
  have hw : 0 ≤ s ^ 0 * bW a s := mul_nonneg (pow_nonneg hs.1 _) (bW_nonneg hs)
  have he : Real.exp (-(2 * z)) ≤ Real.exp (-(z * s)) := Real.exp_le_exp.2 (by nlinarith [hs.2])
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
  nlinarith

/-- **`log besselInt ∈ S_1` in `z`**, to every order. -/
theorem inS_logBesselInt (ha : 0 ≤ a) (d : ℕ) : InS 1 d (fun z => Real.log (besselInt a z)) := by
  set L := Real.log (bN a 0 0) with hL
  have hder : ∀ z, HasDerivAt (fun z => z + Real.log (bN a 0 z)) (1 - bM a 1 z) z := fun z =>
    ((hasDerivAt_id' z).add ((hasDerivAt_bN ha 0 z).log (bN_zero_pos ha z).ne')).congr_deriv
      (by simp only [bM, zero_add]; ring)
  have hone : InS (1 - 1) d (fun _ => (1 : ℝ)) :=
    ((inS_rpow_self 0 d).congr (a := 0) fun x _ => Real.rpow_zero x).of_eq (by norm_num)
  have hM1 : InS (1 - 1) d (bM a 1) := (inS_bM ha d 1).mono (by norm_num)
  have hg : InS 1 (d + 1) (fun z => z + Real.log (bN a 0 z)) := by
    refine InS.of_deriv (a := 1) (C₀ := 1 + |L|)
      (fun z _ => (hder z).differentiableAt.differentiableWithinAt) (fun z hz => ?_)
      ((hone.sub hM1).congr (a := 0) fun z _ => (hder z).deriv.symm)
    have hz1 : (1 : ℝ) < z := hz
    have hz0 : 0 ≤ z := by linarith
    have hup : Real.log (bN a 0 z) ≤ L :=
      Real.log_le_log (bN_zero_pos ha z) (bN_zero_le ha hz0)
    have hlo : -(2 * z) + L ≤ Real.log (bN a 0 z) := by
      have := Real.log_le_log (mul_pos (Real.exp_pos _) (bN_zero_pos ha 0)) (le_bN_zero ha hz0)
      rwa [Real.log_mul (Real.exp_pos _).ne' (bN_zero_pos ha 0).ne', Real.log_exp] at this
    rw [Real.rpow_one, abs_le]
    constructor <;> nlinarith [abs_nonneg L, le_abs_self L, neg_abs_le L]
  exact (hg.congr (a := 0) fun z _ => (log_besselInt ha z).symm).of_le (Nat.le_succ d)

end Moments

/-! ### The model in `x`: `log besselInt a (κ √x)` -/

/-- The main-term model `x ↦ log ∫_{−1}^{1} (1 − t²)^a e^{κ √x t} dt`. -/
noncomputable def besselModel (a κ x : ℝ) : ℝ := Real.log (besselInt a (κ * Real.sqrt x))

/-- **`besselModel ∈ S_{1/2}`**, to every order. -/
theorem inS_besselModel {a κ : ℝ} (ha : 0 ≤ a) (hκ : 0 < κ) (d : ℕ) :
    InS (1 / 2) d (besselModel a κ) :=
  ((inS_logBesselInt ha d).comp_sqrt hκ).congr (a := 0) fun _ _ => rfl

/-- **Concavity:** `besselModel'' ≤ −(κ/8) x^{−3/2}` far out. -/
theorem besselModel_concave {a κ : ℝ} (ha : 0 ≤ a) (hκ : 0 < κ) :
    ∀ᶠ x in atTop, iteratedDeriv 2 (besselModel a κ) x ≤ -(κ / 8) * x ^ ((1 / 2 : ℝ) - 2) := by
  set R : ℝ → ℝ := fun x => Real.log (bN a 0 (κ * Real.sqrt x)) with hR
  have hL0 : ∀ z, HasDerivAt (fun z => Real.log (bN a 0 z)) (-1 * bM a 1 z) z := fun z =>
    ((hasDerivAt_bN ha 0 z).log (bN_zero_pos ha z).ne').congr_deriv
      (by simp only [bM, zero_add]; ring)
  have hRd : ∀ x, 0 < x → HasDerivAt R
      (-1 * bM a 1 (κ * Real.sqrt x) * (κ / 2 * x ^ (-(1 / 2) : ℝ))) x := fun x hx =>
    hasDerivAt_comp_sqrt hx (hL0 _)
  have hR' : InS (-1) 1 (deriv R) := by
    have h1 := ((inS_bM ha 1 1).const_mul (-1)).comp_sqrt hκ
    have h2 := (inS_rpow_self (-(1 / 2)) 1).const_mul (κ / 2)
    exact ((h1.mul h2).of_eq (by push_cast; ring)).congr (a := 0) fun x hx => (hRd x hx).deriv.symm
  obtain ⟨x₁, C, -, hx1, -, hs, hb⟩ := hR'.exists_ge 0
  have hR2 : ContDiffOn ℝ 2 R (Ioi x₁) := by
    have h := (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (n := ((1 : ℕ) : WithTop ℕ∞))
      (f := R) isOpen_Ioi).2 ⟨fun x hx => (hRd x (hx1.trans
          hx)).differentiableAt.differentiableWithinAt,
        fun h => absurd h (by simp), hs⟩
    exact_mod_cast h
  refine concave_of_sqrt_main (γ := 0) (C := C) (x₀ := x₁) hκ (by norm_num) hR2 (fun x hx => ?_)
    (fun x hx => ?_)
  · rw [iteratedDeriv_succ']
    exact (hb 1 le_rfl x hx).trans_eq (by norm_num)
  · simp only [besselModel, hR]
    rw [log_besselInt ha, Real.sqrt_eq_rpow]

/-! ### The colored-partition model -/

/-- The leading constant `κ_r = π √(2r/3)`. -/
noncomputable def coloredKappa (r : ℕ) : ℝ := Real.pi * Real.sqrt (2 * r / 3)

theorem coloredKappa_pos {r : ℕ} (hr : 1 ≤ r) : 0 < coloredKappa r := by
  have : (1 : ℝ) ≤ r := by exact_mod_cast hr
  exact mul_pos Real.pi_pos (Real.sqrt_pos.2 (by positivity))

/-- The colored-partition main-term model:
`log ∫_{−1}^{1} (1 − t²)^{(r+1)/2} e^{κ_r √(x − r/24) t} dt`,
`κ_r = π √(2r/3)`. -/
noncomputable def coloredModel (r : ℕ) (x : ℝ) : ℝ :=
  besselModel (((r : ℝ) + 1) / 2) (coloredKappa r) (x - r / 24)

theorem inS_coloredModel {r : ℕ} (hr : 1 ≤ r) (d : ℕ) : InS (1 / 2) d (coloredModel r) :=
  ((inS_besselModel (a := ((r : ℝ) + 1) / 2) (by positivity) (coloredKappa_pos hr) d).comp_add
      (-((r : ℝ) / 24))).congr
    (a := 0) fun x _ => by simp only [coloredModel, sub_eq_add_neg]

theorem coloredModel_concave {r : ℕ} (hr : 1 ≤ r) :
    ∀ᶠ x in atTop, iteratedDeriv 2 (coloredModel r) x ≤
      -(coloredKappa r / 8) * x ^ ((1 / 2 : ℝ) - 2) :=
  concave_comp_sub (by linarith [coloredKappa_pos hr]) (by positivity)
    (besselModel_concave (a := ((r : ℝ) + 1) / 2) (by positivity) (coloredKappa_pos hr))

/-- If `log α(n) = c + coloredModel r n + o(n^{−3d/4})` and `α > 0` eventually, then eventually
the degree-`d` Jensen polynomials of `α` have as many real roots, with multiplicity, as their
degree (`d ≥ 1`). -/
theorem eventually_card_roots_of_coloredModel {r : ℕ} (hr : 1 ≤ r) {α : ℕ → ℝ} {d : ℕ}
    (hd : 1 ≤ d) {c : ℝ} (hα : ∀ᶠ n in atTop, 0 < α n)
    (hε : (fun n : ℕ => Real.log (α n) - (c + coloredModel r n)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((1 / 2 - 2 : ℝ) * d / 2))) :
    ∀ᶠ n in atTop,
      (∑ j ∈ Finset.range (d + 1), Polynomial.C ((d.choose j : ℝ) * α (n + j)) *
          Polynomial.X ^ j).roots.card =
        (∑ j ∈ Finset.range (d + 1), Polynomial.C ((d.choose j : ℝ) * α (n + j)) *
          Polynomial.X ^ j).natDegree := by
  have hconst : InS (1 / 2) d (fun _ => c) :=
    ((inS_rpow (show (0 : ℝ) ≤ 1 / 2 by norm_num) d).const_mul c).congr (a := 0)
      fun x _ => by simp only [Real.rpow_zero, mul_one]
  refine eventually_card_roots_of_InS hd hα (hconst.add (inS_coloredModel hr d)) (by norm_num)
    (by norm_num) (by linarith [coloredKappa_pos hr] : 0 < coloredKappa r / 8) ?_ hε
  filter_upwards [coloredModel_concave hr] with x hx
  rw [iteratedDeriv_const_add (by norm_num) c]
  exact hx

end

end MetaMathlibExt.ColoredPartitionsJensen
