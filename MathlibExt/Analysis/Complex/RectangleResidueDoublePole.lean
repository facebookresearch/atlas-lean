/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.RectangleResidue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The residue theorem on a rectangle with double poles, and residues of `-f'/f(s) x^s / s`

We extend the residue theorem on a rectangle to principal parts `r p / (s - p) + d p / (s - p)²`:
the double poles contribute nothing to the boundary integral. We also compute the principal parts
of the integrand `-f'/f(s) x^s / s` of explicit formulas at the zeros of `f` and at `s = 0`.

## Main statements

* `RectilinearRectangle.boundaryIntegral_inv_sub_sq_eq_zero`: the boundary integral of
  `(s - p)⁻²` around a rectangle whose sides avoid `p` vanishes.
* `Complex.exists_differentiableOn_eq_add_sum_div_sub_add_div_sub_sq`: subtracting principal parts
  with double poles leaves a function differentiable on the whole set.
* `RectilinearRectangle.boundaryIntegral_eq_two_pi_mul_I_mul_sum_of_double`: the residue theorem
  for simple and double poles on a rectangle.
* `Complex.exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_zpow`: at a zero `p ≠ 0` of order `k`
  of `f`, the integrand `-f'/f(s) x^s / s` has residue `-k x^p / p`.
* `Complex.exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_ne_zero`: if `f(0) ≠ 0`, the residue
  at `0` is `-f'(0)/f(0)`.
* `Complex.exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_eq_mul`: at a simple zero
  `f = s E(s)` at `0`, the integrand has principal part `-(log x + E'(0)/E(0))/s - 1/s²`.
-/

@[expose] public section

open Filter Topology Set

namespace RectilinearRectangle

/-- The boundary integral of `(s - p)⁻²` around a rectangle whose sides avoid `p` vanishes:
`-(s - p)⁻¹` is a primitive. -/
theorem boundaryIntegral_inv_sub_sq_eq_zero (r : RectilinearRectangle) {p : ℂ}
    (h1 : p.im ≠ r.first.im) (h2 : p.im ≠ r.second.im) (h3 : p.re ≠ r.first.re)
    (h4 : p.re ≠ r.second.re) :
    r.boundaryIntegral (fun s => ((s - p) ^ 2)⁻¹) = 0 := by
  set G : ℂ → ℂ := fun s => -(s - p)⁻¹ with hG
  have hGd : ∀ s : ℂ, s ≠ p → HasDerivAt G (((s - p) ^ 2)⁻¹) s := by
    intro s hs
    have hs' : s - p ≠ 0 := sub_ne_zero.mpr hs
    have h := (((hasDerivAt_id' s).sub_const p).inv hs').neg
    exact h.congr_deriv (by field_simp)
  have horiz : ∀ a b c : ℝ, p.im ≠ c →
      (∫ x : ℝ in a..b, (((x : ℂ) + (c : ℂ) * Complex.I - p) ^ 2)⁻¹) =
        G ((b : ℂ) + c * Complex.I) - G ((a : ℂ) + c * Complex.I) := by
    intro a b c hc
    have hne : ∀ x : ℝ, (x : ℂ) + (c : ℂ) * Complex.I ≠ p := fun x hx => hc (by rw [← hx]; simp)
    have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => G ((x : ℂ) + (c : ℂ) * Complex.I))
        (((x : ℂ) + (c : ℂ) * Complex.I - p) ^ 2)⁻¹ x := by
      intro x
      have hl : HasDerivAt (fun x : ℝ => (x : ℂ) + (c : ℂ) * Complex.I) 1 x :=
        (hasDerivAt_id' (x : ℂ)).comp_ofReal.add_const _
      have h := (hGd _ (hne x)).comp x hl
      exact h.congr_deriv (by ring)
    have hcont : Continuous fun x : ℝ => (((x : ℂ) + (c : ℂ) * Complex.I - p) ^ 2)⁻¹ :=
      Continuous.inv₀ (by fun_prop) fun x => pow_ne_zero 2 (sub_ne_zero.mpr (hne x))
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (hcont.intervalIntegrable _ _)
  have vert : ∀ a b c : ℝ, p.re ≠ c →
      Complex.I • (∫ y : ℝ in a..b, (((c : ℂ) + (y : ℂ) * Complex.I - p) ^ 2)⁻¹) =
        G ((c : ℂ) + b * Complex.I) - G ((c : ℂ) + a * Complex.I) := by
    intro a b c hc
    have hne : ∀ y : ℝ, (c : ℂ) + (y : ℂ) * Complex.I ≠ p := fun y hy => hc (by rw [← hy]; simp)
    have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => G ((c : ℂ) + (y : ℂ) * Complex.I))
        (Complex.I * (((c : ℂ) + (y : ℂ) * Complex.I - p) ^ 2)⁻¹) y := by
      intro y
      have hl : HasDerivAt (fun y : ℝ => (c : ℂ) + (y : ℂ) * Complex.I) Complex.I y :=
        (((hasDerivAt_id' (y : ℂ)).mul_const Complex.I).comp_ofReal.const_add (c : ℂ)).congr_deriv
          (one_mul _)
      have h := (hGd _ (hne y)).comp y hl
      exact h.congr_deriv (by ring)
    have hcont : Continuous fun y : ℝ =>
        Complex.I * (((c : ℂ) + (y : ℂ) * Complex.I - p) ^ 2)⁻¹ :=
      continuous_const.mul (Continuous.inv₀ (by fun_prop)
        fun y => pow_ne_zero 2 (sub_ne_zero.mpr (hne y)))
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
      (hcont.intervalIntegrable _ _)
  simp only [boundaryIntegral]
  rw [horiz _ _ _ h1, horiz _ _ _ h2, vert _ _ _ h4, vert _ _ _ h3]
  ring

end RectilinearRectangle

namespace Complex

/-- **Subtracting principal parts with double poles.** If
`f = r p / (s - p) + d p / (s - p)² + φ_p` near each `p ∈ S` with `φ_p` differentiable at `p`, and
`f` is differentiable within `K` off `S`, then `f = g + ∑_{p ∈ S} (r p / (s - p) + d p / (s - p)²)`
on `K \ S` for some `g` differentiable on `K`. -/
theorem exists_differentiableOn_eq_add_sum_div_sub_add_div_sub_sq (K : Set ℂ) (S : Finset ℂ)
    (r d f : ℂ → ℂ)
    (hloc : ∀ p ∈ S, ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧
      ∀ᶠ s in 𝓝[≠] p, f s = r p / (s - p) + d p / (s - p) ^ 2 + φ s)
    (hdiff : ∀ s ∈ K, s ∉ S → DifferentiableWithinAt ℂ f K s) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g K ∧
      ∀ s ∈ K, s ∉ S → f s = g s + ∑ p ∈ S, (r p / (s - p) + d p / (s - p) ^ 2) := by
  classical
  -- subtract the double poles first, then apply the simple-pole version
  set D : ℂ → ℂ := fun s => ∑ p ∈ S, d p / (s - p) ^ 2 with hD
  have hDd : ∀ s, s ∉ S → DifferentiableAt ℂ D s := by
    intro s hs
    apply DifferentiableAt.fun_sum
    intro q hq
    have : (s - q) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr fun h => hs (h ▸ hq))
    fun_prop (disch := assumption)
  have hloc' : ∀ p ∈ S, ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧
      ∀ᶠ s in 𝓝[≠] p, f s - D s = r p / (s - p) + φ s := by
    intro p hp
    obtain ⟨φ, hφ, hφe⟩ := hloc p hp
    refine ⟨fun s => φ s - ∑ q ∈ S.erase p, d q / (s - q) ^ 2, hφ.sub ?_, ?_⟩
    · apply DifferentiableAt.fun_sum
      intro q hq
      have : (p - q) ^ 2 ≠ 0 :=
        pow_ne_zero 2 (sub_ne_zero.mpr fun h => (Finset.mem_erase.mp hq).1 (h ▸ rfl))
      fun_prop (disch := assumption)
    · filter_upwards [hφe] with s hs
      rw [hs]
      simp only [hD]
      rw [← Finset.add_sum_erase S _ hp]
      ring
  have hdiff' : ∀ s ∈ K, s ∉ S → DifferentiableWithinAt ℂ (fun s => f s - D s) K s :=
    fun s hs hsS => (hdiff s hs hsS).sub (hDd s hsS).differentiableWithinAt
  obtain ⟨g, hg, hfg⟩ := exists_differentiableOn_eq_add_sum_div_sub K S r _ hloc' hdiff'
  refine ⟨g, hg, fun s hs hsS => ?_⟩
  have := hfg s hs hsS
  rw [Finset.sum_add_distrib]
  simp only [hD] at this
  linear_combination this

end Complex

namespace RectilinearRectangle

/-- **The residue theorem on a rectangle, for simple and double poles.** If
`f = g + ∑_{p ∈ S} (r p / (s - p) + d p / (s - p)²)` on the closed rectangle off `S`, with `g`
holomorphic on the closed rectangle and `S` contained in the open rectangle, then the positively
oriented boundary integral of `f` is `2πi ∑_{p ∈ S} r p`: the double poles contribute nothing. -/
theorem boundaryIntegral_eq_two_pi_mul_I_mul_sum_of_double (r : RectilinearRectangle)
    (S : Finset ℂ) (res d f g : ℂ → ℂ)
    (hin : ∀ p ∈ S, r.first.re < p.re ∧ p.re < r.second.re ∧ r.first.im < p.im ∧
      p.im < r.second.im)
    (hg : DifferentiableOn ℂ g r.carrier)
    (hf : ∀ s ∈ r.carrier, s ∉ S → f s = g s + ∑ p ∈ S, (res p / (s - p) + d p / (s - p) ^ 2)) :
    r.boundaryIntegral f = 2 * (Real.pi : ℂ) * Complex.I * ∑ p ∈ S, res p := by
  set z := r.first
  set w := r.second
  have hK : r.carrier = Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im := rfl
  rw [hK] at hg hf
  have side : ∀ (a b : ℝ) (φ : ℝ → ℂ),
      ContinuousOn φ (Set.uIcc a b) →
      (∀ v ∈ Set.uIcc a b, φ v ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) →
      (∀ v ∈ Set.uIcc a b, φ v ∉ S) →
      (∫ v : ℝ in a..b, f (φ v))
        = (∫ v : ℝ in a..b, g (φ v)) + (∑ p ∈ S, res p * ∫ v : ℝ in a..b, (φ v - p)⁻¹)
          + ∑ p ∈ S, d p * ∫ v : ℝ in a..b, ((φ v - p) ^ 2)⁻¹ := by
    intro a b φ hcont hmem hne
    have hgc : ContinuousOn (fun v : ℝ => g (φ v)) (Set.uIcc a b) :=
      hg.continuousOn.comp hcont hmem
    have hkc : ∀ p ∈ S, ContinuousOn (fun v : ℝ => res p * (φ v - p)⁻¹) (Set.uIcc a b) :=
      fun p hp => continuousOn_const.mul ((hcont.sub continuousOn_const).inv₀ fun v hv =>
        sub_ne_zero.mpr (fun h => hne v hv (h ▸ hp)))
    have hkc2 : ∀ p ∈ S, ContinuousOn (fun v : ℝ => d p * ((φ v - p) ^ 2)⁻¹) (Set.uIcc a b) :=
      fun p hp => continuousOn_const.mul (((hcont.sub continuousOn_const).pow 2).inv₀
        fun v hv => pow_ne_zero 2 (sub_ne_zero.mpr (fun h => hne v hv (h ▸ hp))))
    have hsc := continuousOn_finsetSum _ hkc
    have hsc2 := continuousOn_finsetSum _ hkc2
    rw [intervalIntegral.integral_congr (g := fun v => g (φ v) +
        (∑ p ∈ S, res p * (φ v - p)⁻¹ + ∑ p ∈ S, d p * ((φ v - p) ^ 2)⁻¹))
      (fun v hv => by
        simp only [hf _ (hmem v hv) (hne v hv), div_eq_mul_inv, Finset.sum_add_distrib])]
    have e1 : (∫ v : ℝ in a..b, (g (φ v) + (∑ p ∈ S, res p * (φ v - p)⁻¹ +
        ∑ p ∈ S, d p * ((φ v - p) ^ 2)⁻¹))) = (∫ v : ℝ in a..b, g (φ v)) +
        ∫ v : ℝ in a..b, (∑ p ∈ S, res p * (φ v - p)⁻¹ + ∑ p ∈ S, d p * ((φ v - p) ^ 2)⁻¹) :=
      intervalIntegral.integral_add hgc.intervalIntegrable (hsc.add hsc2).intervalIntegrable
    have e2 : (∫ v : ℝ in a..b, (∑ p ∈ S, res p * (φ v - p)⁻¹ +
        ∑ p ∈ S, d p * ((φ v - p) ^ 2)⁻¹)) = (∫ v : ℝ in a..b, ∑ p ∈ S, res p * (φ v - p)⁻¹) +
        ∫ v : ℝ in a..b, ∑ p ∈ S, d p * ((φ v - p) ^ 2)⁻¹ :=
      intervalIntegral.integral_add hsc.intervalIntegrable hsc2.intervalIntegrable
    rw [e1, e2, intervalIntegral.integral_finsetSum (fun p hp => (hkc p hp).intervalIntegrable),
      intervalIntegral.integral_finsetSum (fun p hp => (hkc2 p hp).intervalIntegrable)]
    simp only [intervalIntegral.integral_const_mul]
    ring
  have h1 := side z.re w.re (fun x : ℝ => (x : ℂ) + (z.im : ℂ) * Complex.I) (by fun_prop)
    (fun v hv => Complex.mem_reProdIm.mpr ⟨by simpa using hv, by simp [Set.left_mem_uIcc]⟩)
    (fun v hv h => by have := (hin _ h).2.2.1; simp at this)
  have h2 := side z.re w.re (fun x : ℝ => (x : ℂ) + (w.im : ℂ) * Complex.I) (by fun_prop)
    (fun v hv => Complex.mem_reProdIm.mpr ⟨by simpa using hv, by simp [Set.right_mem_uIcc]⟩)
    (fun v hv h => by have := (hin _ h).2.2.2; simp at this)
  have h3 := side z.im w.im (fun y : ℝ => (w.re : ℂ) + (y : ℂ) * Complex.I) (by fun_prop)
    (fun v hv => Complex.mem_reProdIm.mpr ⟨by simp [Set.right_mem_uIcc], by simpa using hv⟩)
    (fun v hv h => by have := (hin _ h).2.1; simp at this)
  have h4 := side z.im w.im (fun y : ℝ => (z.re : ℂ) + (y : ℂ) * Complex.I) (by fun_prop)
    (fun v hv => Complex.mem_reProdIm.mpr ⟨by simp [Set.left_mem_uIcc], by simpa using hv⟩)
    (fun v hv h => by have := (hin _ h).1; simp at this)
  have hG := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g z w hg
  have hP : ∀ p ∈ S, res p * ((∫ x : ℝ in z.re..w.re, ((x : ℂ) + (z.im : ℂ) * Complex.I - p)⁻¹)
        - (∫ x : ℝ in z.re..w.re, ((x : ℂ) + (w.im : ℂ) * Complex.I - p)⁻¹)
      + Complex.I * (∫ y : ℝ in z.im..w.im, ((w.re : ℂ) + (y : ℂ) * Complex.I - p)⁻¹)
      - Complex.I * (∫ y : ℝ in z.im..w.im, ((z.re : ℂ) + (y : ℂ) * Complex.I - p)⁻¹))
      = 2 * (Real.pi : ℂ) * Complex.I * res p := by
    intro p hp
    obtain ⟨a1, a2, a3, a4⟩ := hin p hp
    have := boundaryIntegral_ofBounds_inv_sub_eq_two_pi_mul_I (w := p) a1 a2 a3 a4
    simp only [boundaryIntegral, ofBounds_first_re, ofBounds_first_im, ofBounds_second_re,
      ofBounds_second_im, smul_eq_mul] at this
    rw [this]; ring
  have hQ : ∀ p ∈ S, d p *
      ((∫ x : ℝ in z.re..w.re, (((x : ℂ) + (z.im : ℂ) * Complex.I - p) ^ 2)⁻¹)
        - (∫ x : ℝ in z.re..w.re, (((x : ℂ) + (w.im : ℂ) * Complex.I - p) ^ 2)⁻¹)
      + Complex.I * (∫ y : ℝ in z.im..w.im, (((w.re : ℂ) + (y : ℂ) * Complex.I - p) ^ 2)⁻¹)
      - Complex.I * (∫ y : ℝ in z.im..w.im, (((z.re : ℂ) + (y : ℂ) * Complex.I - p) ^ 2)⁻¹))
      = 0 := by
    intro p hp
    obtain ⟨a1, a2, a3, a4⟩ := hin p hp
    have := boundaryIntegral_inv_sub_sq_eq_zero r (p := p) (ne_of_gt a3) (ne_of_lt a4)
      (ne_of_gt a1) (ne_of_lt a2)
    simp only [boundaryIntegral, smul_eq_mul] at this
    rw [this, mul_zero]
  have hsum2 : (∑ p ∈ S, res p * ∫ x : ℝ in z.re..w.re, ((x : ℂ) + (z.im : ℂ) * Complex.I - p)⁻¹)
      - (∑ p ∈ S, res p * ∫ x : ℝ in z.re..w.re, ((x : ℂ) + (w.im : ℂ) * Complex.I - p)⁻¹)
      + Complex.I * (∑ p ∈ S, res p *
          ∫ y : ℝ in z.im..w.im, ((w.re : ℂ) + (y : ℂ) * Complex.I - p)⁻¹)
      - Complex.I * (∑ p ∈ S, res p *
          ∫ y : ℝ in z.im..w.im, ((z.re : ℂ) + (y : ℂ) * Complex.I - p)⁻¹)
      = 2 * (Real.pi : ℂ) * Complex.I * ∑ p ∈ S, res p := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← hP p hp]; ring
  have hsum3 : (∑ p ∈ S, d p *
          ∫ x : ℝ in z.re..w.re, (((x : ℂ) + (z.im : ℂ) * Complex.I - p) ^ 2)⁻¹)
      - (∑ p ∈ S, d p *
          ∫ x : ℝ in z.re..w.re, (((x : ℂ) + (w.im : ℂ) * Complex.I - p) ^ 2)⁻¹)
      + Complex.I * (∑ p ∈ S, d p *
          ∫ y : ℝ in z.im..w.im, (((w.re : ℂ) + (y : ℂ) * Complex.I - p) ^ 2)⁻¹)
      - Complex.I * (∑ p ∈ S, d p *
          ∫ y : ℝ in z.im..w.im, (((z.re : ℂ) + (y : ℂ) * Complex.I - p) ^ 2)⁻¹)
      = 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [← hQ p hp]; ring
  simp only [smul_eq_mul] at hG
  simp only [boundaryIntegral, smul_eq_mul]
  rw [h1, h2, h3, h4]
  linear_combination hG + hsum2 + hsum3

end RectilinearRectangle

/-! ### Principal parts of `-f'/f(s) x^s / s` -/

namespace Complex

/-- At a point `p ≠ 0` where `f = (s - p)^k E(s)`, with `E` analytic and nonzero at `p`, the
integrand `-f'/f(s) x^s / s` has a simple pole with residue `-k x^p / p`. -/
theorem exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_zpow {x : ℝ} (hx : 0 < x)
    {f : ℂ → ℂ} {p : ℂ} (hp0 : p ≠ 0) {k : ℤ} {E : ℂ → ℂ} (hE : AnalyticAt ℂ E p)
    (hE0 : E p ≠ 0) (hf : ∀ᶠ s in 𝓝[≠] p, f s = (s - p) ^ k * E s) :
    ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧ ∀ᶠ s in 𝓝[≠] p,
      -(deriv f s / f s) * ((x : ℂ) ^ s / s) =
        (-(k : ℂ) * ((x : ℂ) ^ p / p)) / (s - p) + φ s := by
  have hL := eventually_logDeriv_eq_of_eq_zpow_mul hE hE0 hf
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hhd : ∀ s : ℂ, s ≠ 0 → DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s / s) s :=
    fun s hs => (differentiableAt_id.const_cpow (Or.inl hx0)).div differentiableAt_id hs
  have hH : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s / s) p := by
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_compl_singleton.mem_nhds (show p ∈ ({0}ᶜ : Set ℂ) from hp0)]
      with s hs using hhd s hs
  have hΨ : DifferentiableAt ℂ (fun s => -(deriv E s / E s) * ((x : ℂ) ^ s / s)) p :=
    ((hE.deriv.differentiableAt.div hE.differentiableAt hE0).neg).mul (hhd p hp0)
  apply exists_eventually_eq_div_sub_add_of_analyticAt (c := -(k : ℂ)) hH hΨ
  filter_upwards [hL] with s hs
  rw [← logDeriv_apply, hs, logDeriv_apply]
  ring

/-- If `f` is analytic and nonzero at `0`, then `-f'/f(s) x^s / s` has a simple pole at `0` with
residue `-f'(0)/f(0)`. -/
theorem exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_ne_zero {x : ℝ} (hx : 0 < x)
    {f : ℂ → ℂ} (hfa : AnalyticAt ℂ f 0) (hf0 : f 0 ≠ 0) :
    ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ 0 ∧ ∀ᶠ s in 𝓝[≠] (0 : ℂ),
      -(deriv f s / f s) * ((x : ℂ) ^ s / s) = (-(deriv f 0 / f 0)) / (s - 0) + φ s := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hH : AnalyticAt ℂ (fun s => -(deriv f s / f s) * (x : ℂ) ^ s) 0 := by
    have h2 : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s) 0 := by
      rw [analyticAt_iff_eventually_differentiableAt]
      exact Eventually.of_forall fun s => differentiableAt_id.const_cpow (Or.inl hx0)
    exact (hfa.deriv.div hfa hf0).neg.mul h2
  obtain ⟨φ, hφ, hφe⟩ := exists_eventually_eq_div_sub_add_of_analyticAt (c := 1)
    (Ψ := fun _ => 0) (p := 0)
    (F := fun s => -(deriv f s / f s) * ((x : ℂ) ^ s / s)) hH
    (differentiableAt_const 0) (Eventually.of_forall fun s => by simp only [sub_zero]; ring)
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hφe] with s hs
  rw [hs]
  simp

/-- **A double pole at `0`.** If `f = s E(s)` near `0`, with `E` analytic and nonzero at `0`,
then `-f'/f(s) x^s / s = -(log x + E'(0)/E(0))/s - 1/s² + φ(s)` with `φ` differentiable at `0`. -/
theorem exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_eq_mul {x : ℝ} (hx : 0 < x)
    {f E : ℂ → ℂ} (hE : AnalyticAt ℂ E 0) (hE0 : E 0 ≠ 0)
    (hf : ∀ᶠ s in 𝓝[≠] (0 : ℂ), f s = s * E s) :
    ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ 0 ∧ ∀ᶠ s in 𝓝[≠] (0 : ℂ),
      -(deriv f s / f s) * ((x : ℂ) ^ s / s) =
        (-(Real.log x : ℂ) - deriv E 0 / E 0) / (s - 0) + (-1) / (s - 0) ^ 2 + φ s := by
  have hf' : ∀ᶠ s in 𝓝[≠] (0 : ℂ), f s = (s - 0) ^ (1 : ℤ) * E s := by
    filter_upwards [hf] with s hs; rw [hs]; simp
  have hL := eventually_logDeriv_eq_of_eq_zpow_mul hE hE0 hf'
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  set u : ℂ → ℂ := fun s => (x : ℂ) ^ s with hu
  have hud : Differentiable ℂ u := fun s => differentiableAt_id.const_cpow (Or.inl hx0)
  have hu0 : u 0 = 1 := by simp [hu]
  have hderiv : deriv u 0 = (Real.log x : ℂ) := by
    have h : HasDerivAt u ((x : ℂ) ^ (0 : ℂ) * log x * 1) 0 :=
      (hasDerivAt_id' (0 : ℂ)).const_cpow (c := (x : ℂ)) (Or.inl hx0)
    rw [h.deriv, ofReal_log hx.le]
    simp
  set h₁ : ℂ → ℂ := dslope u 0 with hh₁
  have hh₁d : Differentiable ℂ h₁ := fun s =>
    ((differentiableOn_dslope (c := (0 : ℂ)) (f := u) univ_mem).mpr
      hud.differentiableOn).differentiableAt univ_mem
  set h₂ : ℂ → ℂ := dslope h₁ 0 with hh₂
  have hh₂d : Differentiable ℂ h₂ := fun s =>
    ((differentiableOn_dslope (c := (0 : ℂ)) (f := h₁) univ_mem).mpr
      hh₁d.differentiableOn).differentiableAt univ_mem
  set H : ℂ → ℂ := fun s => -(deriv E s / E s) * u s with hH
  have hHa : AnalyticAt ℂ H 0 := (hE.deriv.div hE hE0).neg.mul (hud.analyticAt 0)
  have hHd : DifferentiableAt ℂ (dslope H 0) 0 := by
    have hU : {s | AnalyticAt ℂ H s} ∈ 𝓝 (0 : ℂ) := hHa.eventually_analyticAt
    have hd : DifferentiableOn ℂ H {s | AnalyticAt ℂ H s} :=
      fun s hs => hs.differentiableAt.differentiableWithinAt
    exact ((differentiableOn_dslope hU).mpr hd).differentiableAt hU
  refine ⟨fun s => -h₂ s + dslope H 0 s, (hh₂d 0).neg.add hHd, ?_⟩
  filter_upwards [hL, self_mem_nhdsWithin] with s hs hs0
  have hs0' : s ≠ 0 := hs0
  have e1 : h₁ s = (u s - 1) / s := by
    rw [hh₁, dslope_of_ne _ hs0', slope_def_field, hu0, sub_zero]
  have e10 : h₁ 0 = (Real.log x : ℂ) := by rw [hh₁, dslope_same, hderiv]
  have e2 : h₂ s = (h₁ s - (Real.log x : ℂ)) / s := by
    rw [hh₂, dslope_of_ne _ hs0', slope_def_field, e10, sub_zero]
  have e3 : dslope H 0 s = (H s - H 0) / s := by
    rw [dslope_of_ne _ hs0', slope_def_field, sub_zero]
  have hH0 : H 0 = -(deriv E 0 / E 0) := by simp [hH, hu0]
  rw [e2, e1, e3, hH0, ← logDeriv_apply, hs]
  simp only [hH, sub_zero, logDeriv_apply]
  push_cast
  field_simp
  ring

end Complex
