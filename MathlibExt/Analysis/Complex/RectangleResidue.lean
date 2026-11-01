/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.RectilinearCycle
public import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The residue theorem on a rectangle for finitely many simple poles

A function with simple poles at the points of a finite set `S`, with residues `r p`, splits on a
set `K` as a holomorphic part plus its principal parts. On a rectangle containing `S` in its
interior, the boundary integral is then `2πi ∑_{p ∈ S} r p`.

## Main statements

* `Complex.exists_eventually_eq_div_sub_add_of_analyticAt`: replacing an analytic numerator over
  a simple pole by its value at the pole.
* `Complex.eventually_logDeriv_eq_of_eq_zpow_mul`: near a point where `f = (s - p) ^ k E(s)` with
  `E` analytic and nonzero at `p`, `f'/f = k / (s - p) + E'/E`.
* `Complex.exists_differentiableOn_eq_add_sum_div_sub`: subtracting the principal parts at
  finitely many simple poles leaves a function differentiable on the whole set.
* `RectilinearRectangle.boundaryIntegral_eq_two_pi_mul_I_mul_sum`: the residue theorem for simple
  poles on a rectangle.
-/

@[expose] public section

open Filter Topology Set

namespace Complex

/-- An analytic factor over a simple pole: if `F = c H / (s - p) + Ψ` near `p`, with `H`
analytic and `Ψ` differentiable at `p`, then `F = c H(p) / (s - p) + φ` with `φ`
differentiable at `p`. -/
theorem exists_eventually_eq_div_sub_add_of_analyticAt {p c : ℂ} {H Ψ F : ℂ → ℂ}
    (hH : AnalyticAt ℂ H p) (hΨ : DifferentiableAt ℂ Ψ p)
    (hF : ∀ᶠ s in 𝓝[≠] p, F s = c * H s / (s - p) + Ψ s) :
    ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧ ∀ᶠ s in 𝓝[≠] p, F s = c * H p / (s - p) + φ s := by
  refine ⟨fun s => c * dslope H p s + Ψ s, ?_, ?_⟩
  · have hU : {s | AnalyticAt ℂ H s} ∈ 𝓝 p := hH.eventually_analyticAt
    have hd : DifferentiableOn ℂ H {s | AnalyticAt ℂ H s} :=
      fun s hs => hs.differentiableAt.differentiableWithinAt
    have := ((Complex.differentiableOn_dslope hU).mpr hd).differentiableAt hU
    exact (this.const_mul c).add hΨ
  · filter_upwards [hF, self_mem_nhdsWithin] with s hs hsp
    have hsp' : s - p ≠ 0 := sub_ne_zero.mpr hsp
    rw [hs, dslope_of_ne _ hsp, slope_def_field]
    field_simp
    ring

/-- Near a point where `f = (s - p) ^ k E(s)` with `E` analytic and nonzero at `p`,
`f'/f = k / (s - p) + E'/E`. -/
theorem eventually_logDeriv_eq_of_eq_zpow_mul {f E : ℂ → ℂ} {p : ℂ} {k : ℤ}
    (hE : AnalyticAt ℂ E p) (hE0 : E p ≠ 0) (hf : ∀ᶠ s in 𝓝[≠] p, f s = (s - p) ^ k * E s) :
    ∀ᶠ s in 𝓝[≠] p, logDeriv f s = k / (s - p) + logDeriv E s := by
  have h2 := eventually_eventually_nhdsWithin.mpr hf
  have hA : ∀ᶠ s in 𝓝[≠] p, AnalyticAt ℂ E s := nhdsWithin_le_nhds hE.eventually_analyticAt
  have hN : ∀ᶠ s in 𝓝[≠] p, E s ≠ 0 :=
    nhdsWithin_le_nhds (hE.continuousAt.eventually_ne hE0)
  filter_upwards [h2, hA, hN, self_mem_nhdsWithin] with s hs hAs hNs hsp
  rw [isOpen_compl_singleton.nhdsWithin_eq hsp] at hs
  have hsp' : s - p ≠ 0 := sub_ne_zero.mpr hsp
  have hs' : f =ᶠ[𝓝 s] fun t => (t - p) ^ k * E t := hs
  rw [logDeriv_apply, logDeriv_apply, hs'.deriv_eq, hs'.eq_of_nhds]
  have hd1 : HasDerivAt (fun t => (t - p) ^ k) (k * (s - p) ^ (k - 1)) s :=
    (hasDerivAt_zpow k (s - p) (Or.inl hsp')).comp_sub_const s p
  have hd := hd1.fun_mul hAs.differentiableAt.hasDerivAt
  rw [hd.deriv, zpow_sub_one₀ hsp']
  have : (s - p) ^ k ≠ 0 := zpow_ne_zero _ hsp'
  field_simp

/-- **Subtracting principal parts.** If `f = r p / (s - p) + φ_p` near each `p ∈ S` with `φ_p`
differentiable at `p`, and `f` is differentiable within `K` off `S`, then
`f = g + ∑_{p ∈ S} r p / (s - p)` on `K \ S` for some `g` differentiable on `K`. -/
theorem exists_differentiableOn_eq_add_sum_div_sub (K : Set ℂ) (S : Finset ℂ) (r f : ℂ → ℂ)
    (hloc : ∀ p ∈ S, ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧
      ∀ᶠ s in 𝓝[≠] p, f s = r p / (s - p) + φ s)
    (hdiff : ∀ s ∈ K, s ∉ S → DifferentiableWithinAt ℂ f K s) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g K ∧
      ∀ s ∈ K, s ∉ S → f s = g s + ∑ p ∈ S, r p / (s - p) := by
  classical
  choose φ hφd hφe using hloc
  let g : ℂ → ℂ := fun s => if hs : s ∈ S then φ s hs s - ∑ q ∈ S.erase s, r q / (s - q)
    else f s - ∑ q ∈ S, r q / (s - q)
  refine ⟨g, ?_, ?_⟩
  · intro s hsK
    have hsumd : ∀ T : Finset ℂ, s ∉ T →
        DifferentiableAt ℂ (fun t => ∑ q ∈ T, r q / (t - q)) s := by
      intro T hT
      apply DifferentiableAt.fun_sum
      intro q hq
      have : s - q ≠ 0 := sub_ne_zero.mpr (fun h => hT (h ▸ hq))
      fun_prop (disch := assumption)
    by_cases hs : s ∈ S
    · apply DifferentiableAt.differentiableWithinAt
      have hev1 : ∀ᶠ t in 𝓝 s, t ∉ S.erase s :=
        (S.erase s).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
      have hev2 := eventually_nhdsWithin_iff.mp (hφe s hs)
      have heq : g =ᶠ[𝓝 s] fun t => φ s hs t - ∑ q ∈ S.erase s, r q / (t - q) := by
        filter_upwards [hev1, hev2] with t h1 h2
        by_cases hts : t = s
        · subst hts; simp [g, hs]
        · have htS : t ∉ S := fun h => h1 (Finset.mem_erase.mpr ⟨hts, h⟩)
          simp only [g, htS, dite_false]
          rw [h2 hts, ← Finset.add_sum_erase S _ hs]
          ring
      exact (DifferentiableAt.congr_of_eventuallyEq
        ((hφd s hs).sub (hsumd _ (by simp))) heq)
    · have hev1 : ∀ᶠ t in 𝓝 s, t ∉ S :=
        S.finite_toSet.isClosed.isOpen_compl.mem_nhds (by simpa using hs)
      have heq : g =ᶠ[𝓝 s] fun t => f t - ∑ q ∈ S, r q / (t - q) := by
        filter_upwards [hev1] with t h1
        simp [g, h1]
      exact ((hdiff s hsK hs).sub (hsumd _ hs).differentiableWithinAt).congr_of_eventuallyEq
        (nhdsWithin_le_nhds heq) heq.eq_of_nhds
  · intro s _ hs
    simp [g, hs]

end Complex

namespace RectilinearRectangle

/-- **The residue theorem on a rectangle, for simple poles.** If `f = g + ∑_{p ∈ S} r p / (s - p)`
on the closed rectangle off `S`, with `g` holomorphic on the closed rectangle and `S` contained in
the open rectangle, then the positively oriented boundary integral of `f` is `2πi ∑_{p ∈ S} r p`.
-/
theorem boundaryIntegral_eq_two_pi_mul_I_mul_sum (r : RectilinearRectangle) (S : Finset ℂ)
    (res f g : ℂ → ℂ)
    (hin : ∀ p ∈ S, r.first.re < p.re ∧ p.re < r.second.re ∧ r.first.im < p.im ∧
      p.im < r.second.im)
    (hg : DifferentiableOn ℂ g r.carrier)
    (hf : ∀ s ∈ r.carrier, s ∉ S → f s = g s + ∑ p ∈ S, res p / (s - p)) :
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
        = (∫ v : ℝ in a..b, g (φ v)) + ∑ p ∈ S, res p * ∫ v : ℝ in a..b, (φ v - p)⁻¹ := by
    intro a b φ hcont hmem hne
    have hgc : ContinuousOn (fun v : ℝ => g (φ v)) (Set.uIcc a b) :=
      hg.continuousOn.comp hcont hmem
    have hkc : ∀ p ∈ S, ContinuousOn (fun v : ℝ => res p * (φ v - p)⁻¹) (Set.uIcc a b) :=
      fun p hp => continuousOn_const.mul ((hcont.sub continuousOn_const).inv₀ fun v hv =>
        sub_ne_zero.mpr (fun h => hne v hv (h ▸ hp)))
    rw [intervalIntegral.integral_congr (g := fun v => g (φ v) + ∑ p ∈ S, res p * (φ v - p)⁻¹)
      (fun v hv => by simp only [hf _ (hmem v hv) (hne v hv), div_eq_mul_inv])]
    rw [intervalIntegral.integral_add hgc.intervalIntegrable
        (continuousOn_finsetSum _ hkc).intervalIntegrable,
      intervalIntegral.integral_finsetSum (fun p hp => (hkc p hp).intervalIntegrable)]
    simp only [intervalIntegral.integral_const_mul]
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
  simp only [smul_eq_mul] at hG
  simp only [boundaryIntegral, smul_eq_mul]
  rw [h1, h2, h3, h4]
  linear_combination hG + hsum2

end RectilinearRectangle
