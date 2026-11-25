/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Topology.MetricSpace.Thickening
import MathlibExt.Analysis.Ramanujan.Part1Ch7Entry1Powersum

/-!
# The classical zero-free region of the Riemann zeta function

There is an absolute constant `c > 0` such that the Riemann zeta function has no zero
`s = σ + i t` with `σ > 1 - c / log (2 + |t|)`.

## Main result

* `riemannZeta_ne_zero_of_classical_zero_free_region`: there is `c > 0` such that `ζ(s) ≠ 0`
  for every `s ≠ 1` with `Re s > 1 - c / log (2 + |Im s|)`.

## Proof outline

* **Landau's lemma** (`neg_re_logDeriv_le`, `neg_re_logDeriv_le_of_zero`, private). Let `f` be
  holomorphic on the closed disc of radius `R` around `s0` with `f s0 ≠ 0` and
  `‖f z‖ ≤ exp M * ‖f s0‖` on its boundary, and let `‖s - s0‖ ≤ R / 6`. If every zero `ρ` of `f`
  with `‖ρ - s0‖ ≤ R / 3` has `Re ρ < Re s`, then `-Re (f'(s) / f(s)) ≤ 72 M / R`, and a chosen
  such zero `ρ₀` improves this by `Re (1 / (s - ρ₀))`. The zeros in the disc of radius `R / 3`
  are removed one at a time with `dslope`; each removal halves the constant in the bound on the
  boundary circle, so finitely many removals suffice (this replaces Jensen's formula), and each
  removed zero contributes a term `Re (1 / (s - ρ)) > 0`. On the zero-free quotient, a primitive
  of its logarithmic derivative gives a holomorphic logarithm with real part at most `M`, which
  the Borel–Carathéodory theorem (`Complex.borelCaratheodory_zero`) and a Cauchy estimate bound.
* **Estimates for `ζ`.** The Euler–Maclaurin expansion of
  `MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry1Powersum.chapter7PowerSum_exact_expansion` gives
  `‖ζ s‖ ≤ C (‖s‖ + 2) ^ 3` for `Re s ≥ -3 / 2` and `|Im s| ≥ 1`; the Möbius function gives
  `‖ζ s‖ ≥ c₁ > 0` on `Re s = 3 / 2`; and `ζ'/ζ(σ) + 1 / (σ - 1)` is bounded for real `σ` near
  `1`. Landau's lemma on discs of radius `3` around `3 / 2 + i γ` and `3 / 2 + 2 i γ` then bounds
  `-Re (ζ'/ζ)` at `σ + i γ` and `σ + 2 i γ` by `O(log (2 + |γ|))`, minus `1 / (σ - β)` when
  `β + i γ` is a zero.
* **The `3`–`4`–`1` argument.** Since `-ζ'/ζ = ∑ Λ(n) n^{-s}` for `Re s > 1` and
  `3 + 4 cos θ + cos 2θ = 2 (1 + cos θ) ^ 2 ≥ 0`, taking `σ = 1 + δ / log (2 + |γ|)` with a small
  absolute `δ` gives `1 - β ≥ δ / (7 log (2 + |γ|))` for every zero `β + i γ` with `|γ| > 4` and
  `β ≥ 1 / 2`. Zeros with `|γ| ≤ 4` stay a fixed distance away from the line `Re s = 1` by
  compactness, because `(s - 1) ζ(s)` is entire and does not vanish on `Re s ≥ 1`.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ZetaClassicalZeroFreeRegionWanted

open Complex Metric Set Filter Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry1Powersum
open MetaMathlibExt (bernoulliKernel bernoulliKernel_norm_le)

/-- Maximum modulus principle on a closed disc: a bound on the boundary circle holds on the whole
closed disc. -/
private lemma norm_le_of_forall_mem_sphere {f : ℂ → ℂ} {s0 : ℂ} {R C : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall s0 R)) (hC : ∀ z ∈ sphere s0 R, ‖f z‖ ≤ C) :
    ∀ z ∈ closedBall s0 R, ‖f z‖ ≤ C := by
  intro z hz
  have hd : DiffContOnCl ℂ f (ball s0 R) := by
    apply DifferentiableOn.diffContOnCl
    rwa [closure_ball s0 hR.ne']
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
  · rwa [frontier_ball s0 hR.ne']
  · rwa [closure_ball s0 hR.ne']

/-- The zero-free case of Landau's lemma. If `g` is holomorphic on the closed disc of radius `R`
around `s0`, has no zero in the closed disc of radius `R / 3`, and satisfies
`‖g z‖ ≤ exp M * ‖g s0‖` on the boundary circle, then `‖g'(s) / g(s)‖ ≤ 72 M / R` whenever
`‖s - s0‖ ≤ R / 6`. The proof takes a holomorphic logarithm `h` of `g / g s0` on the disc of radius
`R / 3` (a primitive of `g' / g`), bounds `‖h‖` by the Borel–Carathéodory theorem since
`Re h ≤ M`, and bounds `h'` by a Cauchy estimate. -/
private lemma norm_deriv_div_le {g : ℂ → ℂ} {s0 s : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hg : DifferentiableOn ℂ g (closedBall s0 R))
    (hg0 : ∀ z ∈ closedBall s0 (R / 3), g z ≠ 0)
    (hB : ∀ z ∈ sphere s0 R, ‖g z‖ ≤ Real.exp M * ‖g s0‖)
    (hs : s ∈ closedBall s0 (R / 6)) :
    ‖deriv g s / g s‖ ≤ 72 * M / R := by
  have hball : ∀ z ∈ closedBall s0 R, ‖g z‖ ≤ Real.exp M * ‖g s0‖ :=
    norm_le_of_forall_mem_sphere hR hg hB
  set r := R / 3 with hr
  have hr0 : 0 < r := by positivity
  have hsub : ball s0 r ⊆ ball s0 R := ball_subset_ball (by linarith)
  have hgo : DifferentiableOn ℂ g (ball s0 R) := hg.mono ball_subset_closedBall
  have hdg : DifferentiableOn ℂ (deriv g) (ball s0 R) := hgo.deriv isOpen_ball
  have hg0' : ∀ z ∈ ball s0 r, g z ≠ 0 := fun z hz => hg0 z (ball_subset_closedBall hz)
  have hq : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball s0 r) :=
    (hdg.mono hsub).div (hgo.mono hsub) hg0'
  obtain ⟨L, hL⟩ := hq.isExactOn_ball
  have hs0 : s0 ∈ ball s0 r := mem_ball_self hr0
  have hgs0 : g s0 ≠ 0 := hg0' s0 hs0
  -- `g * exp (-L)` is constant on the ball
  have hderiv : ∀ z ∈ ball s0 r, HasDerivAt (fun w => g w * Complex.exp (-L w)) 0 z := by
    intro z hz
    have hgz : HasDerivAt g (deriv g z) z :=
      (hgo.differentiableAt (isOpen_ball.mem_nhds (hsub hz))).hasDerivAt
    have h := hgz.mul ((hL z hz).neg.cexp)
    convert h using 1
    have : g z ≠ 0 := hg0' z hz
    field_simp
    ring
  have hdiff : DifferentiableOn ℂ (fun w => g w * Complex.exp (-L w)) (ball s0 r) :=
    fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt
  have hconst : ∀ z ∈ ball s0 r, g z * Complex.exp (-L z) = g s0 * Complex.exp (-L s0) :=
    fun z hz => isOpen_ball.is_const_of_deriv_eq_zero (convex_ball s0 r).isPreconnected hdiff
      (fun w hw => (hderiv w hw).deriv) hz hs0
  set h : ℂ → ℂ := fun z => L z - L s0 with hh
  have hexp : ∀ z ∈ ball s0 r, Complex.exp (h z) = g z / g s0 := by
    intro z hz
    have h1 := hconst z hz
    rw [Complex.exp_neg, Complex.exp_neg] at h1
    simp only [hh, Complex.exp_sub]
    rw [div_eq_div_iff (Complex.exp_ne_zero _) hgs0]
    field_simp at h1
    linear_combination -h1
  have hre : ∀ z ∈ ball s0 r, (h z).re ≤ M := by
    intro z hz
    have h1 : Real.exp (h z).re = ‖g z‖ / ‖g s0‖ := by
      rw [← Complex.norm_exp, hexp z hz, norm_div]
    have h2 : ‖g z‖ / ‖g s0‖ ≤ Real.exp M := by
      rw [div_le_iff₀ (norm_pos_iff.mpr hgs0)]
      exact hball z (ball_subset_closedBall (hsub hz))
    rw [← h1] at h2
    exact Real.exp_le_exp.mp h2
  have hLd : ∀ z ∈ ball s0 r, HasDerivAt h (deriv g z / g z) z :=
    fun z hz => (hL z hz).sub_const _
  have hhd : DifferentiableOn ℂ h (ball s0 r) :=
    fun z hz => (hLd z hz).differentiableAt.differentiableWithinAt
  -- Borel–Carathéodory
  have hBC : ∀ z ∈ ball s0 r, ‖h z‖ ≤ 2 * M * ‖z - s0‖ / (r - ‖z - s0‖) := by
    intro z hz
    set H : ℂ → ℂ := fun w => h (s0 + w) with hH
    have hmaps : MapsTo (fun w : ℂ => s0 + w) (ball 0 r) (ball s0 r) := by
      intro w hw
      simpa [mem_ball, dist_eq] using hw
    have hHd : DifferentiableOn ℂ H (ball 0 r) :=
      hhd.comp ((differentiable_const s0).add differentiable_id).differentiableOn hmaps
    have hHm : MapsTo H (ball 0 r) {w | w.re ≤ M} := fun w hw => hre _ (hmaps hw)
    have hH0 : H 0 = 0 := by simp [hH, hh]
    have hzw : z - s0 ∈ ball (0 : ℂ) r := by simpa [mem_ball, dist_eq] using hz
    have := Complex.borelCaratheodory_zero hM hHd hHm hr0 hzw hH0
    simpa [hH] using this
  -- Cauchy estimate on the circle of radius `r / 4` around `s`
  have hs' : ‖s - s0‖ ≤ r / 2 := by
    have := mem_closedBall.mp hs
    rw [dist_eq] at this
    linarith
  have hsub2 : closedBall s (r / 4) ⊆ ball s0 r := by
    intro z hz
    rw [mem_closedBall, dist_eq] at hz
    rw [mem_ball, dist_eq]
    calc ‖z - s0‖ = ‖(z - s) + (s - s0)‖ := by ring_nf
      _ ≤ ‖z - s‖ + ‖s - s0‖ := norm_add_le _ _
      _ < r := by linarith
  have hcl : DiffContOnCl ℂ h (ball s (r / 4)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s (by positivity)]
    exact hhd.mono hsub2
  have hsph : ∀ z ∈ sphere s (r / 4), ‖h z‖ ≤ 6 * M := by
    intro z hz
    have hzb : z ∈ ball s0 r := hsub2 (sphere_subset_closedBall hz)
    have hz' : ‖z - s0‖ ≤ 3 * r / 4 := by
      rw [mem_sphere, dist_eq] at hz
      calc ‖z - s0‖ = ‖(z - s) + (s - s0)‖ := by ring_nf
        _ ≤ ‖z - s‖ + ‖s - s0‖ := norm_add_le _ _
        _ ≤ 3 * r / 4 := by linarith
    refine (hBC z hzb).trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hcl hsph
  have hsb : s ∈ ball s0 r := hsub2 (mem_closedBall_self (by positivity))
  rw [(hLd s hsb).deriv] at hcauchy
  calc ‖deriv g s / g s‖ ≤ 6 * M / (r / 4) := hcauchy
    _ = 72 * M / R := by rw [hr]; field_simp; ring

/-- Removing a zero `ρ` of `f`: the slope function `dslope f ρ` is holomorphic wherever `f` is, and
`f z = (z - ρ) * dslope f ρ z` for every `z`. -/
private lemma differentiableOn_dslope_and_eq {f : ℂ → ℂ} {s0 ρ : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall s0 R)) (hρ : ρ ∈ closedBall s0 (R / 3))
    (hfρ : f ρ = 0) :
    DifferentiableOn ℂ (dslope f ρ) (closedBall s0 R) ∧ ∀ z, f z = (z - ρ) * dslope f ρ z := by
  constructor
  · have hρ' : ρ ∈ ball s0 R := by
      rw [mem_closedBall] at hρ
      rw [mem_ball]
      linarith
    exact (differentiableOn_dslope (closedBall_mem_nhds_of_mem hρ')).2 hf
  · intro z
    have := sub_smul_dslope f ρ z
    rw [hfρ, sub_zero, smul_eq_mul] at this
    exact this.symm

/-- Logarithmic derivative of `(z - ρ) * f₁ z`. -/
private lemma deriv_div_eq {f f1 : ℂ → ℂ} {ρ s : ℂ} (hfz : ∀ z, f z = (z - ρ) * f1 z)
    (hf1 : DifferentiableAt ℂ f1 s) (hsρ : s ≠ ρ) (hf1s : f1 s ≠ 0) :
    deriv f s / f s = 1 / (s - ρ) + deriv f1 s / f1 s := by
  have hfeq : f = fun z => (z - ρ) * f1 z := funext hfz
  have hd : deriv f s = f1 s + (s - ρ) * deriv f1 s := by
    rw [hfeq]
    have := ((hasDerivAt_id s).sub_const ρ).mul hf1.hasDerivAt
    simp only [id, one_mul] at this
    exact this.deriv
  have hsρ' : s - ρ ≠ 0 := sub_ne_zero.mpr hsρ
  rw [hd, hfz s]
  field_simp

/-- `Re (1 / w) > 0` when `Re w > 0`. -/
private lemma re_one_div_pos {w : ℂ} (hw : 0 < w.re) : 0 < (1 / w).re := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  rw [one_div, Complex.inv_re]
  exact div_pos hw (Complex.normSq_pos.mpr hw0)

/-- Removing a zero `ρ` with `‖ρ - s0‖ ≤ R / 3` halves the constant in a bound
`‖f z‖ ≤ A * ‖f s0‖` on the circle of radius `R` around `s0`. -/
private lemma norm_dslope_le_half {f f1 : ℂ → ℂ} {s0 ρ : ℂ} {R A : ℝ} (hR : 0 < R)
    (hρ : ρ ∈ closedBall s0 (R / 3)) (hfz : ∀ z, f z = (z - ρ) * f1 z)
    (hB : ∀ z ∈ sphere s0 R, ‖f z‖ ≤ A * ‖f s0‖) (hA : 0 ≤ A) :
    ∀ z ∈ sphere s0 R, ‖f1 z‖ ≤ (A / 2) * ‖f1 s0‖ := by
  intro z hz
  rw [mem_closedBall, dist_eq] at hρ
  rw [mem_sphere, dist_eq] at hz
  have hzρ : 2 * R / 3 ≤ ‖z - ρ‖ := by
    have : ‖z - s0‖ ≤ ‖z - ρ‖ + ‖ρ - s0‖ := by
      calc ‖z - s0‖ = ‖(z - ρ) + (ρ - s0)‖ := by ring_nf
        _ ≤ ‖z - ρ‖ + ‖ρ - s0‖ := norm_add_le _ _
    linarith
  have h1 : ‖z - ρ‖ * ‖f1 z‖ ≤ A * (‖s0 - ρ‖ * ‖f1 s0‖) := by
    have := hB z (by rw [mem_sphere, dist_eq]; exact hz)
    rw [hfz z, hfz s0, norm_mul, norm_mul] at this
    exact this
  have h2 : ‖s0 - ρ‖ ≤ R / 3 := by rw [norm_sub_rev]; exact hρ
  have h3 : A * (‖s0 - ρ‖ * ‖f1 s0‖) ≤ A * (R / 3 * ‖f1 s0‖) := by
    gcongr
  have h4 : 2 * R / 3 * ‖f1 z‖ ≤ ‖z - ρ‖ * ‖f1 z‖ := by gcongr
  have h5 : 2 * R / 3 * ‖f1 z‖ ≤ 2 * R / 3 * ((A / 2) * ‖f1 s0‖) := by
    calc 2 * R / 3 * ‖f1 z‖ ≤ A * (R / 3 * ‖f1 s0‖) := h4.trans (h1.trans h3)
      _ = 2 * R / 3 * ((A / 2) * ‖f1 s0‖) := by ring
  exact le_of_mul_le_mul_left h5 (by positivity)

/-- A bound `‖f z‖ ≤ A * ‖f s0‖` on the circle forces `1 ≤ A` (maximum modulus at the centre). -/
private lemma one_le_of_norm_le_mul {f : ℂ → ℂ} {s0 : ℂ} {R A : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall s0 R)) (hf0 : f s0 ≠ 0)
    (hB : ∀ z ∈ sphere s0 R, ‖f z‖ ≤ A * ‖f s0‖) : 1 ≤ A := by
  have := norm_le_of_forall_mem_sphere hR hf hB s0 (mem_closedBall_self hR.le)
  have hpos : 0 < ‖f s0‖ := norm_pos_iff.mpr hf0
  nlinarith

/-- Landau's lemma by induction on the number of halvings: if `A < 2 ^ n`, zeros are removed one at
a time with `dslope`, each removal halving `A` and contributing a term `Re (1 / (s - ρ)) > 0`. -/
private lemma neg_re_logDeriv_le_aux {s0 s : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hs : s ∈ closedBall s0 (R / 6)) :
    ∀ n : ℕ, ∀ (f : ℂ → ℂ) (A : ℝ), A < 2 ^ n → A ≤ Real.exp M →
      DifferentiableOn ℂ f (closedBall s0 R) → f s0 ≠ 0 →
      (∀ z ∈ sphere s0 R, ‖f z‖ ≤ A * ‖f s0‖) →
      (∀ ρ ∈ closedBall s0 (R / 3), f ρ = 0 → ρ.re < s.re) →
      -(deriv f s / f s).re ≤ 72 * M / R := by
  intro n
  induction n with
  | zero =>
    intro f A hA _ hf hf0 hB _
    have := one_le_of_norm_le_mul hR hf hf0 hB
    norm_num at hA
    linarith
  | succ k ih =>
    intro f A hA hAM hf hf0 hB hz
    have hA1 := one_le_of_norm_le_mul hR hf hf0 hB
    by_cases h0 : ∀ z ∈ closedBall s0 (R / 3), f z ≠ 0
    · have hB' : ∀ z ∈ sphere s0 R, ‖f z‖ ≤ Real.exp M * ‖f s0‖ := fun z hz' =>
        (hB z hz').trans (mul_le_mul_of_nonneg_right hAM (norm_nonneg _))
      have := norm_deriv_div_le hR hM hf h0 hB' hs
      exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans this)
    · push Not at h0
      obtain ⟨ρ, hρ, hfρ⟩ := h0
      obtain ⟨hf1, hfz⟩ := differentiableOn_dslope_and_eq hR hf hρ hfρ
      set f1 := dslope f ρ
      have hf10 : f1 s0 ≠ 0 := by
        intro h
        apply hf0
        rw [hfz s0, h, mul_zero]
      have hB1 := norm_dslope_le_half hR hρ hfz hB (by linarith)
      have hz1 : ∀ ρ' ∈ closedBall s0 (R / 3), f1 ρ' = 0 → ρ'.re < s.re := by
        intro ρ' hρ' h
        exact hz ρ' hρ' (by rw [hfz ρ', h, mul_zero])
      have hih := ih f1 (A / 2) (by rw [pow_succ] at hA; linarith) (by linarith) hf1 hf10 hB1 hz1
      have hsR3 : s ∈ closedBall s0 (R / 3) := closedBall_subset_closedBall (by linarith) hs
      have hsρ : ρ.re < s.re := hz ρ hρ hfρ
      have hsne : s ≠ ρ := fun h => by rw [h] at hsρ; exact lt_irrefl _ hsρ
      have hf1s : f1 s ≠ 0 := by
        intro h
        have := hz1 s hsR3 h
        exact lt_irrefl _ this
      have hsball : s ∈ ball s0 R := by
        rw [mem_closedBall] at hs
        rw [mem_ball]
        linarith
      have hf1d : DifferentiableAt ℂ f1 s :=
        hf1.differentiableAt (closedBall_mem_nhds_of_mem hsball)
      rw [deriv_div_eq hfz hf1d hsne hf1s, Complex.add_re]
      have hpos := re_one_div_pos (w := s - ρ) (by rw [Complex.sub_re]; linarith)
      linarith

/-- **Landau's lemma, one-sided form.** If `f` is holomorphic on the closed disc of radius `R`
around `s0`, `f s0 ≠ 0`, `‖f z‖ ≤ exp M * ‖f s0‖` on the boundary circle, `‖s - s0‖ ≤ R / 6`, and
every zero `ρ` of `f` with `‖ρ - s0‖ ≤ R / 3` satisfies `Re ρ < Re s`, then
`-Re (f'(s) / f(s)) ≤ 72 M / R`. -/
private theorem neg_re_logDeriv_le {f : ℂ → ℂ} {s0 s : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (closedBall s0 R)) (hf0 : f s0 ≠ 0)
    (hB : ∀ z ∈ sphere s0 R, ‖f z‖ ≤ Real.exp M * ‖f s0‖)
    (hs : s ∈ closedBall s0 (R / 6))
    (hz : ∀ ρ ∈ closedBall s0 (R / 3), f ρ = 0 → ρ.re < s.re) :
    -(deriv f s / f s).re ≤ 72 * M / R := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (Real.exp M) (by norm_num : (1 : ℝ) < 2)
  exact neg_re_logDeriv_le_aux hR hM hs n f _ hn le_rfl hf hf0 hB hz

/-- **Landau's lemma with a chosen zero.** Under the hypotheses of `neg_re_logDeriv_le`, a zero
`ρ₀` of `f` with `‖ρ₀ - s0‖ ≤ R / 3` improves the bound by `Re (1 / (s - ρ₀))`. -/
private theorem neg_re_logDeriv_le_of_zero {f : ℂ → ℂ} {s0 s ρ₀ : ℂ} {R M : ℝ} (hR : 0 < R)
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (closedBall s0 R)) (hf0 : f s0 ≠ 0)
    (hB : ∀ z ∈ sphere s0 R, ‖f z‖ ≤ Real.exp M * ‖f s0‖)
    (hs : s ∈ closedBall s0 (R / 6))
    (hz : ∀ ρ ∈ closedBall s0 (R / 3), f ρ = 0 → ρ.re < s.re)
    (hρ₀ : ρ₀ ∈ closedBall s0 (R / 3)) (hfρ₀ : f ρ₀ = 0) :
    -(deriv f s / f s).re ≤ 72 * M / R - (1 / (s - ρ₀)).re := by
  obtain ⟨hf1, hfz⟩ := differentiableOn_dslope_and_eq hR hf hρ₀ hfρ₀
  set f1 := dslope f ρ₀
  have hf10 : f1 s0 ≠ 0 := by
    intro h
    apply hf0
    rw [hfz s0, h, mul_zero]
  have hB1 := norm_dslope_le_half hR hρ₀ hfz hB (Real.exp_pos M).le
  have hz1 : ∀ ρ' ∈ closedBall s0 (R / 3), f1 ρ' = 0 → ρ'.re < s.re := by
    intro ρ' hρ' h
    exact hz ρ' hρ' (by rw [hfz ρ', h, mul_zero])
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (Real.exp M / 2) (by norm_num : (1 : ℝ) < 2)
  have hih := neg_re_logDeriv_le_aux hR hM hs n f1 _ hn (by linarith [Real.exp_pos M]) hf1 hf10
    hB1 hz1
  have hsR3 : s ∈ closedBall s0 (R / 3) := closedBall_subset_closedBall (by linarith) hs
  have hsρ : ρ₀.re < s.re := hz ρ₀ hρ₀ hfρ₀
  have hsne : s ≠ ρ₀ := fun h => by rw [h] at hsρ; exact lt_irrefl _ hsρ
  have hf1s : f1 s ≠ 0 := fun h => lt_irrefl _ (hz1 s hsR3 h)
  have hsball : s ∈ ball s0 R := by
    rw [mem_closedBall] at hs
    rw [mem_ball]
    linarith
  have hf1d : DifferentiableAt ℂ f1 s :=
    hf1.differentiableAt (closedBall_mem_nhds_of_mem hsball)
  rw [deriv_div_eq hfz hf1d hsne hf1s, Complex.add_re]
  linarith

/-- Norm of a complex power of a positive natural number. -/
private lemma norm_chapter7NatCpow {n : ℕ} (hn : 0 < n) (r : ℂ) :
    ‖chapter7NatCpow n r‖ = (n : ℝ) ^ r.re := by
  unfold chapter7NatCpow
  exact Complex.norm_natCast_cpow_of_pos hn r

/-- The Euler–Maclaurin expansion of `ζ s` with one Bernoulli correction, valid for `s ≠ 1` and
`Re s > -2`. -/
private lemma riemannZeta_eq_expansion {s : ℂ} (hs1 : s ≠ 1) (hs : -2 < s.re) :
    riemannZeta s = chapter7PowerSum (-s) 2 - chapter7NatCpow 2 (-s + 1) / (-s + 1)
      - chapter7NatCpow 2 (-s) / 2 - chapter7Entry1Term (-s) 2 0
      + powerSumRemainderFactor 1 (-s) * powerSumTail 1 (-s) 2 := by
  have hr : -s ≠ -1 := fun h => hs1 (neg_injective h)
  have h := chapter7PowerSum_exact_expansion (-s) 1 2 hr one_pos
    (by simp; linarith) (by norm_num)
  rw [neg_neg, Finset.sum_range_one] at h
  rw [h]
  ring

/-- The integral tail of the expansion is bounded when `Re s ≥ -3 / 2`. -/
private lemma norm_powerSumTail_le {C : ℝ} (hC : ∀ x, ‖bernoulliKernel (2 * 1 + 1) x‖ ≤ C) {s : ℂ}
    (hs : -3 / 2 ≤ s.re) : ‖powerSumTail 1 (-s) 2‖ ≤ 2 * C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set a : ℝ := -s.re - 3 with ha_def
  have ha : a < -1 := by linarith
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hg : IntegrableOn (fun x : ℝ => C * x ^ a) (Set.Ioi 2) :=
    (integrableOn_Ioi_rpow_of_lt ha h2).const_mul C
  have hexp : (-s - ((2 * 1 + 1 : ℕ) : ℂ)).re = a := by
    simp [ha_def]
  have hpoint : ∀ x ∈ Set.Ioi (2 : ℝ), ‖(x : ℂ) ^ (-s - ((2 * 1 + 1 : ℕ) : ℂ)) *
      (bernoulliKernel (2 * 1 + 1) x : ℂ)‖ ≤ C * x ^ a := by
    intro x hx
    have hxpos : 0 < x := h2.trans hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos, hexp, Complex.norm_real]
    calc x ^ a * ‖bernoulliKernel (2 * 1 + 1) x‖ ≤ x ^ a * C :=
          mul_le_mul_of_nonneg_left (hC x) (Real.rpow_nonneg hxpos.le a)
      _ = C * x ^ a := by ring
  have hnorm := norm_integral_le_of_norm_le hg
    ((ae_restrict_mem measurableSet_Ioi).mono hpoint)
  have hint : ∫ x in Set.Ioi (2 : ℝ), C * x ^ a = C * (-(2 : ℝ) ^ (a + 1) / (a + 1)) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt ha h2]
  have hbd : -(2 : ℝ) ^ (a + 1) / (a + 1) ≤ 2 := by
    have h1 : (2 : ℝ) ^ (a + 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    rw [div_le_iff_of_neg (by linarith)]
    linarith
  have hT : powerSumTail 1 (-s) 2 = ∫ x in Set.Ioi (2 : ℝ),
      (x : ℂ) ^ (-s - ((2 * 1 + 1 : ℕ) : ℂ)) * (bernoulliKernel (2 * 1 + 1) x : ℂ) := by
    rw [powerSumTail_eq_integral]
    norm_num
  rw [hT]
  calc _ ≤ ∫ x in Set.Ioi (2 : ℝ), C * x ^ a := hnorm
    _ = C * (-(2 : ℝ) ^ (a + 1) / (a + 1)) := hint
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left hbd hC0
    _ = 2 * C := by ring

/-- Comparison of real powers of `2`. -/
private lemma two_rpow_le {x : ℝ} {n : ℕ} (hx : x ≤ n) : (2 : ℝ) ^ x ≤ 2 ^ n := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hx

/-- **Polynomial growth of `ζ`.** For `Re s ≥ -3 / 2` and `|Im s| ≥ 1`,
`‖ζ s‖ ≤ C * (‖s‖ + 2) ^ 3`. -/
private lemma norm_riemannZeta_le : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -3 / 2 ≤ s.re → 1 ≤ |s.im| →
    ‖riemannZeta s‖ ≤ C * (‖s‖ + 2) ^ 3 := by
  obtain ⟨CB, hCB⟩ := bernoulliKernel_norm_le 1 one_pos
  have hCB0 : 0 ≤ CB := (norm_nonneg _).trans (hCB 0)
  refine ⟨16 + CB, by positivity, fun s hs him => ?_⟩
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at him
    norm_num at him
  rw [riemannZeta_eq_expansion hs1 (by linarith)]
  set x := ‖s‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  -- the pieces
  have hP : ‖chapter7PowerSum (-s) 2‖ ≤ 5 := by
    have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
    rw [chapter7PowerSum, hI, Finset.sum_pair (by norm_num)]
    refine (norm_add_le _ _).trans ?_
    rw [norm_chapter7NatCpow one_pos, norm_chapter7NatCpow two_pos]
    simp only [Nat.cast_one, Real.one_rpow, Nat.cast_ofNat, neg_re]
    have := two_rpow_le (x := -s.re) (n := 2) (by push_cast; linarith)
    norm_num at this ⊢
    linarith
  have hQ : ‖chapter7NatCpow 2 (-s + 1) / (-s + 1)‖ ≤ 8 := by
    rw [norm_div, norm_chapter7NatCpow two_pos]
    have h1 : 1 ≤ ‖-s + 1‖ := by
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      simpa using him
    have h2 := two_rpow_le (x := (-s + 1).re) (n := 3) (by simp; linarith)
    rw [div_le_iff₀ (by linarith)]
    norm_num at h2 ⊢
    nlinarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-s.re + 1)]
  have hR : ‖chapter7NatCpow 2 (-s) / 2‖ ≤ 2 := by
    rw [norm_div, norm_chapter7NatCpow two_pos]
    have h2 := two_rpow_le (x := (-s).re) (n := 2) (by simp; linarith)
    norm_num at h2 ⊢
    linarith
  have hT : ‖chapter7Entry1Term (-s) 2 0‖ ≤ x := by
    simp only [chapter7Entry1Term, chapter7FallingGammaRatio]
    norm_num [bernoulli_two]
    rw [norm_chapter7NatCpow two_pos]
    have h2 := two_rpow_le (x := (-s - 2 + 1).re) (n := 1) (by simp; linarith)
    norm_num at h2 ⊢
    nlinarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-s.re - 2 + 1)]
  have hF : ‖powerSumRemainderFactor 1 (-s)‖ ≤ (x + 2) ^ 3 / 6 := by
    have hFe : powerSumRemainderFactor 1 (-s) = (-s) * (-s - 1) * (-s - 2) / 6 := by
      rw [powerSumRemainderFactor_eq]
      simp [chapter7FallingGammaRatio, Finset.prod_range_succ, Nat.factorial]
    rw [hFe, norm_div, norm_mul, norm_mul, norm_neg]
    have h1 : ‖-s - 1‖ ≤ x + 1 := by
      refine (norm_sub_le _ _).trans ?_
      simp [hx]
    have h2 : ‖-s - 2‖ ≤ x + 2 := by
      refine (norm_sub_le _ _).trans ?_
      simp [hx]
    have h3 : ‖(6 : ℂ)‖ = 6 := by norm_num
    rw [h3]
    have : x * ‖-s - 1‖ * ‖-s - 2‖ ≤ (x + 2) ^ 3 := by
      calc x * ‖-s - 1‖ * ‖-s - 2‖ ≤ (x + 2) * (x + 2) * (x + 2) := by
            gcongr
            · linarith
            · linarith
        _ = (x + 2) ^ 3 := by ring
    linarith
  have hTail := norm_powerSumTail_le hCB hs
  have hsum : ‖chapter7PowerSum (-s) 2 - chapter7NatCpow 2 (-s + 1) / (-s + 1)
      - chapter7NatCpow 2 (-s) / 2 - chapter7Entry1Term (-s) 2 0
      + powerSumRemainderFactor 1 (-s) * powerSumTail 1 (-s) 2‖ ≤
      ‖chapter7PowerSum (-s) 2‖ + ‖chapter7NatCpow 2 (-s + 1) / (-s + 1)‖
      + ‖chapter7NatCpow 2 (-s) / 2‖ + ‖chapter7Entry1Term (-s) 2 0‖
      + ‖powerSumRemainderFactor 1 (-s)‖ * ‖powerSumTail 1 (-s) 2‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    gcongr
    refine (norm_sub_le _ _).trans ?_
    gcongr
    exact norm_sub_le _ _
  have hFT : ‖powerSumRemainderFactor 1 (-s)‖ * ‖powerSumTail 1 (-s) 2‖ ≤
      (x + 2) ^ 3 / 6 * (2 * CB) :=
    mul_le_mul hF hTail (norm_nonneg _) (by positivity)
  have hx2 : x + 2 ≤ (x + 2) ^ 3 := by
    have h1 : 1 ≤ (x + 2) ^ 2 := by nlinarith
    nlinarith
  nlinarith

/-- **A lower bound for `ζ` on the line `Re s = 3 / 2`.** Since `ζ(s) ∑ μ(n) n^{-s} = 1`,
`‖ζ s‖ ≥ 1 / ∑ n^{-3/2}` there. -/
private lemma le_norm_riemannZeta :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s.re = 3 / 2 → c ≤ ‖riemannZeta s‖ := by
  set S : ℝ := ∑' n : ℕ, ‖LSeries.term 1 (3 / 2 : ℂ) n‖ with hS_def
  have hsum1 : LSeriesSummable 1 (3 / 2 : ℂ) := by
    have := (ArithmeticFunction.LSeriesSummable_zeta_iff (s := (3 / 2 : ℂ))).mpr (by norm_num)
    exact (LSeriesSummable_congr _ (fun {n} hn => by simp [hn])).mp this
  have hsum : Summable (fun n : ℕ => ‖LSeries.term 1 (3 / 2 : ℂ) n‖) :=
    summable_norm_iff.mpr hsum1
  have hS : 0 < S := by
    have h1 : ‖LSeries.term 1 (3 / 2 : ℂ) 1‖ = 1 := by simp [LSeries.term]
    have := hsum.le_tsum 1 (fun n _ => norm_nonneg _)
    linarith
  refine ⟨1 / S, by positivity, fun s hs => ?_⟩
  have hs1 : 1 < s.re := by rw [hs]; norm_num
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs1
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs1] at h
  set Lμ := LSeries (fun n => ↑(ArithmeticFunction.moebius n)) s with hLμ
  have hle : ∀ n, ‖LSeries.term (fun n => ↑(ArithmeticFunction.moebius n)) s n‖ ≤
      ‖LSeries.term 1 (3 / 2 : ℂ) n‖ := by
    intro n
    calc _ ≤ ‖LSeries.term 1 s n‖ := LSeries.norm_term_le s (by
            simp only [Pi.one_apply, norm_one]
            have := ArithmeticFunction.abs_moebius_le_one (n := n)
            rw [Complex.norm_intCast]
            exact_mod_cast this)
      _ = ‖LSeries.term 1 (3 / 2 : ℂ) n‖ := by
            simp only [LSeries.norm_term_eq, hs]
            norm_num
  have hμ : ‖Lμ‖ ≤ S := by
    have hs2 : Summable (fun n => ‖LSeries.term (fun n => ↑(ArithmeticFunction.moebius n)) s n‖) :=
      hsum.of_nonneg_of_le (fun n => norm_nonneg _) hle
    calc ‖Lμ‖ ≤ ∑' n, ‖LSeries.term (fun n => ↑(ArithmeticFunction.moebius n)) s n‖ :=
          norm_tsum_le_tsum_norm hs2
      _ ≤ S := hs2.tsum_le_tsum hle hsum
  have h1 : ‖riemannZeta s‖ * ‖Lμ‖ = 1 := by rw [← norm_mul, h, norm_one]
  have hμpos : 0 < ‖Lμ‖ := by
    rcases (norm_nonneg Lμ).lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at h1
      simp at h1
  calc 1 / S ≤ 1 / ‖Lμ‖ := one_div_le_one_div_of_le hμpos hμ
    _ = ‖riemannZeta s‖ := by field_simp; linarith

/-- **The pole of `ζ` at `1`.** For real `σ > 1` close to `1`,
`-Re (ζ'(σ) / ζ(σ)) ≤ 1 / (σ - 1) + C`. -/
private lemma neg_re_logDeriv_riemannZeta_le_of_real :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + ε →
      -(deriv riemannZeta σ / riemannZeta σ).re ≤ 1 / (σ - 1) + C := by
  obtain ⟨C, hC⟩ := log_deriv_riemannZeta_add_inv_sub_bounded.bound
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hC
  obtain ⟨ε, hε, hC⟩ := hC
  refine ⟨ε, hε, max C 0, le_max_right _ _, fun σ h1 h2 => ?_⟩
  have hdist : dist (σ : ℂ) 1 < ε := by
    rw [Complex.dist_eq, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hne : (σ : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact_mod_cast h1.ne'
  have hb := hC hdist hne
  simp only [norm_one, mul_one] at hb
  have hre : (((σ : ℂ) - 1)⁻¹).re = 1 / (σ - 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv, Complex.ofReal_re,
      one_div]
  have hle := (neg_le_abs _).trans
    (Complex.abs_re_le_norm (deriv riemannZeta σ / riemannZeta σ + ((σ : ℂ) - 1)⁻¹))
  rw [Complex.add_re, hre] at hle
  have := le_max_left C 0
  linarith

/-- Termwise form of the inequality `3 + 4 cos θ + cos 2θ ≥ 0` for the Dirichlet series of the
von Mangoldt function. -/
private lemma re_term_vonMangoldt_comb_nonneg {n : ℕ} {σ t : ℝ} :
    0 ≤ 3 * (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) σ n).re
      + 4 * (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ + t * I) n).re
      + (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ + 2 * t * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  simp only [LSeries.term_of_ne_zero hn]
  set u : ℂ := (n : ℂ) ^ ((t : ℂ) * I) with hu
  set v : ℝ := (n : ℝ) ^ σ with hv
  have hv0 : 0 < v := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hnpos) σ
  have hu1 : ‖u‖ = 1 := by
    rw [hu, Complex.norm_natCast_cpow_of_pos hnpos]
    simp
  have hu0 : u ≠ 0 := fun h => by rw [h, norm_zero] at hu1; exact zero_ne_one hu1
  have hvc : (n : ℂ) ^ (σ : ℂ) = (v : ℂ) := by
    rw [hv, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  have h1 : (n : ℂ) ^ ((σ : ℂ) + t * I) = (v : ℂ) * u := by
    rw [Complex.cpow_add _ _ hn0, hvc]
  have h2 : (n : ℂ) ^ ((σ : ℂ) + 2 * t * I) = (v : ℂ) * u ^ 2 := by
    rw [Complex.cpow_add _ _ hn0, hvc,
      show (2 : ℂ) * t * I = ((2 : ℕ) : ℂ) * (t * I) by push_cast; ring, Complex.cpow_nat_mul]
  rw [hvc, h1, h2]
  set w : ℂ := u⁻¹ with hw
  have hw1 : ‖w‖ = 1 := by rw [hw, norm_inv, hu1, inv_one]
  set Λ : ℝ := ArithmeticFunction.vonMangoldt n with hΛ
  have hΛ0 : 0 ≤ Λ := ArithmeticFunction.vonMangoldt_nonneg
  have e1 : (Λ : ℂ) / (v : ℂ) = ((Λ / v : ℝ) : ℂ) := by push_cast; ring
  have e2 : (Λ : ℂ) / ((v : ℂ) * u) = ((Λ / v : ℝ) : ℂ) * w := by
    rw [hw]; push_cast; field_simp
  have e3 : (Λ : ℂ) / ((v : ℂ) * u ^ 2) = ((Λ / v : ℝ) : ℂ) * w ^ 2 := by
    rw [hw]; push_cast; field_simp
  rw [e1, e2, e3, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hnorm : w.re ^ 2 + w.im ^ 2 = 1 := by
    have := Complex.sq_norm w
    rw [hw1, Complex.normSq_apply] at this
    nlinarith
  have hsq : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by
    rw [pow_two, Complex.mul_re]
    ring
  rw [hsq]
  have hq : 0 ≤ Λ / v := div_nonneg hΛ0 hv0.le
  have : 0 ≤ 3 + 4 * w.re + (w.re ^ 2 - w.im ^ 2) := by nlinarith [sq_nonneg (1 + w.re)]
  nlinarith [mul_nonneg hq this]

/-- **The `3`–`4`–`1` inequality.** For real `σ > 1` and `t`,
`3 Re (-ζ'/ζ(σ)) + 4 Re (-ζ'/ζ(σ + i t)) + Re (-ζ'/ζ(σ + 2 i t)) ≥ 0`. -/
private lemma three_four_one {σ t : ℝ} (hσ : 1 < σ) :
    0 ≤ 3 * (-(deriv riemannZeta σ / riemannZeta σ)).re
      + 4 * (-(deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I))).re
      + (-(deriv riemannZeta (σ + 2 * t * I) / riemannZeta (σ + 2 * t * I))).re := by
  have h0 : 1 < (σ : ℂ).re := by simpa using hσ
  have h1 : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have h2 : 1 < ((σ : ℂ) + 2 * t * I).re := by simpa using hσ
  rw [← neg_div, ← neg_div, ← neg_div,
    ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div h0,
    ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div h1,
    ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div h2]
  have s0 := ArithmeticFunction.LSeriesSummable_vonMangoldt h0
  have s1 := ArithmeticFunction.LSeriesSummable_vonMangoldt h1
  have s2 := ArithmeticFunction.LSeriesSummable_vonMangoldt h2
  simp only [LSeries]
  rw [Complex.re_tsum s0, Complex.re_tsum s1, Complex.re_tsum s2]
  have r0 := (Complex.reCLM.summable s0)
  have r1 := (Complex.reCLM.summable s1)
  have r2 := (Complex.reCLM.summable s2)
  simp only [Complex.reCLM_apply] at r0 r1 r2
  rw [← r0.tsum_mul_left, ← r1.tsum_mul_left, ← (r0.mul_left 3).tsum_add (r1.mul_left 4),
    ← ((r0.mul_left 3).add (r1.mul_left 4)).tsum_add r2]
  exact tsum_nonneg fun n => re_term_vonMangoldt_comb_nonneg

/-- The entire function `(s - 1) ζ(s)` does not vanish on `Re s ≥ 1`. -/
private lemma riemannZeta₁_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta₁ s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · simp
  · intro h
    have := riemannZeta_eq_inv_sub_mul hs1
    rw [h, mul_zero] at this
    exact riemannZeta_ne_zero_of_one_le_re hs this

/-- **Bounded imaginary parts.** For every `T`, there is `ε > 0` such that `ζ` has no zero
`s ≠ 1` with `|Im s| ≤ T` and `Re s > 1 - ε`; this follows by compactness from the non-vanishing of
`(s - 1) ζ(s)` on `Re s ≥ 1`. -/
private lemma riemannZeta_ne_zero_of_abs_im_le (T : ℝ) : ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℂ, |s.im| ≤ T →
    1 - ε < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  set K : Set ℂ := (fun y : ℝ => (1 : ℂ) + y * I) '' Set.Icc (-T) T with hK_def
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  set U : Set ℂ := {z | riemannZeta₁ z ≠ 0} with hU_def
  have hU : IsOpen U := isOpen_ne_fun differentiable_riemannZeta₁.continuous continuous_const
  have hKU : K ⊆ U := by
    rintro _ ⟨y, _, rfl⟩
    exact riemannZeta₁_ne_zero_of_one_le_re (by simp)
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨δ, hδ, fun s hsT hsre hs1 => ?_⟩
  rcases le_or_gt 1 s.re with h | h
  · exact riemannZeta_ne_zero_of_one_le_re h
  · have hmem : s ∈ Metric.cthickening δ K := by
      apply Metric.mem_cthickening_of_dist_le s (1 + s.im * I) δ K
      · refine ⟨s.im, ⟨?_, ?_⟩, rfl⟩
        · linarith [neg_abs_le s.im]
        · linarith [le_abs_self s.im]
      · have he : s - (1 + s.im * I) = ((s.re - 1 : ℝ) : ℂ) := by
          apply Complex.ext <;> simp
        rw [Complex.dist_eq, he, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
        linarith
    have := hsub hmem
    rw [riemannZeta_eq_inv_sub_mul hs1]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hs1)) this

/-- Landau's lemma applied to `ζ` on the disc of radius `3` around `3 / 2 + i y`, for `|y| ≥ 4` and
`1 < σ ≤ 3 / 2`, with and without a zero `β + i y`, `β ≥ 1 / 2`. -/
private lemma neg_re_logDeriv_riemannZeta_le {C0 c1 : ℝ} (hC0 : 0 < C0) (hc1 : 0 < c1)
    (hpoly : ∀ s : ℂ, -3 / 2 ≤ s.re → 1 ≤ |s.im| → ‖riemannZeta s‖ ≤ C0 * (‖s‖ + 2) ^ 3)
    (hlow : ∀ s : ℂ, s.re = 3 / 2 → c1 ≤ ‖riemannZeta s‖)
    {y σ : ℝ} (hy : 4 ≤ |y|) (hσ1 : 1 < σ) (hσ2 : σ ≤ 3 / 2) :
    -(deriv riemannZeta (σ + y * I) / riemannZeta (σ + y * I)).re ≤
      24 * Real.log (max (C0 / c1) 1 * (|y| + 7) ^ 3) ∧
    ∀ β : ℝ, 1 / 2 ≤ β → riemannZeta (β + y * I) = 0 →
      -(deriv riemannZeta (σ + y * I) / riemannZeta (σ + y * I)).re ≤
        24 * Real.log (max (C0 / c1) 1 * (|y| + 7) ^ 3) - 1 / (σ - β) := by
  set s0 : ℂ := ((3 / 2 : ℝ) : ℂ) + y * I with hs0
  set M := Real.log (max (C0 / c1) 1 * (|y| + 7) ^ 3) with hM_def
  have hmax : 1 ≤ max (C0 / c1) 1 := le_max_right _ _
  have hy7 : 1 < (|y| + 7) ^ 3 := by
    have : 1 < |y| + 7 := by linarith [abs_nonneg y]
    exact one_lt_pow₀ this (by norm_num)
  have hprod : 1 < max (C0 / c1) 1 * (|y| + 7) ^ 3 := by nlinarith
  have hexpM : Real.exp M = max (C0 / c1) 1 * (|y| + 7) ^ 3 := Real.exp_log (by linarith)
  have hM : 0 < M := Real.log_pos hprod
  have hs0re : s0.re = 3 / 2 := by simp [hs0]
  have hs0im : s0.im = y := by simp [hs0]
  have hgeom : ∀ z ∈ closedBall s0 3, |z.re - 3 / 2| ≤ 3 ∧ |z.im - y| ≤ 3 := by
    intro z hz
    rw [mem_closedBall, dist_eq] at hz
    constructor
    · have := Complex.abs_re_le_norm (z - s0)
      rw [Complex.sub_re, hs0re] at this
      linarith
    · have := Complex.abs_im_le_norm (z - s0)
      rw [Complex.sub_im, hs0im] at this
      linarith
  have him1 : ∀ z ∈ closedBall s0 3, 1 ≤ |z.im| := by
    intro z hz
    have h1 := (hgeom z hz).2
    have h2 := abs_sub_abs_le_abs_sub y z.im
    rw [abs_sub_comm] at h1
    linarith
  have hne1 : ∀ z ∈ closedBall s0 3, z ≠ 1 := by
    intro z hz h
    have := him1 z hz
    rw [h] at this
    norm_num at this
  have hdiff : DifferentiableOn ℂ riemannZeta (closedBall s0 3) := fun z hz =>
    (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
  have hf0 : riemannZeta s0 ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hs0re]; norm_num)
  have hs0norm : ‖s0‖ ≤ 3 / 2 + |y| := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
    norm_num
  have hB : ∀ z ∈ sphere s0 3, ‖riemannZeta z‖ ≤ Real.exp M * ‖riemannZeta s0‖ := by
    intro z hz
    have hz' := sphere_subset_closedBall hz
    have h1 : -3 / 2 ≤ z.re := by linarith [(abs_le.mp (hgeom z hz').1).1]
    have h3 : ‖z‖ + 2 ≤ |y| + 7 := by
      have hzs : ‖z - s0‖ = 3 := by rw [← dist_eq]; exact hz
      have : ‖z‖ ≤ ‖z - s0‖ + ‖s0‖ := by
        calc ‖z‖ = ‖(z - s0) + s0‖ := by ring_nf
          _ ≤ ‖z - s0‖ + ‖s0‖ := norm_add_le _ _
      linarith
    have hlow0 := hlow s0 hs0re
    calc ‖riemannZeta z‖ ≤ C0 * (‖z‖ + 2) ^ 3 := hpoly z h1 (him1 z hz')
      _ ≤ C0 * (|y| + 7) ^ 3 := by gcongr
      _ = C0 / c1 * (|y| + 7) ^ 3 * c1 := by field_simp
      _ ≤ max (C0 / c1) 1 * (|y| + 7) ^ 3 * ‖riemannZeta s0‖ := by
          gcongr
          exact le_max_left _ _
      _ = Real.exp M * ‖riemannZeta s0‖ := by rw [hexpM]
  have hs : (σ : ℂ) + y * I ∈ closedBall s0 (3 / 6) := by
    rw [mem_closedBall, dist_eq]
    have he : (σ : ℂ) + y * I - s0 = ((σ - 3 / 2 : ℝ) : ℂ) := by
      rw [hs0]; push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hzre : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re < 1 := by
    intro ρ hρ
    by_contra h
    push Not at h
    exact riemannZeta_ne_zero_of_one_le_re h hρ
  have hz : ∀ ρ ∈ closedBall s0 (3 / 3), riemannZeta ρ = 0 → ρ.re < ((σ : ℂ) + y * I).re := by
    intro ρ _ hρ
    have := hzre ρ hρ
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  refine ⟨?_, ?_⟩
  · have := neg_re_logDeriv_le (by norm_num) hM hdiff hf0 hB hs hz
    linarith
  · intro β hβ hζβ
    have hβ1 : β < 1 := by
      have := hzre _ hζβ
      simpa using this
    have hρ0 : (β : ℂ) + y * I ∈ closedBall s0 (3 / 3) := by
      rw [mem_closedBall, dist_eq]
      have he : (β : ℂ) + y * I - s0 = ((β - 3 / 2 : ℝ) : ℂ) := by
        rw [hs0]; push_cast; ring
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have := neg_re_logDeriv_le_of_zero (by norm_num) hM hdiff hf0 hB hs hz hρ0 hζβ
    have hre : (1 / ((σ : ℂ) + y * I - (β + y * I))).re = 1 / (σ - β) := by
      have he : (σ : ℂ) + y * I - (β + y * I) = ((σ - β : ℝ) : ℂ) := by push_cast; ring
      rw [he, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [hre] at this
    linarith

/-- Comparison of logarithms used to bound the constants `M` by a multiple of
`log (2 + |γ|)`. -/
private lemma log_mul_pow_le {m γ y L : ℝ} (hm : 1 ≤ m) (hL : L = Real.log (2 + |γ|)) (hL1 : 1 ≤ L)
    (hy : |y| + 7 ≤ 7 * (2 + |γ|)) :
    Real.log (m * (|y| + 7) ^ 3) ≤ (Real.log m + 3 * Real.log 7 + 3) * L := by
  have hm0 : 0 < m := by linarith
  have hy0 : 0 < |y| + 7 := by linarith [abs_nonneg y]
  rw [Real.log_mul hm0.ne' (by positivity), Real.log_pow]
  have h1 : Real.log (|y| + 7) ≤ Real.log 7 + L := by
    rw [hL, ← Real.log_mul (by norm_num) (by linarith [abs_nonneg γ])]
    exact Real.log_le_log hy0 hy
  have hlm : 0 ≤ Real.log m := Real.log_nonneg hm
  have hl7 : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
  push_cast
  nlinarith

/-- **Classical zero-free region for the Riemann zeta function.** There is a constant `c > 0`
such that `ζ(s) ≠ 0` for every complex number `s ≠ 1` with `Re s > 1 - c / log (2 + |Im s|)`.
The point `s = 1`, where `ζ` has its pole, is excluded.

Source: T. Tao, *254A, Notes 2: Complex-analytic multiplicative number theory* (2014),
Proposition 38,
<https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/>.
Its proof combines the inequality `3 + 4 cos θ + cos 2θ ≥ 0` with the approximate formula for
`ζ'/ζ` near a zero (Proposition 19 there), which rests on Jensen's formula and the
Borel–Carathéodory theorem. -/
theorem riemannZeta_ne_zero_of_classical_zero_free_region :
    ∃ c : ℝ, 0 < c ∧
      ∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (2 + |s.im|) < s.re → riemannZeta s ≠ 0 := by
  obtain ⟨C0, hC0, hpoly⟩ := norm_riemannZeta_le
  obtain ⟨c1, hc1, hlow⟩ := le_norm_riemannZeta
  obtain ⟨ε, hε, C2, hC2, hpole⟩ := neg_re_logDeriv_riemannZeta_le_of_real
  obtain ⟨ε', hε', hsmall⟩ := riemannZeta_ne_zero_of_abs_im_le 4
  set m : ℝ := max (C0 / c1) 1 with hm_def
  have hm : 1 ≤ m := le_max_right _ _
  set A : ℝ := Real.log m + 3 * Real.log 7 + 3 with hA_def
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm
  have hlog7 : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
  have hA : 3 ≤ A := by linarith
  set K : ℝ := 3 * C2 + 120 * A with hK_def
  have hK : 0 < K := by positivity
  set δ : ℝ := min (ε / 2) (min (1 / 4) (1 / (2 * K))) with hδ_def
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hδ4 : δ ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδK : δ ≤ 1 / (2 * K) := (min_le_right _ _).trans (min_le_right _ _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := min (δ / 7) (min (ε' * Real.log 2) (1 / 2)) with hc_def
  have hc : 0 < c := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  refine ⟨c, hc, fun s hs1 hsre hζ => ?_⟩
  set L := Real.log (2 + |s.im|) with hL_def
  have hL2 : Real.log 2 ≤ L :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hLpos : 0 < L := hlog2.trans_le hL2
  have hsre1 : s.re < 1 := by
    by_contra h
    push Not at h
    exact riemannZeta_ne_zero_of_one_le_re h hζ
  rcases le_or_gt |s.im| 4 with hsm | hlarge
  · -- bounded imaginary part: compactness
    refine hsmall s hsm ?_ hs1 hζ
    have : c / L ≤ ε' := by
      calc c / L ≤ c / Real.log 2 := div_le_div_of_nonneg_left hc.le hlog2 hL2
        _ ≤ ε' := by
          rw [div_le_iff₀ hlog2]
          exact (min_le_right _ _).trans (min_le_left _ _)
    linarith
  · -- large imaginary part
    have hL1 : 1 ≤ L := by
      rw [hL_def, Real.le_log_iff_exp_le (by positivity)]
      have := Real.exp_one_lt_d9
      linarith
    have hcL : c / L ≤ c := div_le_self hc.le hL1
    by_cases hhalf : s.re < 1 / 2
    · have : c ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
      linarith
    push Not at hhalf
    set γ := s.im with hγ
    set β := s.re with hβ
    have hs_eq : s = (β : ℂ) + γ * I := (Complex.re_add_im s).symm
    set σ0 : ℝ := 1 + δ / L with hσ0
    have hδL : δ / L ≤ δ := div_le_self hδ.le hL1
    have hδL0 : 0 < δ / L := div_pos hδ hLpos
    have hσ0_1 : 1 < σ0 := by linarith
    have hσ0_2 : σ0 ≤ 3 / 2 := by linarith
    have hσ0_ε : σ0 < 1 + ε := by linarith
    have hγ4 : 4 ≤ |γ| := hlarge.le
    have h2γ4 : 4 ≤ |2 * γ| := by
      rw [abs_mul]
      norm_num
      linarith
    obtain ⟨-, hzero⟩ := neg_re_logDeriv_riemannZeta_le hC0 hc1 hpoly hlow hγ4 hσ0_1 hσ0_2
    obtain ⟨hno, -⟩ := neg_re_logDeriv_riemannZeta_le hC0 hc1 hpoly hlow h2γ4 hσ0_1 hσ0_2
    have hii := hzero β hhalf (by rw [← hs_eq]; exact hζ)
    have hi := hpole σ0 hσ0_1 hσ0_ε
    have h341 := three_four_one (t := γ) hσ0_1
    have hcast : ((σ0 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) = (σ0 : ℂ) + 2 * γ * I := by
      push_cast
      ring
    rw [hcast] at hno
    have hMγ : Real.log (max (C0 / c1) 1 * (|γ| + 7) ^ 3) ≤ A * L :=
      log_mul_pow_le (y := γ) hm hL_def hL1 (by linarith [abs_nonneg γ])
    have hM2γ : Real.log (max (C0 / c1) 1 * (|2 * γ| + 7) ^ 3) ≤ A * L :=
      log_mul_pow_le (y := 2 * γ) hm hL_def hL1 (by
        rw [abs_mul]
        norm_num
        linarith [abs_nonneg γ])
    have hσβ : 0 < σ0 - β := by linarith
    have hδ0 : δ ≠ 0 := hδ.ne'
    have hL0 : L ≠ 0 := hLpos.ne'
    have hpole' : 1 / (σ0 - 1) = L / δ := by
      rw [hσ0, add_sub_cancel_left, one_div_div]
    rw [hpole'] at hi
    simp only [Complex.neg_re] at h341
    have key : 4 * (1 / (σ0 - β)) ≤ 3 * (L / δ) + K * L := by
      have hC2L : C2 ≤ C2 * L := le_mul_of_one_le_right hC2 hL1
      rw [hK_def]
      nlinarith
    have hD : σ0 - β < 8 * δ / 7 / L := by
      have h1 : 1 - β < δ / 7 / L := by
        have : c / L ≤ δ / 7 / L := div_le_div_of_nonneg_right (min_le_left _ _) hLpos.le
        linarith
      have h3 : σ0 - β = (1 - β) + δ / L := by rw [hσ0]; ring
      have h4 : δ / 7 / L + δ / L = 8 * δ / 7 / L := by ring
      linarith
    have e1 : 4 ≤ (3 * (L / δ) + K * L) * (σ0 - β) := by
      have h := mul_le_mul_of_nonneg_right key hσβ.le
      rw [mul_assoc, one_div_mul_cancel hσβ.ne', mul_one] at h
      exact h
    have e2 : (3 * (L / δ) + K * L) * (σ0 - β) < (3 * (L / δ) + K * L) * (8 * δ / 7 / L) :=
      mul_lt_mul_of_pos_left hD (by positivity)
    have e3 : (3 * (L / δ) + K * L) * (8 * δ / 7 / L) = 24 / 7 + 8 * K * δ / 7 := by
      field_simp
      ring
    have e4 : K * δ ≤ 1 / 2 := by
      rw [le_div_iff₀ (by positivity)] at hδK
      linarith
    linarith

end MathlibExt.NumberTheory.ZetaClassicalZeroFreeRegionWanted
