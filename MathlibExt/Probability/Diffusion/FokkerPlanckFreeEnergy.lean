/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Free-energy decay for the gradient-drift Fokker–Planck equation

The overdamped Langevin diffusion `dX = -Ψ'(X) dt + √(2D) dW` on an interval `[a, b]` with
reflecting ends has density `p(t, x)` solving the Fokker–Planck equation

`∂ₜ p = ∂ₓ (p Ψ' + D ∂ₓ p)` on `[a, b]`, with zero flux `p Ψ' + D ∂ₓ p = 0` at `a` and `b`.

Its free energy `F(t) = ∫ₐᵇ (Ψ p + D p log p) dx` (potential energy plus `D` times the negative
entropy) satisfies the **dissipation identity**

`F'(t) = -∫ₐᵇ p (Ψ' + D ∂ₓ log p)² dx ≤ 0`,

so `F` is nonincreasing along the flow. Jordan, Kinderlehrer and Otto (1998) showed, on `ℝⁿ`,
that the Fokker–Planck equation is the gradient flow of this free energy for the Wasserstein
metric; that variational characterization is not formalized here, only the dissipation
identity and the monotonicity it implies, in one dimension with no-flux boundary.

We assume `p` is `C²` in `(t, x)` and positive at every time of an open set of times `I`,
and `Ψ` is `C²`. The identity is algebraic in `D` and holds for every real `D`. (Hypotheses on
all times `t ∈ ℝ` would be nearly vacuous: positive solutions defined for all past times are
essentially stationary.)

## Main results

* `hasDerivAt_freeEnergy`: the dissipation identity.
* `antitoneOn_freeEnergy`: the free energy is nonincreasing in time.
* `hasDerivAt_mass`: the total mass `∫ₐᵇ p` is conserved.

## References

* R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck
  equation*, SIAM J. Math. Anal. 29 (1998), 1–17.
* P. A. Markowich, C. Villani, *On the trend to equilibrium for the Fokker–Planck equation: an
  interplay between physics and functional analysis*, Mat. Contemp. 19 (2000), 1–29.
-/

@[expose] public section

open Set intervalIntegral

namespace MathlibExt.Probability.FokkerPlanck

private theorem time_hasDerivAt (p : ℝ → ℝ → ℝ)
    (hp : ContDiff ℝ 2 (Function.uncurry p)) (t x : ℝ) :
    HasDerivAt (fun s => p s x)
      (fderiv ℝ (Function.uncurry p) (t, x) (1, 0)) t := by
  have h := (hp.differentiable (by norm_num) (t, x)).hasFDerivAt
  simpa [Function.comp_def] using
    h.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))

private theorem continuous_timeDeriv (p : ℝ → ℝ → ℝ)
    (hp : ContDiff ℝ 2 (Function.uncurry p)) :
    Continuous (fun z : ℝ × ℝ => deriv (fun s => p s z.2) z.1) := by
  have heq : (fun z : ℝ × ℝ => deriv (fun s => p s z.2) z.1) =
      fun z => fderiv ℝ (Function.uncurry p) z (1, 0) := by
    funext z
    exact (time_hasDerivAt p hp z.1 z.2).deriv
  rw [heq]
  exact (hp.fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const

private theorem spatial_contDiff (p : ℝ → ℝ → ℝ)
    (hp : ContDiff ℝ 2 (Function.uncurry p)) (t : ℝ) : ContDiff ℝ 2 (p t) := by
  exact hp.comp (contDiff_const.prodMk contDiff_id)

private theorem integral_hasDerivAt (F F' : ℝ → ℝ → ℝ) (a b t : ℝ)
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (hderiv : ∀ s x, HasDerivAt (fun r => F r x) (F' s x) s) :
    HasDerivAt (fun s => ∫ x in a..b, F s x) (∫ x in a..b, F' t x) t := by
  have hcompact : IsCompact (Icc (t - 1) (t + 1) ×ˢ uIcc a b) :=
    isCompact_Icc.prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hF'.continuousOn
  have hc (s : ℝ) : Continuous (F s) := hF.comp (continuous_const.prodMk continuous_id)
  have hc' (s : ℝ) : Continuous (F' s) :=
    hF'.comp (continuous_const.prodMk continuous_id)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Icc_mem_nhds (by linarith : t - 1 < t) (by linarith : t < t + 1))
    (Filter.Eventually.of_forall fun s => (hc s).aestronglyMeasurable)
    ((hc t).intervalIntegrable a b) (hc' t).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun x hx s hs => hC (s, x) ⟨hs, uIoc_subset_uIcc hx⟩)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C)
      MeasureTheory.volume a b)
    (MeasureTheory.ae_of_all _ fun x _ s _ => hderiv s x)).2

private theorem density_integral_hasDerivAt (p : ℝ → ℝ → ℝ)
    (hp : ContDiff ℝ 2 (Function.uncurry p)) (a b t : ℝ) :
    HasDerivAt (fun s => ∫ x in a..b, p s x)
      (∫ x in a..b, deriv (fun s => p s x) t) t := by
  exact integral_hasDerivAt p (fun s x => deriv (fun r => p r x) s) a b t
    hp.continuous (continuous_timeDeriv p hp)
    (fun s x => (time_hasDerivAt p hp s x).differentiableAt.hasDerivAt)

private theorem integral_hasDerivAt_local (F F' : ℝ → ℝ → ℝ) (a b t δ : ℝ) (hδ : 0 < δ)
    (hF : ContinuousOn (Function.uncurry F) (Icc (t - δ) (t + δ) ×ˢ uIcc a b))
    (hF' : ContinuousOn (Function.uncurry F') (Icc (t - δ) (t + δ) ×ˢ uIcc a b))
    (hderiv : ∀ s ∈ Icc (t - δ) (t + δ), ∀ x ∈ uIcc a b,
      HasDerivAt (fun r => F r x) (F' s x) s) :
    HasDerivAt (fun s => ∫ x in a..b, F s x) (∫ x in a..b, F' t x) t := by
  have hK : IsCompact (Icc (t - δ) (t + δ) ×ˢ uIcc a b) := isCompact_Icc.prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'
  have htm : t ∈ Icc (t - δ) (t + δ) := ⟨by linarith, by linarith⟩
  have hc : ∀ s ∈ Icc (t - δ) (t + δ), ContinuousOn (F s) (uIcc a b) := fun s hs =>
    hF.comp (continuous_const.prodMk continuous_id).continuousOn fun x hx => ⟨hs, hx⟩
  have hc' : ContinuousOn (F' t) (uIcc a b) :=
    hF'.comp (continuous_const.prodMk continuous_id).continuousOn fun x hx => ⟨htm, hx⟩
  have hmeas : ∀ s ∈ Icc (t - δ) (t + δ),
      MeasureTheory.AEStronglyMeasurable (F s) (MeasureTheory.volume.restrict (uIoc a b)) :=
    fun s hs => ((hc s hs).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hnhds : Icc (t - δ) (t + δ) ∈ nhds t :=
    Icc_mem_nhds (by linarith) (by linarith)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hnhds
    (Filter.eventually_of_mem hnhds hmeas) ((hc t htm).intervalIntegrable)
    ((hc'.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc)
    (MeasureTheory.ae_of_all _ fun x hx s hs => hC (s, x) ⟨hs, uIoc_subset_uIcc hx⟩)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C)
      MeasureTheory.volume a b)
    (MeasureTheory.ae_of_all _ fun x hx s hs => hderiv s hs x (uIoc_subset_uIcc hx))).2

/-- The **free energy** `F(t) = ∫ₐᵇ (Ψ p + D p log p) dx` of the density `p(t, ·)` on
`[a, b]` (potential `Ψ`, diffusion coefficient `D`). -/
noncomputable def freeEnergy (Ψ : ℝ → ℝ) (D a b : ℝ) (p : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in a..b, (Ψ x * p t x + D * (p t x * Real.log (p t x)))

/-- The (negative) probability flux `p Ψ' + D ∂ₓ p` of the gradient-drift Fokker–Planck
equation at `(t, x)`; the flux itself is `-(p Ψ' + D ∂ₓ p)`. -/
noncomputable def negFlux (Ψ : ℝ → ℝ) (D : ℝ) (p : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  p t x * deriv Ψ x + D * deriv (fun y => p t y) x

/-- `p` solves the **gradient-drift Fokker–Planck equation** `∂ₜ p = ∂ₓ (p Ψ' + D ∂ₓ p)` on
`[a, b]` with **zero flux** at both ends, for times `t ∈ I`. -/
structure IsNoFluxSolutionOn (Ψ : ℝ → ℝ) (D a b : ℝ) (I : Set ℝ) (p : ℝ → ℝ → ℝ) : Prop where
  /-- The Fokker–Planck equation on `[a, b]`. -/
  pde : ∀ t ∈ I, ∀ x ∈ Icc a b, deriv (fun s => p s x) t = deriv (negFlux Ψ D p t) x
  /-- Zero flux at the left end. -/
  flux_left : ∀ t ∈ I, negFlux Ψ D p t a = 0
  /-- Zero flux at the right end. -/
  flux_right : ∀ t ∈ I, negFlux Ψ D p t b = 0

private theorem flux_contDiff (Ψ : ℝ → ℝ) (D : ℝ) (p : ℝ → ℝ → ℝ)
    (hΨ : ContDiff ℝ 2 Ψ) (hp : ContDiff ℝ 2 (Function.uncurry p)) (t : ℝ) :
    ContDiff ℝ 1 (negFlux Ψ D p t) := by
  have hΨ' : ContDiff ℝ 1 (deriv Ψ) := hΨ.deriv' (n := 1)
  have hp' : ContDiff ℝ 1 (deriv (p t)) := (spatial_contDiff p hp t).deriv' (n := 1)
  exact ((spatial_contDiff p hp t).of_le (by norm_num)).mul hΨ' |>.add
    (contDiff_const.mul hp')

/-- **Dissipation identity**: let `p` be `C²` in `(t, x)`, positive for times in an open set
`I`, and solve the no-flux gradient-drift Fokker–Planck equation on `[a, b]` for `t ∈ I`, with
`C²` potential `Ψ` (any real `D`). Then for `t ∈ I`,
`F'(t) = -∫ₐᵇ p (Ψ' + D ∂ₓ log p)² dx`. Only the values of `p` on `[a, b]` enter `F`;
positivity is asked of the whole `C²` function `p t` so that `log (p t)` is `C²`. -/
theorem hasDerivAt_freeEnergy {Ψ : ℝ → ℝ} {D a b : ℝ} {I : Set ℝ} {p : ℝ → ℝ → ℝ}
    (hab : a ≤ b) (hI : IsOpen I) (hΨ : ContDiff ℝ 2 Ψ) (hp : ContDiff ℝ 2 (Function.uncurry p))
    (hpos : ∀ t ∈ I, ∀ x, 0 < p t x) (hsol : IsNoFluxSolutionOn Ψ D a b I p) {t : ℝ}
    (ht : t ∈ I) :
    HasDerivAt (freeEnergy Ψ D a b p)
      (-∫ x in a..b, p t x * (deriv Ψ x + D * deriv (fun y => Real.log (p t y)) x) ^ 2) t := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hI t ht
  set δ := ε / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hsub : Icc (t - δ) (t + δ) ⊆ I := fun s hs => hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2])
  let K := Icc (t - δ) (t + δ) ×ˢ uIcc a b
  let A : ℝ → ℝ → ℝ := fun s x => Ψ x + D * Real.log (p s x) + D
  have hne : ∀ s ∈ I, ∀ x, p s x ≠ 0 := fun s hs x => ne_of_gt (hpos s hs x)
  have hneK : ∀ z ∈ K, p z.1 z.2 ≠ 0 := fun z hz => hne z.1 (hsub hz.1) z.2
  have hlog : ContinuousOn (fun z : ℝ × ℝ => Real.log (p z.1 z.2)) K :=
    hp.continuous.continuousOn.log hneK
  have hA : ContinuousOn (Function.uncurry A) K :=
    (((hΨ.continuous.comp continuous_snd).continuousOn.add
      (continuousOn_const.mul hlog))).add continuousOn_const
  have hE : ContinuousOn (fun z : ℝ × ℝ =>
      Ψ z.2 * p z.1 z.2 + D * (p z.1 z.2 * Real.log (p z.1 z.2))) K :=
    ((hΨ.continuous.comp continuous_snd).mul hp.continuous).continuousOn.add
      (continuousOn_const.mul (hp.continuous.continuousOn.mul hlog))
  have hdt : HasDerivAt (freeEnergy Ψ D a b p)
      (∫ x in a..b, A t x * deriv (fun s => p s x) t) t := by
    apply integral_hasDerivAt_local
      (fun s x => Ψ x * p s x + D * (p s x * Real.log (p s x)))
      (fun s x => A s x * deriv (fun r => p r x) s) a b t δ hδ hE
      (hA.mul (continuous_timeDeriv p hp).continuousOn)
    intro s hs x _
    have hd := (time_hasDerivAt p hp s x).differentiableAt.hasDerivAt
    have hnx := hne s (hsub hs) x
    convert (hd.const_mul (Ψ x)).add ((hd.mul (hd.log hnx)).const_mul D) using 1
    dsimp [A]
    field_simp [hnx]
    ring
  have hpt := spatial_contDiff p hp t
  have hplog := hpt.log (hne t ht)
  have hflux := flux_contDiff Ψ D p hΨ hp t
  let B : ℝ → ℝ := fun x => deriv Ψ x + D * deriv (fun y => Real.log (p t y)) x
  have hB : Continuous B := (hΨ.continuous_deriv (by norm_num)).add
    (continuous_const.mul (hplog.continuous_deriv (by norm_num)))
  have hdA (x : ℝ) : HasDerivAt (A t) (B x) x := by
    exact ((hΨ.differentiable (by norm_num) x).hasDerivAt.add
      ((hplog.differentiable (by norm_num) x).hasDerivAt.const_mul D)).add_const D
  have hparts := integral_mul_deriv_eq_deriv_mul
    (fun x (_ : x ∈ uIcc a b) => hdA x)
    (fun x (_ : x ∈ uIcc a b) => (hflux.differentiable (by norm_num) x).hasDerivAt)
    (hB.intervalIntegrable a b)
    ((hflux.continuous_deriv (by norm_num)).intervalIntegrable a b)
  have heq : (∫ x in a..b, A t x * deriv (fun s => p s x) t) =
      -∫ x in a..b, p t x * (B x) ^ 2 := by
    calc
      (∫ x in a..b, A t x * deriv (fun s => p s x) t) =
          ∫ x in a..b, A t x * deriv (negFlux Ψ D p t) x := by
        apply integral_congr
        intro x hx
        exact congrArg (fun r => A t x * r)
          (hsol.pde t ht x (by simpa [uIcc_of_le hab] using hx))
      _ = -∫ x in a..b, B x * negFlux Ψ D p t x := by
        simpa [hsol.flux_left t ht, hsol.flux_right t ht] using hparts
      _ = -∫ x in a..b, p t x * (B x) ^ 2 := by
        congr 1
        apply integral_congr
        intro x _
        have hdx := (hpt.differentiable (by norm_num) x).hasDerivAt
        have hlogdx := (hdx.log (hne t ht x)).deriv
        dsimp [B, negFlux]
        rw [hlogdx]
        field_simp [hne t ht x]
  rw [heq] at hdt
  exact hdt

/-- **Free-energy decay**: under the hypotheses of `hasDerivAt_freeEnergy`, on a convex open
time set `I` the free energy is nonincreasing. -/
theorem antitoneOn_freeEnergy {Ψ : ℝ → ℝ} {D a b : ℝ} {I : Set ℝ} {p : ℝ → ℝ → ℝ}
    (hab : a ≤ b) (hI : IsOpen I) (hIc : Convex ℝ I) (hΨ : ContDiff ℝ 2 Ψ)
    (hp : ContDiff ℝ 2 (Function.uncurry p)) (hpos : ∀ t ∈ I, ∀ x, 0 < p t x)
    (hsol : IsNoFluxSolutionOn Ψ D a b I p) : AntitoneOn (freeEnergy Ψ D a b p) I := by
  have hd : ∀ t ∈ I, HasDerivAt (freeEnergy Ψ D a b p) _ t := fun t ht =>
    hasDerivAt_freeEnergy hab hI hΨ hp hpos hsol ht
  refine antitoneOn_of_deriv_nonpos hIc ?_ ?_ ?_
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    exact neg_nonpos.mpr (integral_nonneg hab fun x _ =>
      mul_nonneg (hpos t (interior_subset ht) x).le (sq_nonneg _))

/-- **Mass conservation**: if `p` is `C²` and solves the no-flux equation on `[a, b]` for times
in `I` (positivity is not needed), the total mass `∫ₐᵇ p(t, x) dx` has zero time derivative at
every `t ∈ I`. -/
theorem hasDerivAt_mass {Ψ : ℝ → ℝ} {D a b : ℝ} {I : Set ℝ} {p : ℝ → ℝ → ℝ} (hab : a ≤ b)
    (hΨ : ContDiff ℝ 2 Ψ) (hp : ContDiff ℝ 2 (Function.uncurry p))
    (hsol : IsNoFluxSolutionOn Ψ D a b I p) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => ∫ x in a..b, p s x) 0 t := by
  have hflux := flux_contDiff Ψ D p hΨ hp t
  have heq : (∫ x in a..b, deriv (fun s => p s x) t) = 0 := by
    calc
      (∫ x in a..b, deriv (fun s => p s x) t) =
          ∫ x in a..b, deriv (negFlux Ψ D p t) x := by
        apply integral_congr
        intro x hx
        exact hsol.pde t ht x (by simpa [uIcc_of_le hab] using hx)
      _ = negFlux Ψ D p t b - negFlux Ψ D p t a := by
        exact integral_eq_sub_of_hasDerivAt
          (fun x _ => (hflux.differentiable (by norm_num) x).hasDerivAt)
          ((hflux.continuous_deriv (by norm_num)).intervalIntegrable a b)
      _ = 0 := by rw [hsol.flux_left t ht, hsol.flux_right t ht, sub_self]
  rw [← heq]
  exact density_integral_hasDerivAt p hp a b t

end MathlibExt.Probability.FokkerPlanck
