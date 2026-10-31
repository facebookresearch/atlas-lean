/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ItoIntegral
public import MathlibExt.Probability.ItoRiemannSums
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import MathlibExt.Probability.BrownianQuadraticVariation
import MathlibExt.Probability.Distributions.GaussianL2Limit
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Independence.Integration

/-!
# The pathwise Langevin solution is an Ornstein–Uhlenbeck process

Let `B` be a Brownian motion (`IsBrownianReal`: Brownian finite-dimensional laws and almost surely
continuous paths), `θ > 0`, `σ` real, and `X₀ ~ N(0, v)` independent of `B`. The pathwise solution
`X t = ouPathSolution θ σ X₀ B t` of the Langevin equation `dX = -θ X dt + σ dB` is a centered
Gaussian process with covariance
`E[X s X t] = e^{-θ(s+t)} (v + σ² (e^{2θ (s ∧ t)} - 1) / (2θ))`.
With `X₀ = 0` this is the Ornstein–Uhlenbeck process started at `0`, and with
`v = σ² / (2θ)` the stationary Ornstein–Uhlenbeck process.

## Main results

* `ProbabilityTheory.IsBrownianReal.isGaussianProcess_ouPathSolution`: Gaussianity, mean and
  covariance of the pathwise solution for an independent Gaussian start.
* `ProbabilityTheory.IsBrownianReal.isOrnsteinUhlenbeckFromZero_ouPathSolution`: started at `0`,
  the pathwise solution is an Ornstein–Uhlenbeck process started at `0`.
* `ProbabilityTheory.IsBrownianReal.isStationaryOrnsteinUhlenbeck_ouPathSolution`: started from
  an independent `N(0, σ² / (2θ))` variable, it is a stationary Ornstein–Uhlenbeck process.
* `ProbabilityTheory.IsGaussianProcess.option_elim`: a Gaussian process with an independent
  Gaussian variable adjoined is a Gaussian process.
* `ProbabilityTheory.integral_itoIntegralL2_exp_mul`: the covariance
  `E[I_s I_t] = (e^{2θ (s ∧ t)} - 1) / (2θ)` of the Wiener integrals `I_t = ∫_0^t e^{θu} dB_u`.

## Implementation notes

The statements need no filtration: the proof replaces `B` by a modification `B'` with measurable
coordinates (a pre-Brownian motion), works with the natural filtration of `B'`, whose increments
are independent of the past (`IsPreBrownianReal.indep_natural`), and uses the Itô integral of
`MathlibExt.Probability.ItoIntegral` against `B'`. The Itô–Riemann sums
`∑_k e^{θ t k / n} (B (t (k + 1) / n) - B (t k / n))` are finite linear combinations of values of
`B`, hence jointly Gaussian with the independent start; they converge in `L²` to the Wiener
integral, and almost surely (along a subsequence and on continuous paths) to the pathwise
solution (`IsBrownianReal.ae_tendsto_ou_itoIntegral_riemann`). Gaussianity passes to the limit by
`IsGaussianProcess.of_tendsto_eLpNorm`. The covariance of the Wiener integrals follows from the
martingale property and the Itô isometry.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer,
  1991, Section 5.6 (linear equations; the Ornstein–Uhlenbeck process).
* B. Øksendal, *Stochastic Differential Equations*, 6th ed., Springer, 2003, Chapter 5 (the
  Langevin equation and its solution).
* G. E. Uhlenbeck and L. S. Ornstein, *On the theory of the Brownian motion*, Phys. Rev. 36
  (1930), 823–841.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped NNReal ENNReal ProbabilityTheory

namespace ProbabilityTheory


/-- A process of the form `c₀ X i₀ + ∑_{k < n} c k (X (τ (k + 1)) - X (τ k))`, built from finitely
many values of a real Gaussian process, is a Gaussian process. -/
private theorem IsGaussianProcess.of_sum_increments {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {T S : Type*} {X : T → Ω → ℝ} (hX : IsGaussianProcess X P)
    {Y : S → Ω → ℝ} (i₀ : S → T) (c₀ : S → ℝ) (n : S → ℕ) (τ : S → ℕ → T) (c : S → ℕ → ℝ)
    (hY : ∀ s ω, Y s ω = c₀ s * X (i₀ s) ω +
      ∑ k ∈ Finset.range (n s), c s k * (X (τ s (k + 1)) ω - X (τ s k) ω)) :
    IsGaussianProcess Y P := by
  classical
  refine hX.of_isGaussianProcess fun s ↦ ?_
  let I : Finset T := insert (i₀ s) ((Finset.range (n s + 1)).image (τ s))
  have h0 : i₀ s ∈ I := Finset.mem_insert_self _ _
  have hτ : ∀ k, k < n s + 1 → τ s k ∈ I := fun k hk ↦
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hk))
  let L : (I → ℝ) →ₗ[ℝ] ℝ :=
    { toFun x := c₀ s * x ⟨i₀ s, h0⟩ + ∑ k ∈ (Finset.range (n s)).attach,
        c s k * (x ⟨τ s (k + 1), hτ _ (by have := Finset.mem_range.mp k.2; omega)⟩ -
          x ⟨τ s k, hτ _ (by have := Finset.mem_range.mp k.2; omega)⟩)
      map_add' x y := by
        simp only [Pi.add_apply]
        rw [mul_add, add_add_add_comm, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        ring
      map_smul' a x := by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [mul_add, Finset.mul_sum]
        congr 1
        · ring
        · refine Finset.sum_congr rfl fun k _ ↦ ?_
          ring }
  refine ⟨I, LinearMap.toContinuousLinearMap L, fun ω ↦ ?_⟩
  simp only [LinearMap.coe_toContinuousLinearMap', L, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.restrict_def, hY]
  congr 1
  exact (Finset.sum_attach (Finset.range (n s))
    (fun k ↦ c s k * (X (τ s (k + 1)) ω - X (τ s k) ω))).symm

/-- Elementary Itô integrals against two modifications of the same process agree almost
surely. -/
theorem ElementaryIntegrand.itoIntegral_ae_eq_of_ae_eq {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} (H : ElementaryIntegrand F) {B B' : ℝ≥0 → Ω → ℝ}
    (h : ∀ t, B t =ᵐ[P] B' t) (t : ℝ≥0) : H.itoIntegral B t =ᵐ[P] H.itoIntegral B' t := by
  have h' : ∀ᵐ ω ∂P, ∀ i : Fin (H.n + 1), B (min (H.time i) t) ω = B' (min (H.time i) t) ω :=
    ae_all_iff.2 fun i ↦ h _
  filter_upwards [h'] with ω hω
  simp only [ElementaryIntegrand.itoIntegral, hω]

/-- A real random variable independent of a pre-Brownian path is orthogonal to every
Itô–Riemann sum of a deterministic integrand: `E[Y ∑_k g(t_k) (B t_{k+1} - B t_k)] = 0`. -/
private theorem integral_mul_itoIntegral_riemann_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (F : Filtration ℝ≥0 mΩ)
    {Y : Ω → ℝ} (hY : Integrable Y P) (hYB : IndepFun Y (fun ω t ↦ B t ω) P) (g : ℝ → ℝ)
    (t : ℝ≥0) (n : ℕ) :
    ∫ ω, Y ω * (ElementaryIntegrand.riemann F g t n).itoIntegral B t ω ∂P = 0 := by
  have hpt : ∀ a b : ℝ≥0, ∫ ω, Y ω * (B a ω - B b ω) ∂P = 0 ∧
      Integrable (fun ω ↦ Y ω * (B a ω - B b ω)) P := by
    intro a b
    have hI : IndepFun Y (fun ω ↦ B a ω - B b ω) P :=
      hYB.comp measurable_id (ψ := fun x : ℝ≥0 → ℝ ↦ x a - x b)
        ((measurable_pi_apply a).sub (measurable_pi_apply b))
    have hint : Integrable (fun ω ↦ B a ω - B b ω) P :=
      (hB.integrable_eval a).sub (hB.integrable_eval b)
    refine ⟨?_, IndepFun.integrable_mul hI hY hint⟩
    rw [show (fun ω ↦ Y ω * (B a ω - B b ω)) = Y * fun ω ↦ B a ω - B b ω from rfl,
      IndepFun.integral_mul_eq_mul_integral hI hY.aestronglyMeasurable
        hint.aestronglyMeasurable,
      integral_sub (hB.integrable_eval a) (hB.integrable_eval b), hB.integral_eval,
      hB.integral_eval]
    ring
  simp_rw [ElementaryIntegrand.itoIntegral_riemann, Finset.mul_sum]
  rw [integral_finsetSum _ fun k _ ↦ ?_]
  · refine Finset.sum_eq_zero fun k _ ↦ ?_
    simp_rw [mul_left_comm (Y _)]
    rw [integral_const_mul, (hpt _ _).1, mul_zero]
  · simp_rw [mul_left_comm (Y _)]
    exact (hpt _ _).2.const_mul _

/-- **Adjoining an independent Gaussian variable.** If `X₀` is a real Gaussian random variable
independent of the real Gaussian process `B`, the process indexed by `Option T` that is `X₀` at
`none` and `B t` at `some t` is a Gaussian process. -/
theorem IsGaussianProcess.option_elim {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {T : Type*} {X₀ : Ω → ℝ} {B : T → Ω → ℝ} (hX₀ : HasGaussianLaw X₀ P)
    (hB : IsGaussianProcess B P) (hind : IndepFun X₀ (fun ω t ↦ B t ω) P) :
    IsGaussianProcess (fun (o : Option T) ω ↦ o.elim (X₀ ω) (fun t ↦ B t ω)) P := by
  classical
  refine ⟨fun I ↦ ?_⟩
  let J : Finset T := I.eraseNone
  have hres : Measurable fun x : T → ℝ ↦ J.restrict x :=
    Measurable.of_eval fun i ↦ measurable_pi_apply _
  have hpair : HasGaussianLaw (fun ω ↦ (X₀ ω, J.restrict (B · ω))) P :=
    IndepFun.hasGaussianLaw hX₀ (hB.hasGaussianLaw J) (hind.comp measurable_id hres)
  let L : (ℝ × (J → ℝ)) →ₗ[ℝ] (I → ℝ) :=
    { toFun p := fun i ↦ match i with
        | ⟨none, _⟩ => p.1
        | ⟨some t, h⟩ => p.2 ⟨t, Finset.mem_eraseNone.2 h⟩
      map_add' p q := by
        funext i
        rcases i with ⟨_ | t, h⟩ <;> rfl
      map_smul' c p := by
        funext i
        rcases i with ⟨_ | t, h⟩ <;> rfl }
  have heq : (fun ω ↦ I.restrict (fun o ↦ o.elim (X₀ ω) (fun t ↦ B t ω))) =
      (LinearMap.toContinuousLinearMap L) ∘ (fun ω ↦ (X₀ ω, J.restrict (B · ω))) := by
    funext ω
    funext i
    rcases i with ⟨_ | t, h⟩ <;> rfl
  rw [heq]
  exact hpair.map _

/-- **Covariance of the Wiener integrals** `I_t = ∫_0^t e^{θu} dB_u`: for a pre-Brownian motion
`B` adapted to `F` with increments independent of the past and `θ ≠ 0`,
`E[I_s I_t] = (e^{2θ (s ∧ t)} - 1) / (2θ)`, by the martingale property and the Itô isometry. -/
theorem integral_itoIntegralL2_exp_mul {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) {θ : ℝ} (hθ : θ ≠ 0) (s t : ℝ≥0) :
    ∫ ω, (itoIntegralL2 P F B (fun u _ ↦ exp (θ * u)) s : Ω → ℝ) ω *
      (itoIntegralL2 P F B (fun u _ ↦ exp (θ * u)) t : Ω → ℝ) ω ∂P =
      (exp (2 * θ * min (s : ℝ) t) - 1) / (2 * θ) := by
  have hprob := hB.isGaussianProcess.isProbabilityMeasure
  set H : ℝ≥0 → Ω → ℝ := fun u _ ↦ exp (θ * u)
  have hg : Continuous (fun u : ℝ ↦ exp (θ * u)) := by fun_prop
  have happ : ∀ t, IsItoApproximable P F H t := fun t ↦
    ⟨(hg.measurable.comp (NNReal.continuous_coe.measurable.comp
      measurable_real_toNNReal)).comp measurable_fst, _,
      tendsto_integrandDist_riemann (F := F) (P := P) hg t⟩
  have hmart := martingale_itoIntegral hB hBF hInd happ
  set J := itoIntegral P F B H
  have hJ : ∀ t, J t =ᵐ[P] (itoIntegralL2 P F B H t : Ω → ℝ) := itoIntegral_ae_eq P F B H
  have hJm : ∀ t, MemLp (J t) 2 P := fun t ↦ (Lp.memLp _).ae_eq (hJ t).symm
  have hsq : ∀ t : ℝ≥0, ∫ ω, J t ω * J t ω ∂P = (exp (2 * θ * t) - 1) / (2 * θ) := by
    intro t
    have h1 : ∫ ω, J t ω * J t ω ∂P = (∫⁻ ω, ‖J t ω‖ₑ ^ 2 ∂P).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω ↦ mul_self_nonneg _)
        ((hJm t).integrable_mul (hJm t)).aestronglyMeasurable]
      congr 1
      refine lintegral_congr fun ω ↦ ?_
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, sq]
    have h2 : ∀ ω : Ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) =
        ∫⁻ u in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (exp (2 * θ * u)) := fun ω ↦ by
      refine setLIntegral_congr_fun measurableSet_Ioc fun u hu ↦ ?_
      simp only [H, Real.coe_toNNReal _ hu.1.le, Real.enorm_eq_ofReal_abs,
        abs_of_pos (exp_pos _), ← ENNReal.ofReal_pow (exp_pos _).le, sq, ← Real.exp_add]
      ring_nf
    have hcont : Continuous fun u : ℝ ↦ exp (2 * θ * u) := by fun_prop
    have hint : IntegrableOn (fun u : ℝ ↦ exp (2 * θ * u)) (Set.Ioc 0 t) volume :=
      hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    rw [h1, lintegral_itoIntegral_sq hB hBF hInd (happ t)]
    simp_rw [h2]
    rw [lintegral_const, measure_univ, mul_one,
      ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun u ↦ (exp_pos _).le),
      ENNReal.toReal_ofReal (integral_nonneg fun u ↦ (exp_pos _).le),
      ← intervalIntegral.integral_of_le (μ := volume) (f := fun u ↦ exp (2 * θ * u))
        (show (0 : ℝ) ≤ t from t.2),
      intervalIntegral.integral_comp_mul_left (fun x ↦ exp x) (mul_ne_zero two_ne_zero hθ),
      integral_exp, mul_zero, Real.exp_zero, smul_eq_mul]
    field_simp
  have hcross : ∀ s t, s ≤ t → ∫ ω, J s ω * J t ω ∂P = ∫ ω, J s ω * J s ω ∂P := by
    intro s t hst
    have h1 := condExp_mul_of_stronglyMeasurable_left (m := F s) (μ := P) (hmart.1 s)
      ((hJm s).integrable_mul (hJm t)) ((hJm t).integrable one_le_two)
    rw [show (fun ω ↦ J s ω * J t ω) = J s * J t from rfl, ← integral_condExp (F.le s),
      integral_congr_ae h1]
    refine integral_congr_ae ?_
    filter_upwards [hmart.condExp_ae_eq hst] with ω hω
    simp [hω]
  have hst' : ∫ ω, (itoIntegralL2 P F B H s : Ω → ℝ) ω * (itoIntegralL2 P F B H t : Ω → ℝ) ω ∂P
      = ∫ ω, J s ω * J t ω ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hJ s, hJ t] with ω h1 h2
    rw [h1, h2]
  rw [hst']
  rcases le_total s t with hst | hts
  · rw [hcross s t hst, hsq, min_eq_left (by exact_mod_cast hst)]
  · simp_rw [mul_comm (J s _)]
    rw [hcross t s hts, hsq, min_eq_right (by exact_mod_cast hts)]

/-- **The pathwise Langevin solution driven by Brownian motion is Gaussian.** For a Brownian
motion `B`, `θ ≠ 0`, any real `σ`, and a start `X₀ ~ N(0, v)` independent of `B`, the process
`X t = ouPathSolution θ σ X₀ B t` (`t ≥ 0`) is a Gaussian process with `E[X t] = 0` and
`cov[X s, X t] = e^{-θ(s+t)} (v + σ² (e^{2θ (s ∧ t)} - 1) / (2θ))` (Karatzas–Shreve 1991,
Section 5.6). -/
theorem IsBrownianReal.isGaussianProcess_ouPathSolution {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {θ : ℝ} (hθ : θ ≠ 0) (σ : ℝ)
    {X₀ : Ω → ℝ} {v : ℝ≥0} (hX₀ : HasLaw X₀ (gaussianReal 0 v) P)
    (hind : IndepFun X₀ (fun ω t ↦ B t ω) P) :
    IsGaussianProcess
        (fun (t : ℝ≥0) ω ↦ ouPathSolution θ σ (X₀ ω) (fun u ↦ B (Real.toNNReal u) ω) t) P ∧
      (∀ t : ℝ≥0, P[fun ω ↦ ouPathSolution θ σ (X₀ ω) (fun u ↦ B (Real.toNNReal u) ω) t] = 0) ∧
      ∀ s t : ℝ≥0,
        cov[fun ω ↦ ouPathSolution θ σ (X₀ ω) (fun u ↦ B (Real.toNNReal u) ω) s,
          fun ω ↦ ouPathSolution θ σ (X₀ ω) (fun u ↦ B (Real.toNNReal u) ω) t; P] =
          exp (-θ * (s + t)) * (v + σ ^ 2 * ((exp (2 * θ * min (s : ℝ) t) - 1) / (2 * θ))) := by
  have hpre := hB.toIsPreBrownianReal
  have hprob := hpre.isGaussianProcess.isProbabilityMeasure
  -- a measurable modification and its natural filtration
  set B' : ℝ≥0 → Ω → ℝ := fun t ↦ (hpre.aemeasurable t).mk (B t) with hB'def
  have hB'm : ∀ t, Measurable (B' t) := fun t ↦ (hpre.aemeasurable t).measurable_mk
  have hBB' : ∀ t, B t =ᵐ[P] B' t := fun t ↦ (hpre.aemeasurable t).ae_eq_mk
  have hpre' : IsPreBrownianReal B' P := hpre.congr hBB'
  set F := Filtration.natural B' (fun t ↦ (hB'm t).stronglyMeasurable)
  have hBF : Adapted F B' := adapted_natural_of_measurable hB'm
  have hInd := hpre'.indep_natural hB'm
  set g : ℝ → ℝ := fun u ↦ exp (θ * u) with hgdef
  have hg : Continuous g := by fun_prop
  set X : ℝ≥0 → Ω → ℝ := fun t ω ↦ ouPathSolution θ σ (X₀ ω) (fun u ↦ B (Real.toNNReal u) ω) t
  set I : ℝ≥0 → Ω → ℝ := fun t ↦ (itoIntegralL2 P F B' (fun u _ ↦ g u) t : Ω → ℝ)
  set S : ℕ → ℝ≥0 → Ω → ℝ := fun n t ↦ (ElementaryIntegrand.riemann F g t n).itoIntegral B t
  have hImem : ∀ t, MemLp (I t) 2 P := fun t ↦ Lp.memLp _
  have hSmem : ∀ n t, MemLp (S n t) 2 P := fun n t ↦
    ((ElementaryIntegrand.riemann F g t n).memLp_itoIntegral hpre' t).ae_eq
      ((ElementaryIntegrand.riemann F g t n).itoIntegral_ae_eq_of_ae_eq hBB' t).symm
  -- `L²` convergence of the Itô–Riemann sums to the Wiener integral
  have hL2 : ∀ t, Tendsto (fun n ↦ eLpNorm (S n t - I t) 2 P) atTop (𝓝 0) := by
    intro t
    have hHm : Measurable fun p : ℝ × Ω ↦ (fun u _ ↦ g u : ℝ≥0 → Ω → ℝ) p.1.toNNReal p.2 :=
      (hg.measurable.comp (NNReal.continuous_coe.measurable.comp
        measurable_real_toNNReal)).comp measurable_fst
    have hlim := tendsto_toL2_itoIntegral hpre' hBF hInd hHm
      (tendsto_integrandDist_riemann (F := F) (P := P) hg t)
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hlim
    refine hlim.congr' (Eventually.of_forall fun n ↦ eLpNorm_congr_ae ?_)
    have hm := (ElementaryIntegrand.riemann F g t n).memLp_itoIntegral hpre' t
    simp only [toL2, hm, ↓reduceDIte]
    filter_upwards [hm.coeFn_toLp,
      (ElementaryIntegrand.riemann F g t n).itoIntegral_ae_eq_of_ae_eq hBB' t] with ω h1 h2
    simp only [Pi.sub_apply, h1, h2, S, I]
  -- almost sure identification of the pathwise solution
  have hXI : ∀ t, X t =ᵐ[P] fun ω ↦ exp (-θ * t) * X₀ ω + σ * exp (-θ * t) * I t ω := by
    intro t
    obtain ⟨ns, hns, hae⟩ :=
      (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (hL2 t)).exists_seq_tendsto_ae
    filter_upwards [hae, hB.ae_tendsto_ou_itoIntegral_riemann F θ σ X₀] with ω h1 h2
    exact tendsto_nhds_unique ((h2 t).comp hns.tendsto_atTop)
      ((h1.const_mul (σ * exp (-θ * t))).const_add (exp (-θ * t) * X₀ ω))
  have hX₀g : HasGaussianLaw X₀ P := hX₀.hasGaussianLaw
  have hX₀m : MemLp X₀ 2 P := hX₀g.memLp_two
  have hXmem : ∀ t, MemLp (X t) 2 P := fun t ↦
    ((hX₀m.const_mul _).add ((hImem t).const_mul _)).ae_eq (hXI t).symm
  -- Gaussianity: `L²` limit of Gaussian processes
  have hZ := IsGaussianProcess.option_elim hX₀g hpre.isGaussianProcess hind
  have hXn : ∀ n, IsGaussianProcess
      (fun (t : ℝ≥0) ω ↦ exp (-θ * t) * X₀ ω + σ * exp (-θ * t) * S n t ω) P := fun n ↦
    hZ.of_sum_increments (fun _ ↦ none) (fun t : ℝ≥0 ↦ exp (-θ * t)) (fun _ ↦ n)
      (fun (t : ℝ≥0) k ↦ some (Real.toNNReal (t * k / n)))
      (fun (t : ℝ≥0) k ↦ σ * exp (-θ * t) * g (t * k / n)) fun t ω ↦ by
        simp only [S, ElementaryIntegrand.itoIntegral_riemann, Option.elim, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        push_cast
        ring
  have hGP : IsGaussianProcess X P := by
    refine IsGaussianProcess.of_tendsto_eLpNorm hXn (fun t ↦ (hXmem t).aestronglyMeasurable)
      fun t ↦ ?_
    have heq : ∀ n, eLpNorm ((fun ω ↦ exp (-θ * t) * X₀ ω + σ * exp (-θ * t) * S n t ω) - X t)
        2 P = ‖σ * exp (-θ * t)‖ₑ * eLpNorm (S n t - I t) 2 P := fun n ↦ by
      rw [← eLpNorm_const_smul]
      refine eLpNorm_congr_ae ?_
      filter_upwards [hXI t] with ω hω
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hω]
      ring
    simp_rw [heq]
    simpa using ENNReal.Tendsto.const_mul (a := ‖σ * exp (-θ * t)‖ₑ) (hL2 t)
      (Or.inr enorm_ne_top)
  -- orthogonality of independent variables to the Wiener integral
  have horth : ∀ (Y : Ω → ℝ), MemLp Y 2 P → IndepFun Y (fun ω t ↦ B t ω) P →
      ∀ t, ∫ ω, Y ω * I t ω ∂P = 0 := by
    intro Y hY hYB t
    refine tendsto_nhds_unique (tendsto_integral_mul_of_tendsto_eLpNorm (fun _ ↦ hY)
      (fun n ↦ hSmem n t) hY (hImem t) (by simp) (hL2 t)) ?_
    simp only [S,
      integral_mul_itoIntegral_riemann_eq_zero hpre F (hY.integrable one_le_two) hYB]
    exact tendsto_const_nhds
  have hI0 : ∀ t, ∫ ω, I t ω ∂P = 0 := fun t ↦ by
    simpa using horth (fun _ ↦ 1) (memLp_const 1) (indepFun_const_left _ _) t
  have hX₀0 : ∫ ω, X₀ ω ∂P = 0 := by
    rw [hX₀.integral_eq, integral_id_gaussianReal]
  have hX₀2 : ∫ ω, X₀ ω * X₀ ω ∂P = v := by
    have hv := hX₀.variance_eq
    rw [variance_id_gaussianReal, variance_of_integral_eq_zero hX₀.aemeasurable hX₀0] at hv
    simpa [sq] using hv
  have hmean : ∀ t, P[X t] = 0 := fun t ↦ by
    rw [integral_congr_ae (hXI t), integral_add ((hX₀m.integrable one_le_two).const_mul _)
      (((hImem t).integrable one_le_two).const_mul _), integral_const_mul, integral_const_mul,
      hX₀0, hI0]
    ring
  refine ⟨hGP, hmean, fun s t ↦ ?_⟩
  rw [covariance_eq_sub (hXmem s) (hXmem t), hmean, hmean, mul_zero, sub_zero]
  have hprod : X s * X t =ᵐ[P] fun ω ↦
      exp (-θ * s) * exp (-θ * t) * (X₀ ω * X₀ ω) +
        exp (-θ * s) * (σ * exp (-θ * t)) * (X₀ ω * I t ω) +
        σ * exp (-θ * s) * exp (-θ * t) * (X₀ ω * I s ω) +
        σ * exp (-θ * s) * (σ * exp (-θ * t)) * (I s ω * I t ω) := by
    filter_upwards [hXI s, hXI t] with ω h1 h2
    simp only [Pi.mul_apply, h1, h2]
    ring
  have hi : ∀ {f h : Ω → ℝ}, MemLp f 2 P → MemLp h 2 P → Integrable (fun ω ↦ f ω * h ω) P :=
    fun hf hh ↦ hf.integrable_mul hh
  have i1 := (hi hX₀m hX₀m).const_mul (exp (-θ * s) * exp (-θ * t))
  have i2 := (hi hX₀m (hImem t)).const_mul (exp (-θ * s) * (σ * exp (-θ * t)))
  have i3 := (hi hX₀m (hImem s)).const_mul (σ * exp (-θ * s) * exp (-θ * t))
  have i4 := (hi (hImem s) (hImem t)).const_mul (σ * exp (-θ * s) * (σ * exp (-θ * t)))
  rw [integral_congr_ae hprod, integral_add, integral_add, integral_add, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, hX₀2, horth X₀ hX₀m hind,
    horth X₀ hX₀m hind, integral_itoIntegralL2_exp_mul hpre' hBF hInd hθ,
    show -θ * ((s : ℝ) + t) = -θ * s + -θ * t by ring, Real.exp_add]
  · ring
  all_goals first
    | exact i1 | exact i2 | exact i3 | exact i4 | exact i1.add i2 | exact (i1.add i2).add i3

private lemma exp_mul_exp_min (θ s t : ℝ) :
    exp (-θ * (s + t)) * exp (2 * θ * min s t) = exp (-θ * |t - s|) := by
  rw [← Real.exp_add]
  congr 1
  rcases le_total s t with hst | hts
  · rw [min_eq_left hst, abs_of_nonneg (sub_nonneg.mpr hst)]
    ring
  · rw [min_eq_right hts, abs_of_nonpos (sub_nonpos.mpr hts)]
    ring

/-- **The pathwise Langevin solution is an OU process.** Driven by a Brownian motion and started
at `0`, `ouPathSolution` is an Ornstein–Uhlenbeck process started at `0` (Karatzas–Shreve 1991,
Section 5.6). No filtration and no measurability of the coordinates of `B` is assumed. -/
theorem IsBrownianReal.isOrnsteinUhlenbeckFromZero_ouPathSolution {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) :
    IsOrnsteinUhlenbeckFromZero θ σ
      (fun t ω ↦ ouPathSolution θ σ 0 (fun u ↦ B (Real.toNNReal u) ω) t) P := by
  have := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hX₀ : HasLaw (fun _ : Ω ↦ (0 : ℝ)) (gaussianReal 0 0) P := by
    rw [gaussianReal_zero_var]
    exact ⟨aemeasurable_const, by simp [Measure.map_const]⟩
  obtain ⟨hGP, hmean, hcov⟩ := hB.isGaussianProcess_ouPathSolution hθ.ne' σ hX₀
    (indepFun_const_left _ _)
  refine ⟨hθ, hGP, hmean, fun s t ↦ ?_⟩
  rw [hcov, ouCovariance]
  have h2 : (2 : ℝ) * θ ≠ 0 := by positivity
  rw [← exp_mul_exp_min θ s t, show -θ * ((t : ℝ) + s) = -θ * (s + t) by ring]
  field_simp
  simp

/-- **Stationary start.** Driven by a Brownian motion `B` and started from `X₀ ~ N(0, σ²/(2θ))`
independent of `B`, `ouPathSolution` is a stationary Ornstein–Uhlenbeck process
(Karatzas–Shreve 1991, Section 5.6). -/
theorem IsBrownianReal.isStationaryOrnsteinUhlenbeck_ouPathSolution {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) {X₀ : Ω → ℝ}
    (hX₀ : HasLaw X₀ (gaussianReal 0 (σ ^ 2 / (2 * θ)).toNNReal) P)
    (hind : IndepFun X₀ (fun ω t ↦ B t ω) P) :
    IsStationaryOrnsteinUhlenbeck θ σ
      (fun t ω ↦ ouPathSolution θ σ (X₀ ω) (fun u ↦ B (Real.toNNReal u) ω) t) P := by
  obtain ⟨hGP, hmean, hcov⟩ := hB.isGaussianProcess_ouPathSolution hθ.ne' σ hX₀ hind
  refine ⟨hθ, hGP, hmean, fun s t ↦ ?_⟩
  rw [hcov, ouStationaryCovariance, Real.coe_toNNReal _ (by positivity),
    ← exp_mul_exp_min θ s t]
  have h2 : (2 : ℝ) * θ ≠ 0 := by positivity
  field_simp
  ring

end ProbabilityTheory
