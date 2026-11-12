/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Semilinear reaction–diffusion flows: the C₀-semigroup interface

## Frozen setting

The target system is the semilinear reaction–diffusion system
`∂ₜ u = D Δ u + f(u)` for `u = (u₁, …, uₘ) : [0, T] × Ω̄ → ℝᵐ`, with

* **domain**: `Ω ⊆ ℝⁿ` a bounded open set with smooth boundary `∂Ω`;
* **boundary condition**: homogeneous Neumann (zero flux), `∂_ν uᵢ = 0` on `∂Ω` for each `i`;
* **diffusion**: `D = diag(d₁, …, dₘ)` with every `dᵢ > 0`, so `A = diag(d₁ Δ_N, …, dₘ Δ_N)`;
* **function space**: `X = C(Ω̄; ℝᵐ)` with the sup norm;
* **reaction**: the Nemytskii map `F(u)(x) = f(u(x))` for a locally Lipschitz `f : ℝᵐ → ℝᵐ`.
  On `C(Ω̄)` it is Lipschitz on bounded sets, which is the hypothesis used below.

The Neumann Laplacian generates an analytic semigroup on `C(Ω̄)`. Its domain is dense there,
so the semigroup is strongly continuous (Stewart 1974/1980; Lunardi, *Analytic Semigroups and
Optimal Regularity in Parabolic Problems*, Ch. 3). Because `F` maps `X` to `X` and is Lipschitz
on bounded sets, local well-posedness only needs the C₀ structure (Pazy, *Semigroups of
Linear Operators and Applications to PDE*, Thm. 6.1.4). Analyticity matters for smoothing and
for nonlinearities defined on fractional power spaces `X^α`; it is not needed for this flow.

## Audit

Mathlib (v4.35.0) has no C₀, analytic, or sectorial semigroups and no Laplacian on a bounded
domain. Atlas only has the bounded-operator variation-of-constants formula
(`MathlibExt.Analysis.ODE.Duhamel`) and the Fourier-mode linear analysis in
`MathlibExt.Biology.Dynamics.TuringPatterns`. A bounded generator is the finite-dimensional/ODE
case (`isC0Semigroup_exp`). It does not cover the Neumann Laplacian, which is unbounded, so
the interface below asks only for strong continuity.

## Main results

* `IsC0Semigroup`: strongly continuous semigroups of bounded operators, indexed by `ℝ≥0`.
* `IsMildSolution`: continuous solutions of the Duhamel identity
  `u t = S t x₀ + ∫₀ᵗ S (t - s) F(u s) ds` on `[0, T]`.
* `exists_isMildSolution`: local existence, with an existence time that is uniform for
  initial values in a ball (Banach fixed-point theorem on `C([0, T], X)`).
* `IsMildSolution.eqOn`: uniqueness. `exists_norm_sub_le_of_norm_le`: Lipschitz dependence
  on initial data, with the constant depending only on a norm bound `R` and the time `T`
  (integral Grönwall). With the a priori bound from `exists_isMildSolution`, the solution map
  is Lipschitz on balls.
* `IsMildSolution.restart`: the semiflow (restart) identity; `u (s + ·)` is the mild solution
  from `u s`.
* `nemytskii`, `lipschitzOnWith_nemytskii`: the reaction term `u ↦ f ∘ u` on `C(K, E)` is
  Lipschitz on bounded sets when `f` is.
* `isC0Semigroup_exp`: bounded generators give C₀ semigroups.
* `exists_memLp_two_not_memLp_two_sq`, the incompatible-spaces boundary case: `u ↦ u²` does
  not map `L²(0, 1)` to itself, so `(L², u ↦ u²)` fails the typing `F : X → X` of the interface.
  The Dirichlet Laplacian on `C(Ω̄)` is a second incompatible pair (non-dense domain, so no
  C₀ semigroup); the C₀ case there lives on `C₀(Ω)`.

## Not formalized here

No analytic or sectorial semigroup structure is defined here. Constructing the
Neumann-Laplacian semigroup on `C(Ω̄)` and proving it is analytic are outside the scope of this
file, and so are the maximal existence interval and the blow-up alternative. A concrete
reaction–diffusion system enters through the hypothesis `hS : IsC0Semigroup S`; its reaction
term satisfies `hF` by `lipschitzOnWith_nemytskii`.

Note for linearized instability: for a general C₀ semigroup the spectrum of the generator does
not control `‖S t‖` (the spectral mapping theorem can fail). Spectral instability hypotheses
should therefore be stated on `S` itself, e.g. `S t φ = exp (λ t) • φ` for an eigenvector `φ`
or spectral radius of `S t₀` greater than `1`, or eventual norm continuity should be assumed
explicitly.
-/

open MeasureTheory Set
open scoped NNReal

@[expose] public section

namespace MathlibExt.Analysis.PDE.SemilinearFlow

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A **strongly continuous (C₀) semigroup** of bounded operators on a real normed space `X`,
indexed by nonnegative time: `S 0 = 1`, `S (s + t) = S s ∘ S t`, every orbit `t ↦ S t x` is
continuous, and `‖S t‖` is bounded on every compact time interval `[0, T]`.

Only strong (orbitwise) continuity is required, never norm continuity of `t ↦ S t`, so the
semigroups generated by unbounded operators such as the Neumann Laplacian are admissible.
The local bound is part of the classical definition up to the uniform boundedness principle. -/
structure IsC0Semigroup (S : ℝ≥0 → X →L[ℝ] X) : Prop where
  /-- `S 0` is the identity. -/
  map_zero : S 0 = 1
  /-- The semigroup law `S (s + t) = S s ∘ S t`. -/
  map_add : ∀ s t, S (s + t) = (S s).comp (S t)
  /-- Strong continuity: every orbit `t ↦ S t x` is continuous. -/
  continuous_apply : ∀ x, Continuous fun t => S t x
  /-- Local boundedness: `‖S t‖ ≤ M` for `t ∈ [0, T]`. -/
  locally_bounded : ∀ T : ℝ≥0, ∃ M : ℝ, ∀ t ≤ T, ‖S t‖ ≤ M

/-- The **Duhamel term** `t ↦ ∫₀ᵗ S (t - s) g(s) ds` of a forcing `g : ℝ → X` in a Banach
space. Negative time differences are truncated to `0`; on `s ∈ [0, t]` they never occur. -/
noncomputable def duhamel [CompleteSpace X]
    (S : ℝ≥0 → X →L[ℝ] X) (g : ℝ → X) (t : ℝ) : X :=
  ∫ s in (0 : ℝ)..t, S (t - s).toNNReal (g s)

variable [CompleteSpace X]

/-- `u` is a **mild solution** on `[0, T]` of the semilinear equation `u' = A u + F u`,
`u 0 = x₀`, where `A` generates the semigroup `S`: `u` is continuous on `[0, T]`, each
Duhamel integrand is integrable on `[0, t]`, and the variation-of-constants identity holds. -/
def IsMildSolution (S : ℝ≥0 → X →L[ℝ] X) (F : X → X) (x₀ : X) (T : ℝ) (u : ℝ → X) : Prop :=
  ContinuousOn u (Icc 0 T) ∧
    (∀ t ∈ Icc 0 T,
      IntervalIntegrable (fun s => S (t - s).toNNReal (F (u s))) volume 0 t) ∧
    ∀ t ∈ Icc 0 T, u t = S t.toNNReal x₀ + duhamel S (fun s => F (u s)) t

namespace IsC0Semigroup

variable {S : ℝ≥0 → X →L[ℝ] X}

omit [CompleteSpace X] in
/-- A C₀ semigroup is jointly continuous in time and state. -/
theorem continuous_uncurry (hS : IsC0Semigroup S) :
    Continuous fun p : ℝ≥0 × X => S p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, x₀⟩
  obtain ⟨M, hM⟩ := hS.locally_bounded (t₀ + 1)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 bot_le)
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have h1 : ∀ᶠ p : ℝ≥0 × X in nhds (t₀, x₀), p.1 < t₀ + 1 :=
    (continuous_fst.tendsto (t₀, x₀)).eventually (gt_mem_nhds (lt_add_one t₀))
  have h2 : ∀ᶠ p : ℝ≥0 × X in nhds (t₀, x₀), dist (S p.1 x₀) (S t₀ x₀) < ε / 2 :=
    ((hS.continuous_apply x₀).tendsto t₀).comp (continuous_fst.tendsto (t₀, x₀))
      |>.eventually (Metric.ball_mem_nhds _ (half_pos hε))
  have h3 : ∀ᶠ p : ℝ≥0 × X in nhds (t₀, x₀), (M + 1) * dist p.2 x₀ < ε / 2 := by
    have : Continuous fun p : ℝ≥0 × X => (M + 1) * dist p.2 x₀ := by fun_prop
    have h0 : (M + 1) * dist (t₀, x₀).2 x₀ < ε / 2 := by simpa using half_pos hε
    exact this.continuousAt.eventually (gt_mem_nhds h0) |>.mono fun p hp => hp
  filter_upwards [h1, h2, h3] with p hp1 hp2 hp3
  have hdist : dist (S p.1 p.2) (S p.1 x₀) ≤ M * dist p.2 x₀ := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact ((S p.1).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hM _ hp1.le) (norm_nonneg _))
  calc dist (S p.1 p.2) (S t₀ x₀)
      ≤ dist (S p.1 p.2) (S p.1 x₀) + dist (S p.1 x₀) (S t₀ x₀) := dist_triangle _ _ _
    _ < ε := by nlinarith [dist_nonneg (x := p.2) (y := x₀)]

/-- The Duhamel term of a continuous forcing is continuous in time. -/
theorem continuous_duhamel (hS : IsC0Semigroup S) {g : ℝ → X} (hg : Continuous g) :
    Continuous (duhamel S g) := by
  unfold duhamel
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous _ continuous_id
  exact hS.continuous_uncurry.comp
    ((continuous_real_toNNReal.comp (continuous_fst.sub continuous_snd)).prodMk
      (hg.comp continuous_snd))

omit [CompleteSpace X] in
/-- The integrand of the Duhamel term of a continuous forcing is interval integrable. -/
theorem intervalIntegrable_duhamel_integrand (hS : IsC0Semigroup S) {g : ℝ → X}
    (hg : Continuous g) (t a b : ℝ) :
    IntervalIntegrable (fun s => S (t - s).toNNReal (g s)) volume a b :=
  (hS.continuous_uncurry.comp
    ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).prodMk hg)
    ).intervalIntegrable a b

/-- Difference estimate for Duhamel terms: if `‖g s - h s‖ ≤ K` on `[0, t]` and
`‖S τ‖ ≤ M` for `τ ≤ t`, then the Duhamel terms differ by at most `M K t`. -/
theorem norm_duhamel_sub_le (hS : IsC0Semigroup S) {g h : ℝ → X} (hg : Continuous g)
    (hh : Continuous h) {t M K : ℝ} (ht : 0 ≤ t) (hM : ∀ τ : ℝ≥0, (τ : ℝ) ≤ t → ‖S τ‖ ≤ M)
    (hM0 : 0 ≤ M) (hK : ∀ s ∈ Icc 0 t, ‖g s - h s‖ ≤ K) :
    ‖duhamel S g t - duhamel S h t‖ ≤ M * K * t := by
  unfold duhamel
  rw [← intervalIntegral.integral_sub (hS.intervalIntegrable_duhamel_integrand hg t 0 t)
    (hS.intervalIntegrable_duhamel_integrand hh t 0 t)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := M * K)
    (f := fun s => S (t - s).toNNReal (g s) - S (t - s).toNNReal (h s)) (by
      intro s hs
      rw [uIoc_of_le ht] at hs
      rw [← map_sub]
      refine ((S _).le_opNorm _).trans (mul_le_mul (hM _ ?_) (hK s ⟨hs.1.le, hs.2⟩)
        (norm_nonneg _) hM0)
      rw [Real.coe_toNNReal']
      exact max_le (by linarith [hs.1]) ht)
  simpa [abs_of_nonneg ht] using this

/-- Integral difference estimate for Duhamel terms: if `‖S τ‖ ≤ M` for `τ ≤ t`, then
`‖∫₀ᵗ S (t - s) (g s - h s) ds‖ ≤ M ∫₀ᵗ ‖g s - h s‖ ds`. -/
theorem norm_duhamel_sub_le_integral (hS : IsC0Semigroup S) {g h : ℝ → X} (hg : Continuous g)
    (hh : Continuous h) {t M : ℝ} (ht : 0 ≤ t) (hM : ∀ τ : ℝ≥0, (τ : ℝ) ≤ t → ‖S τ‖ ≤ M) :
    ‖duhamel S g t - duhamel S h t‖ ≤ M * ∫ s in (0 : ℝ)..t, ‖g s - h s‖ := by
  unfold duhamel
  rw [← intervalIntegral.integral_sub (hS.intervalIntegrable_duhamel_integrand hg t 0 t)
    (hS.intervalIntegrable_duhamel_integrand hh t 0 t), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le ht (Filter.Eventually.of_forall
    fun s hs => ?_) ((continuous_const.mul (hg.sub hh).norm).intervalIntegrable 0 t)
  rw [← map_sub]
  refine ((S _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hM _ ?_) (norm_nonneg _))
  rw [Real.coe_toNNReal']
  exact max_le (by linarith [hs.1]) ht

end IsC0Semigroup

omit [NormedSpace ℝ X] [CompleteSpace X] in
/-- A map that is Lipschitz on every closed ball centred at `0` is continuous. -/
theorem continuous_of_lipschitzOnWith_closedBall {F : X → X}
    (hF : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (Metric.closedBall 0 R)) : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨L, hL⟩ := hF (‖x‖ + 1)
  refine hL.continuousOn.continuousAt (Metric.closedBall_mem_nhds_of_mem ?_)
  simp

/-- At time `0` a mild solution takes its initial value. -/
theorem IsMildSolution.apply_zero {S : ℝ≥0 → X →L[ℝ] X} {F : X → X} {x₀ : X} {T : ℝ}
    {u : ℝ → X} (hS : IsC0Semigroup S) (hu : IsMildSolution S F x₀ T u) (hT : 0 ≤ T) :
    u 0 = x₀ := by
  rw [hu.2.2 0 ⟨le_rfl, hT⟩]
  simp [duhamel, hS.map_zero]

/-- **Local existence of mild solutions, uniform on bounded sets of initial data.**
Let `S` be a C₀ semigroup on a real Banach space `X` and let `F : X → X` be Lipschitz on
bounded sets. For every radius `r` there are a time `T > 0` and a bound `R` such that every
initial value `x₀` with `‖x₀‖ ≤ r` has a continuous mild solution of `u' = A u + F u`,
`u 0 = x₀` on `[0, T]` with `‖u t‖ ≤ R` there. Both `T` and `R` are chosen before `x₀`, so
together with `exists_norm_sub_le_of_norm_le` the solution map is Lipschitz on the ball.
The proof is the Banach fixed-point theorem for the Duhamel map on `C([0, T], X)`. -/
theorem exists_isMildSolution {S : ℝ≥0 → X →L[ℝ] X} {F : X → X}
    (hS : IsC0Semigroup S)
    (hF : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (Metric.closedBall 0 R)) (r : ℝ) :
    ∃ T > 0, ∃ R : ℝ, ∀ x₀ : X, ‖x₀‖ ≤ r →
      ∃ u : ℝ → X, Continuous u ∧ IsMildSolution S F x₀ T u ∧ ∀ t ∈ Icc 0 T, ‖u t‖ ≤ R := by
  have hFc := continuous_of_lipschitzOnWith_closedBall hF
  obtain ⟨M₀, hM₀⟩ := hS.locally_bounded 1
  set M := max M₀ 1 with hM_def
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM : ∀ τ : ℝ≥0, (τ : ℝ) ≤ 1 → ‖S τ‖ ≤ M := fun τ hτ =>
    (hM₀ τ (by exact_mod_cast hτ)).trans (le_max_left _ _)
  set R := M * max r 0 + 1 with hR_def
  have hR1 : 1 ≤ R := by have : 0 ≤ M * max r 0 := by positivity
                         linarith
  obtain ⟨L, hL⟩ := hF R
  set K := ‖F 0‖ + L * R with hK_def
  have hK0 : 0 ≤ K := by positivity
  have hFK : ∀ y ∈ Metric.closedBall (0 : X) R, ‖F y‖ ≤ K := by
    intro y hy
    have h0 : (0 : X) ∈ Metric.closedBall (0 : X) R := Metric.mem_closedBall_self (by linarith)
    have := hL.dist_le_mul y hy 0 h0
    rw [dist_eq_norm, dist_eq_norm, sub_zero] at this
    have hy' : ‖y‖ ≤ R := by simpa using hy
    calc ‖F y‖ ≤ ‖F 0‖ + ‖F y - F 0‖ := by
          simpa using norm_le_insert' (F y) (F 0)
      _ ≤ ‖F 0‖ + L * ‖y‖ := by linarith
      _ ≤ K := by have := mul_le_mul_of_nonneg_left hy' L.coe_nonneg; linarith
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  set D := M * (K + 2 * L + 1) with hD_def
  have hD1 : 1 ≤ D := by
    have h1 : 1 ≤ K + 2 * L + 1 := by linarith
    have := mul_le_mul hM1 h1 zero_le_one (by linarith)
    linarith
  set T := 1 / D with hT_def
  have hT0 : 0 < T := by positivity
  have hT1 : T ≤ 1 := by rw [hT_def, div_le_one (by linarith)]; exact hD1
  have hTK : M * K * T ≤ 1 := by
    rw [hT_def, mul_one_div, div_le_one (by linarith), hD_def]
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hTL : M * L * T ≤ 1 / 2 := by
    rw [hT_def, mul_one_div, div_le_iff₀ (by linarith), hD_def]
    have := mul_le_mul_of_nonneg_left (show 2 * (L : ℝ) ≤ K + 2 * L + 1 by linarith)
      (show 0 ≤ M by linarith)
    linarith
  refine ⟨T, hT0, R, fun x₀ hx₀ => ?_⟩
  -- The Duhamel map on `C([0, T], X)`.
  set I := Icc (0 : ℝ) T
  let ext : C(I, X) → ℝ → X := fun u => IccExtend hT0.le u
  have hext : ∀ u, Continuous (ext u) := fun u => u.continuous.Icc_extend'
  let Φ : C(I, X) → C(I, X) := fun u =>
    ⟨fun t => S (t : ℝ).toNNReal x₀ + duhamel S (fun s => F (ext u s)) t,
      (((hS.continuous_apply x₀).comp continuous_real_toNNReal).add
        (hS.continuous_duhamel (hFc.comp (hext u)))).comp continuous_subtype_val⟩
  have hΦ : ∀ u (t : I), Φ u t = S (t : ℝ).toNNReal x₀ + duhamel S (fun s => F (ext u s)) t :=
    fun _ _ => rfl
  set B : Set C(I, X) := {u | ∀ t, ‖u t‖ ≤ R}
  have hB : IsClosed B := by
    have : B = ⋂ t : I, {u : C(I, X) | ‖u t‖ ≤ R} := by ext u; simp [B]
    rw [this]
    exact isClosed_iInter fun t =>
      isClosed_le (continuous_norm.comp (continuous_eval_const t))
        continuous_const
  have hextB : ∀ u ∈ B, ∀ s, ext u s ∈ Metric.closedBall (0 : X) R := by
    intro u hu s
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hu (projIcc 0 T hT0.le s)
  have hSt : ∀ t : I, ∀ τ : ℝ≥0, (τ : ℝ) ≤ t → ‖S τ‖ ≤ M :=
    fun t τ hτ => hM τ (hτ.trans (t.2.2.trans hT1))
  have hmaps : MapsTo Φ B B := by
    intro u hu t
    rw [hΦ]
    have h1 : ‖S (t : ℝ).toNNReal x₀‖ ≤ M * max r 0 := by
      refine ((S _).le_opNorm _).trans (mul_le_mul (hSt t _ ?_) (hx₀.trans (le_max_left _ _))
        (norm_nonneg _) (by linarith))
      rw [Real.coe_toNNReal']; exact max_le le_rfl t.2.1
    have h2 := hS.norm_duhamel_sub_le (hFc.comp (hext u)) continuous_const (h := fun _ => 0)
      t.2.1 (hSt t) (by linarith) (K := K) (fun s _ => by simpa using hFK _ (hextB u hu s))
    have h3 : M * K * t ≤ 1 := (mul_le_mul_of_nonneg_left t.2.2 (by positivity)).trans hTK
    have h4 : duhamel S (fun _ => (0 : X)) t = 0 := by simp [duhamel]
    rw [h4, sub_zero] at h2
    have h5 : ‖duhamel S (fun s => F (ext u s)) t‖ ≤ M * K * t := h2
    calc _ ≤ ‖S (t : ℝ).toNNReal x₀‖ + ‖duhamel S (fun s => F (ext u s)) t‖ := norm_add_le _ _
      _ ≤ R := by rw [hR_def]; linarith
  have hcontr : ∀ u ∈ B, ∀ v ∈ B, dist (Φ u) (Φ v) ≤ (1 / 2 : ℝ) * dist u v := by
    intro u hu v hv
    refine (ContinuousMap.dist_le (by positivity)).2 fun t => ?_
    rw [hΦ, hΦ, dist_eq_norm, add_sub_add_left_eq_sub]
    have h2 := hS.norm_duhamel_sub_le (hFc.comp (hext u)) (hFc.comp (hext v)) t.2.1 (hSt t)
      (by linarith) (K := L * dist u v) (fun s _ => by
        rw [← dist_eq_norm]
        refine (hL.dist_le_mul _ (hextB u hu s) _ (hextB v hv s)).trans
          (mul_le_mul_of_nonneg_left ?_ hL0)
        exact ContinuousMap.dist_apply_le_dist _)
    have h3 : M * (L * dist u v) * t ≤ M * L * T * dist u v := by
      have := mul_le_mul_of_nonneg_left t.2.2
        (show 0 ≤ M * L * dist u v by have := dist_nonneg (x := u) (y := v); positivity)
      nlinarith
    have h4 : M * L * T * dist u v ≤ 1 / 2 * dist u v :=
      mul_le_mul_of_nonneg_right hTL dist_nonneg
    exact h2.trans (h3.trans h4)
  have hK' : ContractingWith (1 / 2 : ℝ≥0) (hmaps.restrict Φ B B) := by
    refine ⟨by norm_num, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simpa [Subtype.dist_eq, MapsTo.val_restrict_apply] using hcontr a a.2 b b.2
  have h0B : (0 : C(I, X)) ∈ B := fun t => by simp; linarith
  obtain ⟨w, hwB, hw, -⟩ := ContractingWith.exists_fixedPoint' hB.isComplete hmaps hK' h0B
    (edist_ne_top _ _)
  refine ⟨ext w, hext w, ⟨(hext w).continuousOn,
    fun t _ => hS.intervalIntegrable_duhamel_integrand (hFc.comp (hext w)) t 0 t,
    fun t ht => ?_⟩, fun t _ => by simpa using hextB w hwB t⟩
  have hwt : ext w t = w ⟨t, ht⟩ := IccExtend_of_mem _ _ ht
  rw [hwt]
  exact (congrArg (fun f : C(I, X) => f ⟨t, ht⟩) hw.eq).symm

/-- **Integral Grönwall inequality.** A continuous `ψ ≥ 0` with
`ψ t ≤ a + K ∫₀ᵗ ψ` on `[0, T]` (`K ≥ 0`) satisfies `ψ t ≤ a exp (K t)` there. -/
private theorem le_mul_exp_of_le_add_mul_integral {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hψ0 : ∀ t, 0 ≤ ψ t) {a K T : ℝ} (hK : 0 ≤ K)
    (h : ∀ t ∈ Icc 0 T, ψ t ≤ a + K * ∫ s in (0 : ℝ)..t, ψ s) :
    ∀ t ∈ Icc 0 T, ψ t ≤ a * Real.exp (K * t) := by
  set Ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, ψ s with hΨ_def
  have hd : ∀ t, HasDerivAt Ψ (ψ t) t := fun t => (hψ.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hΨ0 : ∀ t ∈ Icc 0 T, 0 ≤ Ψ t := fun t ht =>
    intervalIntegral.integral_nonneg ht.1 fun s _ => hψ0 s
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le (f := Ψ) (f' := ψ) (δ := 0) (K := K)
    (ε := a) (a := 0) (b := T) (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).hasDerivWithinAt) (by simp [Ψ]) (fun t ht => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hψ0 t),
        abs_of_nonneg (hΨ0 t ⟨ht.1, ht.2.le⟩)]
      linarith [h t ⟨ht.1, ht.2.le⟩])
  intro t ht
  have h1 := hG t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (hΨ0 t ht), sub_zero] at h1
  have h2 : ψ t ≤ a + K * gronwallBound 0 K a t :=
    (h t ht).trans (by linarith [mul_le_mul_of_nonneg_left h1 hK])
  rcases eq_or_ne K 0 with rfl | hK0
  · simpa using h2
  · rw [gronwallBound_of_K_ne_0 hK0] at h2
    have : a + K * (0 * Real.exp (K * t) + a / K * (Real.exp (K * t) - 1)) =
        a * Real.exp (K * t) := by field_simp; ring
    linarith

/-- **Lipschitz dependence on initial data.** For every bound `R` and time `T` there is one
constant `C` (namely `M exp (M L T)` with `M` bounding `‖S τ‖` on `[0, T]` and `L` a Lipschitz
constant of `F` on the ball of radius `R`) such that any two mild solutions on `[0, T]` that stay
in that ball satisfy `‖u t - v t‖ ≤ C ‖x₀ - y₀‖` on `[0, T]`. The constant is chosen before the
solutions. -/
theorem exists_norm_sub_le_of_norm_le {S : ℝ≥0 → X →L[ℝ] X} {F : X → X}
    (hS : IsC0Semigroup S)
    (hF : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (Metric.closedBall 0 R)) (R T : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (x₀ y₀ : X) (u v : ℝ → X), IsMildSolution S F x₀ T u →
      IsMildSolution S F y₀ T v → (∀ t ∈ Icc 0 T, ‖u t‖ ≤ R ∧ ‖v t‖ ≤ R) →
      ∀ t ∈ Icc 0 T, ‖u t - v t‖ ≤ C * ‖x₀ - y₀‖ := by
  rcases lt_or_ge T 0 with hT | hT
  · exact ⟨0, le_rfl, fun _ _ _ _ _ _ _ t ht => absurd (ht.1.trans ht.2) (not_le.2 hT)⟩
  have hFc := continuous_of_lipschitzOnWith_closedBall hF
  obtain ⟨L, hL⟩ := hF R
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  obtain ⟨M₀, hM₀⟩ := hS.locally_bounded T.toNNReal
  set M := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ τ : ℝ≥0, (τ : ℝ) ≤ T → ‖S τ‖ ≤ M := fun τ hτ =>
    (hM₀ τ (Real.le_toNNReal_iff_coe_le hT |>.2 hτ)).trans (le_max_left _ _)
  refine ⟨M * Real.exp (M * L * T), by positivity, fun x₀ y₀ u v hu hv hR => ?_⟩
  have hp : Continuous fun t => (projIcc 0 T hT t : ℝ) := continuous_subtype_val.comp
    continuous_projIcc
  have hpm : ∀ t, (projIcc 0 T hT t : ℝ) ∈ Icc 0 T := fun t => (projIcc 0 T hT t).2
  set u' := fun t => u (projIcc 0 T hT t)
  set v' := fun t => v (projIcc 0 T hT t)
  have hu' : Continuous u' := hu.1.comp_continuous hp hpm
  have hv' : Continuous v' := hv.1.comp_continuous hp hpm
  have hu'e : ∀ t ∈ Icc 0 T, u' t = u t := fun t ht => by simp [u', projIcc_of_mem hT ht]
  have hv'e : ∀ t ∈ Icc 0 T, v' t = v t := fun t ht => by simp [v', projIcc_of_mem hT ht]
  have hu'B : ∀ s, u' s ∈ Metric.closedBall (0 : X) R := fun s => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hR _ (hpm s)).1
  have hv'B : ∀ s, v' s ∈ Metric.closedBall (0 : X) R := fun s => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hR _ (hpm s)).2
  -- The Duhamel terms only see the solutions on `[0, t] ⊆ [0, T]`.
  have hcongr : ∀ (w w' : ℝ → X), (∀ s ∈ Icc 0 T, w' s = w s) → ∀ t ∈ Icc 0 T,
      duhamel S (fun s => F (w s)) t = duhamel S (fun s => F (w' s)) t := by
    intro w w' hw t ht
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    simp only [hw s ⟨hs.1, hs.2.trans ht.2⟩]
  set ψ := fun t => ‖u' t - v' t‖
  have hψ : Continuous ψ := (hu'.sub hv').norm
  have hineq : ∀ t ∈ Icc 0 T,
      ψ t ≤ M * ‖x₀ - y₀‖ + M * L * ∫ s in (0 : ℝ)..t, ψ s := by
    intro t ht
    have hut := hu.2.2 t ht
    have hvt := hv.2.2 t ht
    rw [hcongr u u' hu'e t ht] at hut
    rw [hcongr v v' hv'e t ht] at hvt
    have e : u' t - v' t = (S t.toNNReal (x₀ - y₀)) +
        (duhamel S (fun s => F (u' s)) t - duhamel S (fun s => F (v' s)) t) := by
      rw [hu'e t ht, hv'e t ht, hut, hvt, map_sub]; abel
    have h1 : ‖S t.toNNReal (x₀ - y₀)‖ ≤ M * ‖x₀ - y₀‖ := by
      refine ((S _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hM _ ?_) (norm_nonneg _))
      rw [Real.coe_toNNReal']; exact max_le ht.2 hT
    have h2 := hS.norm_duhamel_sub_le_integral (hFc.comp hu') (hFc.comp hv') ht.1
      (fun τ hτ => hM τ (hτ.trans ht.2))
    have h3 : ∫ s in (0 : ℝ)..t, ‖F (u' s) - F (v' s)‖ ≤ ∫ s in (0 : ℝ)..t, L * ψ s := by
      refine intervalIntegral.integral_mono_on ht.1
        ((((hFc.comp hu').sub (hFc.comp hv')).norm).intervalIntegrable 0 t)
        ((continuous_const.mul hψ).intervalIntegrable 0 t) fun s _ => ?_
      rw [← dist_eq_norm]
      exact hL.dist_le_mul _ (hu'B s) _ (hv'B s) |>.trans_eq (by rw [dist_eq_norm])
    rw [intervalIntegral.integral_const_mul] at h3
    have h4 := mul_le_mul_of_nonneg_left h3 hM0
    rw [show ψ t = ‖u' t - v' t‖ from rfl, e]
    refine (norm_add_le _ _).trans ?_
    have : ‖duhamel S (fun s => F (u' s)) t - duhamel S (fun s => F (v' s)) t‖ ≤
        M * ∫ s in (0 : ℝ)..t, ‖F (u' s) - F (v' s)‖ := h2
    nlinarith
  have hG := le_mul_exp_of_le_add_mul_integral hψ (fun t => norm_nonneg _)
    (by positivity) hineq
  intro t ht
  have h := hG t ht
  rw [show ψ t = ‖u t - v t‖ by simp [ψ, hu'e t ht, hv'e t ht]] at h
  refine h.trans ?_
  rw [mul_right_comm]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 (by positivity))) hM0) (norm_nonneg _)

/-- **Uniqueness of mild solutions.** Two mild solutions on `[0, T]` with the same initial
value agree on `[0, T]`. -/
theorem IsMildSolution.eqOn {S : ℝ≥0 → X →L[ℝ] X} {F : X → X} {x₀ : X} {T : ℝ}
    {u v : ℝ → X} (hS : IsC0Semigroup S)
    (hF : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (Metric.closedBall 0 R))
    (hu : IsMildSolution S F x₀ T u) (hv : IsMildSolution S F x₀ T v) :
    EqOn u v (Icc 0 T) := by
  obtain ⟨Cu, hCu⟩ := isCompact_Icc.exists_bound_of_continuousOn hu.1
  obtain ⟨Cv, hCv⟩ := isCompact_Icc.exists_bound_of_continuousOn hv.1
  obtain ⟨C, -, hC⟩ := exists_norm_sub_le_of_norm_le hS hF (max Cu Cv) T
  intro t ht
  have := hC x₀ x₀ u v hu hv (fun s hs => ⟨(hCu s hs).trans (le_max_left _ _),
    (hCv s hs).trans (le_max_right _ _)⟩) t ht
  rw [sub_self, norm_zero, mul_zero] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

omit [CompleteSpace X] in
/-- The Duhamel integrand of a mild solution is interval integrable on subintervals of
`[0, T]`. -/
private theorem intervalIntegrable_mild {S : ℝ≥0 → X →L[ℝ] X} {F : X → X} {T : ℝ}
    {u : ℝ → X} (hS : IsC0Semigroup S) (hFc : Continuous F) (hu : ContinuousOn u (Icc 0 T))
    (c : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    IntervalIntegrable (fun r => S (c - r).toNNReal (F (u r))) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  exact hS.continuous_uncurry.comp_continuousOn
    ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).continuousOn.prodMk
      (hFc.comp_continuousOn (hu.mono (Icc_subset_Icc ha hb))))

/-- **Restart (semiflow) identity.** If `u` is a mild solution on `[0, T]` from `x₀`, then for
every `s ∈ [0, T]` the shifted curve `τ ↦ u (s + τ)` is a mild solution on `[0, T - s]` from
`u s`. Together with uniqueness this makes the time-`t` maps compose: the solution from `x₀`
at time `s + τ` is the solution from `u s` at time `τ`. -/
theorem IsMildSolution.restart {S : ℝ≥0 → X →L[ℝ] X} {F : X → X} {x₀ : X}
    {T : ℝ} {u : ℝ → X} (hS : IsC0Semigroup S)
    (hF : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (Metric.closedBall 0 R))
    (hu : IsMildSolution S F x₀ T u) {s : ℝ} (hs : s ∈ Icc 0 T) :
    IsMildSolution S F (u s) (T - s) fun τ => u (s + τ) := by
  have hFc := continuous_of_lipschitzOnWith_closedBall hF
  have huc : ContinuousOn (fun τ => u (s + τ)) (Icc 0 (T - s)) :=
    hu.1.comp (continuousOn_const.add continuousOn_id) fun τ hτ =>
      ⟨by linarith [hs.1, hτ.1], by linarith [hτ.2]⟩
  refine ⟨huc, fun t ht => intervalIntegrable_mild hS hFc huc t le_rfl ht.1 ht.2,
    fun τ hτ => ?_⟩
  have hτ0 : 0 ≤ τ := hτ.1
  have hsτ : s + τ ∈ Icc 0 T := ⟨by linarith [hs.1], by linarith [hτ.2]⟩
  -- Integrability of the Duhamel integrand on `[0, s]` and on `[s, s + τ]`.
  have hI₁ := intervalIntegrable_mild hS hFc hu.1 s le_rfl hs.1 hs.2
  have hI₂ := intervalIntegrable_mild hS hFc hu.1 (s + τ) le_rfl hs.1 hs.2
  have hI₃ := intervalIntegrable_mild hS hFc hu.1 (s + τ) hs.1
    (by linarith : s ≤ s + τ) hsτ.2
  -- Split the Duhamel integral at `s`.
  have hsplit : duhamel S (fun r => F (u r)) (s + τ) =
      (∫ r in (0 : ℝ)..s, S (s + τ - r).toNNReal (F (u r))) +
        ∫ r in s..s + τ, S (s + τ - r).toNNReal (F (u r)) := by
    rw [duhamel]; exact (intervalIntegral.integral_add_adjacent_intervals hI₂ hI₃).symm
  -- On `[0, s]`, `S (s + τ - r) = S τ ∘ S (s - r)`.
  have hfirst : ∫ r in (0 : ℝ)..s, S (s + τ - r).toNNReal (F (u r)) =
      S τ.toNNReal (duhamel S (fun r => F (u r)) s) := by
    rw [duhamel, ← (S τ.toNNReal).intervalIntegral_comp_comm hI₁]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hs.1] at hr
    have : (s + τ - r).toNNReal = τ.toNNReal + (s - r).toNNReal := by
      rw [← Real.toNNReal_add hτ0 (by linarith [hr.2])]; ring_nf
    simp only [this, hS.map_add, ContinuousLinearMap.comp_apply]
  -- On `[s, s + τ]`, shift the variable by `s`.
  have hsecond : ∫ r in s..s + τ, S (s + τ - r).toNNReal (F (u r)) =
      duhamel S (fun r => F (u (s + r))) τ := by
    have h := intervalIntegral.integral_comp_add_left
      (fun r => S (s + τ - r).toNNReal (F (u r))) s (a := 0) (b := τ)
    rw [add_zero] at h
    rw [duhamel, ← h]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [show s + τ - (s + r) = τ - r by ring]
  have hx : S (s + τ).toNNReal x₀ = S τ.toNNReal (S s.toNNReal x₀) := by
    rw [Real.toNNReal_add hs.1 hτ0, add_comm, hS.map_add, ContinuousLinearMap.comp_apply]
  dsimp only
  rw [hu.2.2 _ hsτ, hu.2.2 s hs, hsplit, hfirst, ← hsecond, hx, map_add]
  abel

section Nemytskii

variable {K E : Type*} [TopologicalSpace K] [CompactSpace K] [NormedAddCommGroup E]

/-- The **Nemytskii (superposition) operator** `u ↦ f ∘ u` on `C(K, E)`. In the frozen setting,
`K = Ω̄` and `E = ℝᵐ`, and this is the reaction term `F(u)(x) = f(u(x))`. -/
def nemytskii (f : E → E) (hf : Continuous f) (u : C(K, E)) : C(K, E) :=
  (ContinuousMap.mk f hf).comp u

/-- If `f` is Lipschitz on bounded sets, so is the Nemytskii operator on `C(K, E)` with the sup
norm, with the same constants. So the reaction term of the frozen setting satisfies the
hypothesis `hF` of `exists_isMildSolution`. -/
theorem lipschitzOnWith_nemytskii {f : E → E} (hfc : Continuous f)
    (hf : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L f (Metric.closedBall 0 R)) :
    ∀ R : ℝ, ∃ L : ℝ≥0,
      LipschitzOnWith L (nemytskii (K := K) f hfc) (Metric.closedBall 0 R) := by
  intro R
  obtain ⟨L, hL⟩ := hf R
  refine ⟨L, LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_⟩
  refine (ContinuousMap.dist_le (by positivity)).2 fun k => ?_
  have hb : ∀ w : C(K, E), w ∈ Metric.closedBall 0 R → w k ∈ Metric.closedBall (0 : E) R :=
    fun w hw => by
      rw [Metric.mem_closedBall, dist_zero_right] at hw ⊢
      exact (w.norm_coe_le_norm k).trans hw
  exact (hL.dist_le_mul _ (hb u hu) _ (hb v hv)).trans
    (mul_le_mul_of_nonneg_left (ContinuousMap.dist_apply_le_dist k) L.coe_nonneg)

end Nemytskii

/-- **Bounded generators.** For a bounded operator `A`, `t ↦ exp (t A)` is a C₀ semigroup
(indeed norm continuous). This is the finite-dimensional/ODE case of the interface; the PDE
case uses an unbounded generator such as the Neumann Laplacian, whose semigroup is only
strongly continuous. -/
theorem isC0Semigroup_exp (A : X →L[ℝ] X) :
    IsC0Semigroup fun t : ℝ≥0 => NormedSpace.exp ((t : ℝ) • A) := by
  let : NormedAlgebra ℚ (X →L[ℝ] X) := NormedAlgebra.restrictScalars ℚ ℝ (X →L[ℝ] X)
  have hc : Continuous fun t : ℝ≥0 => NormedSpace.exp ((t : ℝ) • A) :=
    NormedSpace.exp_continuous.comp (NNReal.continuous_coe.smul continuous_const)
  refine ⟨by simp, fun s t => ?_, fun x => hc.clm_apply continuous_const, fun T => ?_⟩
  · rw [NNReal.coe_add, add_smul, NormedSpace.exp_add_of_commute
      (((Commute.refl A).smul_left _).smul_right _), ContinuousLinearMap.mul_def]
  · obtain ⟨C, hC⟩ := (isCompact_Icc (a := 0) (b := T)).exists_bound_of_continuousOn hc.continuousOn
    exact ⟨C, fun t ht => hC t ⟨bot_le, ht⟩⟩

/-- **Incompatible spaces (boundary case).** The quadratic reaction term `u ↦ u²` does not map
`L²(0, 1)` into itself: `u x = x ^ (-1/3)` is square integrable on `(0, 1)` but `u²` is not.
So `(X, F) = (L²(0, 1), u ↦ u²)` does not satisfy the hypotheses of `exists_isMildSolution`
(there is no map `F : X → X` at all); this is why the frozen phase space is `C(Ω̄)`. -/
theorem exists_memLp_two_not_memLp_two_sq :
    ∃ u : ℝ → ℝ, MemLp u 2 (volume.restrict (Ioo 0 1)) ∧
      ¬ MemLp (fun x => u x ^ 2) 2 (volume.restrict (Ioo 0 1)) := by
  have hm : ∀ p : ℝ, AEStronglyMeasurable (fun x : ℝ => x ^ p) (volume.restrict (Ioo 0 1)) :=
    fun p => (measurable_id.pow_const p).aestronglyMeasurable
  have hsq : ∀ p : ℝ, ∀ x ∈ Ioo (0 : ℝ) 1, (x ^ p) ^ 2 = x ^ (2 * p) := by
    intro p x hx
    rw [mul_comm, Real.rpow_mul hx.1.le, Real.rpow_two]
  refine ⟨fun x => x ^ (-(1 / 3) : ℝ), ?_, ?_⟩
  · rw [memLp_two_iff_integrable_sq (hm _), ← IntegrableOn,
      integrableOn_congr_fun (hsq _) measurableSet_Ioo,
      intervalIntegral.integrableOn_Ioo_rpow_iff one_pos]
    norm_num
  · have hm2 : AEStronglyMeasurable (fun x : ℝ => (x ^ (-(1 / 3) : ℝ)) ^ 2)
        (volume.restrict (Ioo 0 1)) := (hm _).pow 2
    rw [memLp_two_iff_integrable_sq hm2, ← IntegrableOn,
      integrableOn_congr_fun (g := fun x : ℝ => x ^ (2 * (2 * (-(1 / 3) : ℝ))))
        (fun x hx => by simp only; rw [hsq _ x hx, hsq _ x hx]) measurableSet_Ioo,
      intervalIntegral.integrableOn_Ioo_rpow_iff one_pos]
    norm_num

end MathlibExt.Analysis.PDE.SemilinearFlow
