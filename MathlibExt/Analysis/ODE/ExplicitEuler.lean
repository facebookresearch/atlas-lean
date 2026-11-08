/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.DiscreteGronwall
import MathlibExt.Analysis.ODE.MaximalSolution

/-!
# Explicit Euler convergence

This file proves a quadratic local truncation-error bound for the explicit Euler method and uses
it with global ODE existence and discrete Grönwall to obtain first-order convergence.
-/

@[expose] public section

namespace MathlibExt.Analysis.ODE.ExplicitEulerWanted

private lemma explicitEuler_hasDerivAt_velocity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E → E} (hf : ContDiff ℝ 2 (Function.uncurry f))
    {x : ℝ → E} {t : ℝ} (hx : HasDerivAt x (f t (x t)) t) :
    HasDerivAt (fun s ↦ f s (x s))
      (fderiv ℝ (Function.uncurry f) (t, x t) (1, f t (x t))) t := by
  have hinner : HasDerivAt (fun s : ℝ ↦ (s, x s)) (1, f t (x t)) t :=
    (hasDerivAt_id t).prodMk hx
  simpa [Function.comp_def] using
    ((hf.differentiable (by norm_num) (t, x t)).hasFDerivAt.comp_hasDerivAt t hinner)

private lemma explicitEuler_velocity_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E → E} {t₀ T : ℝ} (hT : t₀ ≤ T)
    (hf : ContDiff ℝ 2 (Function.uncurry f)) {x : ℝ → E}
    (hx : ∀ t ∈ Set.Icc t₀ T, HasDerivAt x (f t (x t)) t) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Set.Icc t₀ T, ∀ t ∈ Set.Icc t₀ T,
      ‖f s (x s) - f t (x t)‖ ≤ M * ‖s - t‖ := by
  let φ : ℝ → E := fun s ↦ f s (x s)
  let d : ℝ → E := fun s ↦
    fderiv ℝ (Function.uncurry f) (s, x s) (1, φ s)
  have hxcont : ContinuousOn x (Set.Icc t₀ T) := fun s hs ↦
    (hx s hs).continuousAt.continuousWithinAt
  have hpcont : ContinuousOn (fun s : ℝ ↦ (s, x s)) (Set.Icc t₀ T) :=
    continuousOn_id.prodMk hxcont
  have hφcont : ContinuousOn φ (Set.Icc t₀ T) := by
    simpa [φ, Function.comp_def] using hf.continuous.comp_continuousOn hpcont
  have hvcont : ContinuousOn (fun s : ℝ ↦ ((1 : ℝ), φ s)) (Set.Icc t₀ T) :=
    continuousOn_const.prodMk hφcont
  have hdcont : ContinuousOn d (Set.Icc t₀ T) := by
    simpa [d, Function.comp_def] using
      (hf.continuous_fderiv_apply (by norm_num)).comp_continuousOn (hpcont.prodMk hvcont)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hdcont
  have hM0 : 0 ≤ M := (norm_nonneg (d t₀)).trans (hM t₀ ⟨le_rfl, hT⟩)
  refine ⟨M, hM0, ?_⟩
  intro s hs t ht
  have hderiv : ∀ u ∈ Set.Icc t₀ T,
      HasDerivWithinAt φ (d u) (Set.Icc t₀ T) u := fun u hu ↦ by
    exact (explicitEuler_hasDerivAt_velocity hf (hx u hu)).hasDerivWithinAt
  simpa [φ] using
    (Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hM (convex_Icc t₀ T) ht hs)

/-- A solution of a `C²` ODE has a uniform quadratic explicit-Euler local error on a compact
time interval. -/
theorem _root_.ODE.exists_explicitEuler_localTruncationError_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E → E) (t₀ T : ℝ) (hT : t₀ < T)
    (hf : ContDiff ℝ 2 (Function.uncurry f))
    (x : ℝ → E) (hx : ∀ t ∈ Set.Icc t₀ T, HasDerivAt x (f t (x t)) t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ Set.Ioc 0 (T - t₀),
      ∀ t ∈ Set.Icc t₀ T, t + h ≤ T →
        ‖x (t + h) - (x t + h • f t (x t))‖ ≤ C * h ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := explicitEuler_velocity_lipschitz hT.le hf hx
  refine ⟨M, hM0, ?_⟩
  intro h hh t ht hth
  let φ : ℝ → E := fun s ↦ f s (x s)
  let r : ℝ → E := fun s ↦ x s - (x t + (s - t) • φ t)
  have hseg : Set.Icc t (t + h) ⊆ Set.Icc t₀ T := by
    intro s hs
    exact ⟨ht.1.trans hs.1, hs.2.trans hth⟩
  have hrderiv : ∀ s ∈ Set.Icc t (t + h),
      HasDerivWithinAt r (φ s - φ t) (Set.Icc t (t + h)) s := by
    intro s hs
    have hlinear : HasDerivAt (fun u : ℝ ↦ (u - t) • φ t) (φ t) s := by
      simpa using ((hasDerivAt_id s).sub_const t).smul_const (φ t)
    have hsum : HasDerivAt (fun u : ℝ ↦ x t + (u - t) • φ t) (φ t) s := by
      exact hlinear.const_add (x t)
    exact ((hx s (hseg hs)).sub hsum).hasDerivWithinAt
  have hrbound : ∀ s ∈ Set.Ico t (t + h), ‖φ s - φ t‖ ≤ M * h := by
    intro s hs
    calc
      ‖φ s - φ t‖ ≤ M * ‖s - t‖ := hM s (hseg (Set.Ico_subset_Icc_self hs)) t ht
      _ ≤ M * h := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.1)]
        gcongr
        linarith [hs.2]
  have hr := norm_image_sub_le_of_norm_deriv_le_segment' hrderiv hrbound
    (t + h) (Set.right_mem_Icc.mpr (by linarith [hh.1]))
  simpa [r, φ, pow_two, mul_assoc] using hr

private lemma explicitEuler_exists_solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E → E) (t₀ T : ℝ) (x₀ : E) (L : NNReal)
    (hT : t₀ < T) (hf : ContDiff ℝ 2 (Function.uncurry f))
    (hlip : ∀ t ∈ Set.Icc t₀ T, LipschitzWith L (f t)) :
    ∃ x : ℝ → E, x t₀ = x₀ ∧ ∀ t ∈ Set.Icc t₀ T, HasDerivAt x (f t (x t)) t := by
  let g : ℝ → E → E := fun t y ↦ f (max t₀ (min t T)) y
  have hgcont : Continuous (Function.uncurry g) := by
    have hp : Continuous (fun p : ℝ × E ↦ (max t₀ (min p.1 T), p.2)) := by
      fun_prop
    change Continuous (fun p : ℝ × E ↦ f (max t₀ (min p.1 T)) p.2)
    exact hf.continuous.comp hp
  have hglip : ∀ t, LipschitzWith L (g t) := by
    intro t
    apply hlip
    exact ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  obtain ⟨x, hx, _⟩ :=
    MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
      g t₀ x₀ L hgcont hglip
  refine ⟨x, hx.1, ?_⟩
  intro t ht
  simpa [g, min_eq_left ht.2, max_eq_right ht.1] using hx.2 t

private lemma explicitEuler_error_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E → E} {t₀ T h C : ℝ} {L : NNReal}
    {x : ℝ → E} {X : ℕ → E} {k : ℕ}
    (hh : 0 < h)
    (hlip : ∀ t ∈ Set.Icc t₀ T, LipschitzWith L (f t))
    (hlocal : ∀ t ∈ Set.Icc t₀ T, t + h ≤ T →
      ‖x (t + h) - (x t + h • f t (x t))‖ ≤ C * h ^ 2)
    (hX : ∀ n, X (n + 1) = X n + h • f (t₀ + (n : ℝ) * h) (X n))
    (hk : ((k + 1 : ℕ) : ℝ) * h ≤ T - t₀) :
    ‖X (k + 1) - x (t₀ + ((k + 1 : ℕ) : ℝ) * h)‖ ≤
      (1 + (L : ℝ) * h) * ‖X k - x (t₀ + (k : ℝ) * h)‖ + C * h ^ 2 := by
  let tk : ℝ := t₀ + (k : ℝ) * h
  have hkh : (k : ℝ) * h ≤ T - t₀ := by
    calc
      (k : ℝ) * h ≤ ((k + 1 : ℕ) : ℝ) * h := by
        gcongr
        exact_mod_cast Nat.le_succ k
      _ ≤ T - t₀ := hk
  have htk : tk ∈ Set.Icc t₀ T := by
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hh.le)
    · dsimp [tk]
      linarith
  have hnext : t₀ + ((k + 1 : ℕ) : ℝ) * h = tk + h := by
    dsimp [tk]
    push_cast
    ring
  have htknext : tk + h ≤ T := by
    rw [← hnext]
    linarith
  have hfield : ‖f tk (X k) - f tk (x tk)‖ ≤
      (L : ℝ) * ‖X k - x tk‖ := by
    simpa only [dist_eq_norm] using (hlip tk htk).dist_le_mul (X k) (x tk)
  have hsmul : ‖h • (f tk (X k) - f tk (x tk))‖ ≤
      h * ((L : ℝ) * ‖X k - x tk‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left hfield hh.le
  have herr : X (k + 1) - x (t₀ + ((k + 1 : ℕ) : ℝ) * h) =
      (X k - x tk) + h • (f tk (X k) - f tk (x tk)) -
        (x (tk + h) - (x tk + h • f tk (x tk))) := by
    rw [hX k, hnext]
    dsimp [tk]
    module
  rw [herr]
  calc
    ‖(X k - x tk) + h • (f tk (X k) - f tk (x tk)) -
        (x (tk + h) - (x tk + h • f tk (x tk)))‖
        ≤ ‖(X k - x tk) + h • (f tk (X k) - f tk (x tk))‖ +
          ‖x (tk + h) - (x tk + h • f tk (x tk))‖ := norm_sub_le _ _
    _ ≤ (‖X k - x tk‖ + ‖h • (f tk (X k) - f tk (x tk))‖) + C * h ^ 2 := by
      gcongr
      · exact norm_add_le _ _
      · exact hlocal tk htk htknext
    _ ≤ (‖X k - x tk‖ + h * ((L : ℝ) * ‖X k - x tk‖)) + C * h ^ 2 := by
      gcongr
    _ = (1 + (L : ℝ) * h) * ‖X k - x tk‖ + C * h ^ 2 := by ring

/-- Explicit Euler is first-order convergent: for a `C^2` right-hand side,
Lipschitz in the state, a true solution exists on `[t₀, T]` and the Euler
polygonal approximations have global error `O(h)` with a uniform constant.
Sources: `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` /
`Ordinary differential equations`, entries `explicit Euler method`,
`convergence` and `order` (unmapped);
E. Hairer, S. P. Nørsett and G. Wanner, Solving Ordinary Differential
Equations I, 2nd ed., Theorem I.7.3;
stable ref https://en.wikipedia.org/wiki/Euler_method.

Proves `Wanted` entry `explicit_euler_first_order_convergence`.

Proof: clamp the time variable and use global Picard--Lindelöf for existence.  The local bound
above and Mathlib's discrete Grönwall inequality then give the first-order global estimate.
-/
theorem explicit_euler_first_order_convergence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E → E) (t₀ T : ℝ) (x₀ : E) (L : NNReal)
    (hT : t₀ < T)
    (hf : ContDiff ℝ 2 (Function.uncurry f))
    (hlip : ∀ t ∈ Set.Icc t₀ T, LipschitzWith L (f t)) :
    ∃ x : ℝ → E, x t₀ = x₀ ∧ (∀ t ∈ Set.Icc t₀ T, HasDerivAt x (f t (x t)) t) ∧
      ∃ C : ℝ, ∀ h ∈ Set.Ioc 0 (T - t₀), ∀ X : ℕ → E, X 0 = x₀ →
        (∀ n, X (n + 1) = X n + h • f (t₀ + (n : ℝ) * h) (X n)) →
        ∀ n : ℕ, (n : ℝ) * h ≤ T - t₀ →
          ‖X n - x (t₀ + (n : ℝ) * h)‖ ≤ C * h := by
  obtain ⟨x, hx0, hx⟩ := explicitEuler_exists_solution f t₀ T x₀ L hT hf hlip
  obtain ⟨C₁, hC₁0, hlocalAll⟩ :=
    ODE.exists_explicitEuler_localTruncationError_le f t₀ T hT hf x hx
  let D : ℝ := T - t₀
  refine ⟨x, hx0, hx, C₁ * D * Real.exp ((L : ℝ) * D), ?_⟩
  intro h hh X hX0 hX n hn
  have hlocal : ∀ t ∈ Set.Icc t₀ T, t + h ≤ T →
      ‖x (t + h) - (x t + h • f t (x t))‖ ≤ C₁ * h ^ 2 :=
    hlocalAll h hh
  let err : ℕ → ℝ := fun k ↦ ‖X k - x (t₀ + (k : ℝ) * h)‖
  let u : ℕ → ℝ := fun k ↦ if k ≤ n then err k else 0
  let c : ℕ → ℝ := fun _ ↦ (L : ℝ) * h
  let b : ℕ → ℝ := fun _ ↦ C₁ * h ^ 2
  have hu : ∀ k ≥ 0, u (k + 1) ≤ (1 + c k) * u k + b k := by
    intro k _
    by_cases hk : k < n
    · have hkle : k ≤ n := hk.le
      have hk1le : k + 1 ≤ n := Nat.succ_le_iff.mpr hk
      have hkstep : ((k + 1 : ℕ) : ℝ) * h ≤ T - t₀ := by
        calc
          ((k + 1 : ℕ) : ℝ) * h ≤ (n : ℝ) * h := by
            apply mul_le_mul_of_nonneg_right _ hh.1.le
            exact_mod_cast hk1le
          _ ≤ T - t₀ := hn
      simp only [u, ite_eq_left hk1le, ite_eq_left hkle, c, b, err]
      exact explicitEuler_error_step hh.1 hlip hlocal hX hkstep
    · have hnot : ¬k + 1 ≤ n := by omega
      have huk : 0 ≤ u k := by
        dsimp [u]
        split <;> simp_all [err]
      have hck : 0 ≤ 1 + c k := by
        exact add_nonneg zero_le_one (mul_nonneg L.2 hh.1.le)
      have hbk : 0 ≤ b k := by
        exact mul_nonneg hC₁0 (sq_nonneg h)
      rw [show u (k + 1) = 0 by simp [u, hnot]]
      exact add_nonneg (mul_nonneg hck huk) hbk
  have hc : ∀ k ≥ 0, 0 ≤ c k := by
    intro k _
    dsimp [c]
    exact mul_nonneg L.2 hh.1.le
  have hb : ∀ k ≥ 0, 0 ≤ b k := by
    intro k _
    dsimp [b]
    positivity
  have hgr := discrete_gronwall (u := u) (c := c) (b := b) (n₀ := 0)
    (by positivity) hu hc hb (Nat.zero_le n)
  have hgr' : err n ≤ ((n : ℝ) * (C₁ * h ^ 2)) *
      Real.exp ((n : ℝ) * ((L : ℝ) * h)) := by
    simpa [u, c, b, err, hX0, hx0] using hgr
  have hbase : (n : ℝ) * (C₁ * h ^ 2) ≤ C₁ * D * h := by
    calc
      (n : ℝ) * (C₁ * h ^ 2) = C₁ * ((n : ℝ) * h) * h := by ring
      _ ≤ C₁ * D * h := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hC₁0) hh.1.le
  have hexp : (n : ℝ) * ((L : ℝ) * h) ≤ (L : ℝ) * D := by
    calc
      (n : ℝ) * ((L : ℝ) * h) = (L : ℝ) * ((n : ℝ) * h) := by ring
      _ ≤ (L : ℝ) * D := by
        exact mul_le_mul_of_nonneg_left hn L.2
  change err n ≤ (C₁ * D * Real.exp ((L : ℝ) * D)) * h
  calc
    err n ≤ ((n : ℝ) * (C₁ * h ^ 2)) *
        Real.exp ((n : ℝ) * ((L : ℝ) * h)) := hgr'
    _ ≤ (C₁ * D * h) * Real.exp ((L : ℝ) * D) := by
      have hD0 : 0 ≤ D := by
        dsimp [D]
        linarith
      exact mul_le_mul hbase (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le
        (mul_nonneg (mul_nonneg hC₁0 hD0) hh.1.le)
    _ = (C₁ * D * Real.exp ((L : ℝ) * D)) * h := by ring

/-- Explicit Euler consistency: one step from the exact solution has local
truncation error `O(h^2)`.
Sources: `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` /
`Ordinary differential equations`, entry `consistency` (unmapped);
E. Hairer, S. P. Nørsett and G. Wanner, Solving Ordinary Differential
Equations I, 2nd ed., Section I.7.

Proves `Wanted` entry `explicit_euler_local_truncation_error`.

Proof: differentiate the velocity by the chain rule, bound that derivative on the compact time
interval, and apply the mean value inequality twice.
-/
theorem explicit_euler_local_truncation_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E → E) (t₀ T : ℝ) (x₀ : E)
    (hT : t₀ < T)
    (hf : ContDiff ℝ 2 (Function.uncurry f))
    (x : ℝ → E) (hx0 : x t₀ = x₀)
    (hx : ∀ t ∈ Set.Icc t₀ T, HasDerivAt x (f t (x t)) t) :
    ∃ C : ℝ, ∀ h ∈ Set.Ioc 0 (T - t₀), ∀ t ∈ Set.Icc t₀ T, t + h ≤ T →
      ‖x (t + h) - (x t + h • f t (x t))‖ ≤ C * h ^ 2 := by
  obtain ⟨C, _, hC⟩ := ODE.exists_explicitEuler_localTruncationError_le f t₀ T hT hf x hx
  exact ⟨C, hC⟩

end MathlibExt.Analysis.ODE.ExplicitEulerWanted
