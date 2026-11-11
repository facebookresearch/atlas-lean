/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.ODEBridge
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MathlibExt.Analysis.ODE.MaximalSolution
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Global nonnegative solutions of the SIR system

For the Kermack–McKendrick system `S' = -β S I / N`, `I' = β S I / N - γ I`, `R' = γ I`
(`MathlibExt.Biology.Epidemiology.SIR.IsSolution`), this file proves that every nonnegative
initial state has a solution defined for all `t ≥ 0`, and that it stays nonnegative.

## Main results

* `exists_isSolution_nonneg`: for `γ ≥ 0` and nonnegative `(S₀, I₀, R₀)` there is a solution
  with these initial values whose compartments are nonnegative and keep their total for all
  `t ≥ 0`; `S` (resp. `I`) is positive at `t ≥ 0` iff `S₀ > 0` (resp. `I₀ > 0`).
* `IsSolution.susceptible_eq_mul_exp`, `IsSolution.infected_eq_mul_exp`,
  `IsSolution.removed_eq_add_integral`: `S(t) = S(0) e^{-∫₀ᵗ β I / N}`,
  `I(t) = I(0) e^{∫₀ᵗ (β S / N - γ)}`, `R(t) = R(0) + γ ∫₀ᵗ I`; hence `IsSolution.nonneg` and
  the positivity criteria `IsSolution.susceptible_pos_iff`, `IsSolution.infected_pos_iff`.

## Proof of global existence

`ode_maximal_solution_exit_compact` (with `U = univ`, `t₀ = 0`) gives a maximal solution on an
open interval `J ∋ 0` that eventually leaves every compact set at the right end of `J`. The
uncurried field satisfies its spacetime local Lipschitz hypothesis (`sirField_locallyLipschitz`)
because it is `C¹` and time independent. On `[0, T] ⊆ J` the integrating-factor formulas, which
only use the equations on `[0, T]`, keep the solution in the compact simplex
`{x ≥ 0, x 0 + x 1 + x 2 = S₀ + I₀ + R₀}` (`isCompact_sirSimplex`). If some `T ≥ 0` were not in
`J`, every forward time of `J` would be `< T`, so the forward graph would stay in
`[0, T] ×ˢ simplex`; the time `max c 0` then contradicts the exit statement.
-/

@[expose] public section

open Set Filter Metric Real
open scoped Topology

namespace MathlibExt.Biology.Epidemiology.SIR

variable {β γ N : ℝ} {S I R : ℝ → ℝ}

/-! ### Integrating factors on a forward interval -/

/-- **Integrating factor.** If `u' = g u` on `[0, T]` with `g` continuous there, then
`u(t) = u(0) e^{∫₀ᵗ g}` on `[0, T]`. -/
theorem eq_mul_exp_integral_of_hasDerivAt {u g : ℝ → ℝ} {T : ℝ}
    (hg : ContinuousOn g (Icc 0 T)) (hu : ∀ t ∈ Icc 0 T, HasDerivAt u (g t * u t) t) :
    ∀ t ∈ Icc 0 T, u t = u 0 * exp (∫ s in (0 : ℝ)..t, g s) := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  set g' : ℝ → ℝ := fun s => g (max 0 (min T s)) with hg'
  have hg'c : Continuous g' := hg.comp_continuous (by fun_prop)
    fun s => ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩
  have hg'eq : ∀ s ∈ Icc 0 T, g' s = g s := fun s hs => by
    simp only [hg', min_eq_right hs.2, max_eq_right hs.1]
  set G : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, g' s with hG
  have hGd : ∀ s, HasDerivAt G (g' s) s := fun s => (hg'c.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hFd : ∀ s ∈ Icc 0 T, HasDerivAt (fun s => u s * exp (-G s)) 0 s := fun s hs => by
    convert (hu s hs).mul ((hGd s).neg.exp) using 1
    rw [hg'eq s hs]
    ring
  have hconst := constant_of_has_deriv_right_zero (f := fun s => u s * exp (-G s))
    (fun s hs => (hFd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hFd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) t ht
  have hG0 : G 0 = 0 := intervalIntegral.integral_same
  have hGt : G t = ∫ s in (0 : ℝ)..t, g s := intervalIntegral.integral_congr fun s hs => by
    rw [uIcc_of_le ht.1] at hs
    exact hg'eq s ⟨hs.1, hs.2.trans ht.2⟩
  simp only [hG0, neg_zero, exp_zero, mul_one] at hconst
  rw [← hGt, ← hconst, mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]

section Forward

/-! ### Invariance on `[0, T]`

The lemmas in this section only assume the SIR equations, with two-sided derivatives, at the
times of `[0, T]`. They apply to solutions (`IsSolution`, with any `T`) and to the maximal
solution below (with `T` in its interval of definition). -/

variable {T : ℝ}
  (hd : ∀ t ∈ Icc 0 T, HasDerivAt S (-(β * S t * I t / N)) t ∧
    HasDerivAt I (β * S t * I t / N - γ * I t) t ∧ HasDerivAt R (γ * I t) t)
include hd

private theorem continuousOn_S : ContinuousOn S (Icc 0 T) :=
  fun t ht => (hd t ht).1.continuousAt.continuousWithinAt

private theorem continuousOn_I : ContinuousOn I (Icc 0 T) :=
  fun t ht => (hd t ht).2.1.continuousAt.continuousWithinAt

/-- **Susceptibles, integrating-factor form.** `S(t) = S(0) e^{-∫₀ᵗ β I / N}` on `[0, T]`. -/
theorem susceptible_eq_mul_exp_of_hasDerivAt :
    ∀ t ∈ Icc 0 T, S t = S 0 * exp (∫ s in (0 : ℝ)..t, -(β * I s / N)) :=
  eq_mul_exp_integral_of_hasDerivAt (by have := continuousOn_I hd; fun_prop) fun t ht => by
    convert (hd t ht).1 using 1
    ring

/-- **Infectives, integrating-factor form.** `I(t) = I(0) e^{∫₀ᵗ (β S / N - γ)}` on `[0, T]`. -/
theorem infected_eq_mul_exp_of_hasDerivAt :
    ∀ t ∈ Icc 0 T, I t = I 0 * exp (∫ s in (0 : ℝ)..t, (β * S s / N - γ)) :=
  eq_mul_exp_integral_of_hasDerivAt (by have := continuousOn_S hd; fun_prop) fun t ht => by
    convert (hd t ht).2.1 using 1
    ring

/-- **Removed, integral form.** `R(t) = R(0) + γ ∫₀ᵗ I` on `[0, T]`. -/
theorem removed_eq_add_integral_of_hasDerivAt :
    ∀ t ∈ Icc 0 T, R t = R 0 + γ * ∫ s in (0 : ℝ)..t, I s := by
  intro t ht
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := R) (f' := fun s => γ * I s)
    (fun s hs => (hd s (hsub hs)).2.2)
    (((continuousOn_I hd).mono hsub).const_smul γ).intervalIntegrable
  rw [intervalIntegral.integral_const_mul] at this
  linarith

/-- **Conservation on `[0, T]`.** `S + I + R` is constant on `[0, T]`. -/
theorem total_eq_of_hasDerivAt :
    ∀ t ∈ Icc 0 T, S t + I t + R t = S 0 + I 0 + R 0 := by
  have hF : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => S s + I s + R s) 0 t := fun t ht => by
    obtain ⟨h1, h2, h3⟩ := hd t ht
    convert (h1.add h2).add h3 using 1
    ring
  exact constant_of_has_deriv_right_zero (fun t ht => (hF t ht).continuousAt.continuousWithinAt)
    fun t ht => (hF t (Ico_subset_Icc_self ht)).hasDerivWithinAt

/-- **Forward nonnegativity on `[0, T]`.** Nonnegative initial compartments stay nonnegative
(for `γ ≥ 0`; the sign of `β` and `N` plays no role). -/
theorem nonneg_of_hasDerivAt (hγ : 0 ≤ γ) (hS : 0 ≤ S 0) (hI : 0 ≤ I 0) (hR : 0 ≤ R 0) :
    ∀ t ∈ Icc 0 T, 0 ≤ S t ∧ 0 ≤ I t ∧ 0 ≤ R t := by
  intro t ht
  have hIt : ∀ s ∈ Icc 0 T, 0 ≤ I s := fun s hs => by
    rw [infected_eq_mul_exp_of_hasDerivAt hd s hs]
    positivity
  refine ⟨?_, hIt t ht, ?_⟩
  · rw [susceptible_eq_mul_exp_of_hasDerivAt hd t ht]
    positivity
  · rw [removed_eq_add_integral_of_hasDerivAt hd t ht]
    have := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) ht.1 fun s hs =>
      hIt s ⟨hs.1, hs.2.trans ht.2⟩
    positivity

end Forward

/-! ### Formulas along an arbitrary solution -/

namespace IsSolution

private theorem hasDerivAt_Icc (h : IsSolution β γ N S I R) (T : ℝ) :
    ∀ t ∈ Icc 0 T, HasDerivAt S (-(β * S t * I t / N)) t ∧
      HasDerivAt I (β * S t * I t / N - γ * I t) t ∧ HasDerivAt R (γ * I t) t :=
  fun t ht => ⟨h.hasDerivAt_susceptible t ht.1, h.hasDerivAt_infected t ht.1,
    h.hasDerivAt_removed t ht.1⟩

/-- Along a solution, `S(t) = S(0) e^{-∫₀ᵗ β I / N}` for `t ≥ 0`. -/
theorem susceptible_eq_mul_exp (h : IsSolution β γ N S I R) {t : ℝ} (ht : 0 ≤ t) :
    S t = S 0 * exp (∫ s in (0 : ℝ)..t, -(β * I s / N)) :=
  susceptible_eq_mul_exp_of_hasDerivAt (h.hasDerivAt_Icc t) t ⟨ht, le_rfl⟩

/-- Along a solution, `I(t) = I(0) e^{∫₀ᵗ (β S / N - γ)}` for `t ≥ 0`. -/
theorem infected_eq_mul_exp (h : IsSolution β γ N S I R) {t : ℝ} (ht : 0 ≤ t) :
    I t = I 0 * exp (∫ s in (0 : ℝ)..t, (β * S s / N - γ)) :=
  infected_eq_mul_exp_of_hasDerivAt (h.hasDerivAt_Icc t) t ⟨ht, le_rfl⟩

/-- Along a solution, `R(t) = R(0) + γ ∫₀ᵗ I` for `t ≥ 0`. -/
theorem removed_eq_add_integral (h : IsSolution β γ N S I R) {t : ℝ} (ht : 0 ≤ t) :
    R t = R 0 + γ * ∫ s in (0 : ℝ)..t, I s :=
  removed_eq_add_integral_of_hasDerivAt (h.hasDerivAt_Icc t) t ⟨ht, le_rfl⟩

/-- **Forward invariance of the nonnegative orthant.** Along a solution with `γ ≥ 0` and
nonnegative initial compartments, all compartments stay nonnegative for `t ≥ 0`. -/
theorem nonneg (h : IsSolution β γ N S I R) (hγ : 0 ≤ γ) (hS : 0 ≤ S 0) (hI : 0 ≤ I 0)
    (hR : 0 ≤ R 0) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ S t ∧ 0 ≤ I t ∧ 0 ≤ R t :=
  nonneg_of_hasDerivAt (h.hasDerivAt_Icc t) hγ hS hI hR t ⟨ht, le_rfl⟩

/-- Along a solution, `S(t) > 0` for `t ≥ 0` iff `S(0) > 0`. -/
theorem susceptible_pos_iff (h : IsSolution β γ N S I R) {t : ℝ} (ht : 0 ≤ t) :
    0 < S t ↔ 0 < S 0 := by
  rw [h.susceptible_eq_mul_exp ht, mul_pos_iff_of_pos_right (exp_pos _)]

/-- Along a solution, `I(t) > 0` for `t ≥ 0` iff `I(0) > 0`. -/
theorem infected_pos_iff (h : IsSolution β γ N S I R) {t : ℝ} (ht : 0 ≤ t) :
    0 < I t ↔ 0 < I 0 := by
  rw [h.infected_eq_mul_exp ht, mul_pos_iff_of_pos_right (exp_pos _)]

/-- Along a solution, `S(t) = 0` for `t ≥ 0` iff `S(0) = 0`. -/
theorem susceptible_eq_zero_iff (h : IsSolution β γ N S I R) {t : ℝ} (ht : 0 ≤ t) :
    S t = 0 ↔ S 0 = 0 := by
  rw [h.susceptible_eq_mul_exp ht, mul_eq_zero, or_iff_left (exp_pos _).ne']

/-- Along a solution, `I(t) = 0` for `t ≥ 0` iff `I(0) = 0`. -/
theorem infected_eq_zero_iff (h : IsSolution β γ N S I R) {t : ℝ} (ht : 0 ≤ t) :
    I t = 0 ↔ I 0 = 0 := by
  rw [h.infected_eq_mul_exp ht, mul_eq_zero, or_iff_left (exp_pos _).ne']

end IsSolution

/-! ### Local Lipschitz bound and the compact simplex -/

/-- The uncurried SIR field satisfies the spacetime local Lipschitz hypothesis of
`ode_maximal_solution_exit_compact` on `U = univ`: near `p`, take the slab
`univ ×ˢ closedBall p.2 1`, on which the (`C¹`, time-independent) field is Lipschitz in the
state. -/
theorem sirField_locallyLipschitz (β γ N : ℝ) (p : ℝ × (Fin 3 → ℝ)) :
    ∃ C : NNReal, ∃ s ∈ 𝓝 p, ∀ t : ℝ, ∀ x y : Fin 3 → ℝ,
      (t, x) ∈ s ∩ univ → (t, y) ∈ s ∩ univ →
        dist (Function.uncurry (sirField β γ N) (t, x))
          (Function.uncurry (sirField β γ N) (t, y)) ≤ C * dist x y := by
  obtain ⟨C, hC⟩ := ((sirField_contDiff (β := β) (γ := γ) (N := N) (n := 1) 0).contDiffOn
    (s := closedBall p.2 1)).exists_lipschitzOnWith one_ne_zero (convex_closedBall _ _)
    (isCompact_closedBall _ _)
  refine ⟨C, univ ×ˢ closedBall p.2 1,
    prod_mem_nhds univ_mem (closedBall_mem_nhds _ one_pos), ?_⟩
  rintro t x y ⟨⟨-, hx⟩, -⟩ ⟨⟨-, hy⟩, -⟩
  exact hC.dist_le_mul x hx y hy

/-- The uncurried SIR field is continuous. -/
theorem continuous_uncurry_sirField (β γ N : ℝ) :
    Continuous (Function.uncurry (sirField β γ N)) :=
  (sirField_contDiff (β := β) (γ := γ) (N := N) (n := 0) 0).continuous.comp continuous_snd

/-- The simplex `{x | x ≥ 0, x 0 + x 1 + x 2 = N}` of states with total population `N` is
compact. -/
theorem isCompact_sirSimplex (N : ℝ) :
    IsCompact {x : Fin 3 → ℝ | (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 = N} := by
  refine (isCompact_Icc (a := (0 : Fin 3 → ℝ)) (b := fun _ => N)).of_isClosed_subset ?_ ?_
  · exact (isClosed_Ici (a := (0 : Fin 3 → ℝ))).inter (isClosed_eq (by fun_prop) continuous_const)
  · rintro x ⟨hx, hsum⟩
    refine ⟨hx, fun i => ?_⟩
    have := hx 0; have := hx 1; have := hx 2
    fin_cases i <;> simp <;> linarith

/-! ### Forward-global existence -/

/-- **Forward-global nonnegative SIR solutions.** For `γ ≥ 0` (any real `β`, `N`) and every
nonnegative initial state `(S₀, I₀, R₀)`, the SIR system has a solution with these initial values,
with two-sided derivatives at every `t ≥ 0`, whose compartments stay nonnegative and keep the
total `S₀ + I₀ + R₀` for all `t ≥ 0`, and along which `S` (resp. `I`) is positive at a time
`t ≥ 0` iff `S₀ > 0` (resp. `I₀ > 0`). The epidemiological domain `β ≥ 0`, `γ > 0`, `N > 0`,
`S₀ + I₀ + R₀ = N` is a special case.

Proof: the maximal solution of `ode_maximal_solution_exit_compact` (`U = univ`, `t₀ = 0`) stays,
over `[0, T] ∩ I`, in the compact set `[0, T] ×ˢ simplex`; if some `T ≥ 0` were not in its open
interval `I`, every forward time of `I` would be `< T`, and the time `max c 0` would contradict
the forward exit from that compact set. -/
theorem exists_isSolution_nonneg (hγ : 0 ≤ γ) {S₀ I₀ R₀ : ℝ} (hS₀ : 0 ≤ S₀) (hI₀ : 0 ≤ I₀)
    (hR₀ : 0 ≤ R₀) :
    ∃ S I R : ℝ → ℝ, IsSolution β γ N S I R ∧ S 0 = S₀ ∧ I 0 = I₀ ∧ R 0 = R₀ ∧
      (∀ t, 0 ≤ t → 0 ≤ S t ∧ 0 ≤ I t ∧ 0 ≤ R t) ∧
      (∀ t, 0 ≤ t → S t + I t + R t = S₀ + I₀ + R₀) ∧
      (∀ t, 0 ≤ t → (0 < S t ↔ 0 < S₀) ∧ (0 < I t ↔ 0 < I₀)) := by
  obtain ⟨J, α, hα0, hJo, h0J, hJc, hαd, hexit⟩ :=
    MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_maximal_solution_exit_compact univ
      (Function.uncurry (sirField β γ N)) 0 ![S₀, I₀, R₀] isOpen_univ trivial
      (continuous_uncurry_sirField β γ N).continuousOn
      fun p _ => sirField_locallyLipschitz β γ N p
  have hcurve : IsIntegralCurveOn α (sirField β γ N) J := fun t ht =>
    (hαd t ht).2.hasDerivWithinAt
  have hd : ∀ T ∈ J, ∀ t ∈ Icc 0 T,
      HasDerivAt (α · 0) (-(β * α t 0 * α t 1 / N)) t ∧
        HasDerivAt (α · 1) (β * α t 0 * α t 1 / N - γ * α t 1) t ∧
          HasDerivAt (α · 2) (γ * α t 1) t := fun T hT t ht => by
    have htJ : t ∈ J := hJc 0 h0J T hT ht
    obtain ⟨h1, h2, h3⟩ := hcurve.sir_hasDerivWithinAt htJ
    exact ⟨h1.hasDerivAt (hJo.mem_nhds htJ), h2.hasDerivAt (hJo.mem_nhds htJ),
      h3.hasDerivAt (hJo.mem_nhds htJ)⟩
  have hinit : α 0 0 = S₀ ∧ α 0 1 = I₀ ∧ α 0 2 = R₀ := by simp [hα0]
  have hnn : ∀ T ∈ J, ∀ t ∈ Icc 0 T, 0 ≤ α t 0 ∧ 0 ≤ α t 1 ∧ 0 ≤ α t 2 := fun T hT =>
    nonneg_of_hasDerivAt (hd T hT) hγ (hinit.1 ▸ hS₀) (hinit.2.1 ▸ hI₀) (hinit.2.2 ▸ hR₀)
  have hglobal : Ici 0 ⊆ J := by
    intro T hT0
    by_contra hTJ
    obtain ⟨⟨c, hcJ, hc⟩, -⟩ := hexit (Icc 0 T ×ˢ
      {x : Fin 3 → ℝ | (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 = S₀ + I₀ + R₀})
      (isCompact_Icc.prod (isCompact_sirSimplex _)) (subset_univ _)
    have htJ : max c 0 ∈ J := by rcases max_choice c 0 with h | h <;> rw [h] <;> assumption
    set t := max c 0
    have ht0 : 0 ≤ t := le_max_right _ _
    have htT : t ≤ T := by
      by_contra h
      exact hTJ (hJc 0 h0J t htJ ⟨hT0, (not_le.1 h).le⟩)
    refine hc t htJ (le_max_left _ _) ⟨⟨ht0, htT⟩, fun i => ?_, ?_⟩
    · obtain ⟨h0, h1, h2⟩ := hnn t htJ t ⟨ht0, le_rfl⟩
      fin_cases i <;> assumption
    · have := total_eq_of_hasDerivAt (hd t htJ) t ⟨ht0, le_rfl⟩
      rw [this, hinit.1, hinit.2.1, hinit.2.2]
  have hsol : IsSolution β γ N (α · 0) (α · 1) (α · 2) :=
    isSolution_of_isIntegralCurveOn hcurve hglobal (hJo.mem_nhds h0J)
  refine ⟨(α · 0), (α · 1), (α · 2), hsol, hinit.1, hinit.2.1, hinit.2.2,
    fun t ht => hnn t (hglobal ht) t ⟨ht, le_rfl⟩, fun t ht => ?_, fun t ht => ?_⟩
  · rw [hsol.total_eq ht, hinit.1, hinit.2.1, hinit.2.2]
  · rw [hsol.susceptible_pos_iff ht, hsol.infected_pos_iff ht, hinit.1, hinit.2.1]
    exact ⟨Iff.rfl, Iff.rfl⟩

end MathlibExt.Biology.Epidemiology.SIR
