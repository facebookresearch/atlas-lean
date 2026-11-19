/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Epidemiology.NextGenerationMatrix
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MathlibExt.Analysis.ODE.MaximalSolution
import MathlibExt.Biology.Epidemiology.SIRAsymptotics
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The closed SEIR epidemic model

A closed population of size `N` (no births, deaths or migration) is split into susceptible `S`,
exposed (infected but not yet infectious) `E`, infectious `I` and removed `R` individuals. With
transmission rate `β`, rate `σ` of leaving the latent class (mean latent period `1 / σ`) and
removal rate `γ`, the SEIR model is

  `S' = -β S I / N`,   `E' = β S I / N - σ E`,   `I' = σ E - γ I`,   `R' = γ I`.

The epidemiological parameter domain is `β ≥ 0`, `σ, γ, N > 0`, with nonnegative compartments
summing to `N`. Each result states the hypotheses its proof needs; nonnegativity needs `N ≥ 0`
(so that the infection coefficient `β S / N` is nonnegative), which with Lean's `a / 0 = 0`
includes the degenerate `N = 0`.

## Main results

* `IsSolution β σ γ N S E I R` and `IsSolution.total_eq`: conservation of `S + E + I + R`.
* `IsSolution.deriv_exposed_add_infected_pos_iff`: the infected total grows initially,
  `(E + I)'(0) > 0`, iff `R₀ S(0) / N > 1`, `R₀ = β / γ` (for `I(0) > 0`); and
  `IsSolution.deriv_infected_pos_of_exposed`: a purely latent seed (`I(0) = 0 < E(0)`) gives
  `I'(0) = σ E(0) > 0`.
* `exists_isSolution_nonneg`, `exists_isSolution_simplex`, `IsSolution.eq_of_initial`:
  forward-global existence and uniqueness for nonnegative initial data, with nonnegative
  compartments of constant total (`N` on the simplex).
* `IsSolution.nonneg`, `IsSolution.susceptible_pos_iff`, `IsSolution.exposed_ge`,
  `IsSolution.infected_ge`: forward invariance, `S(t) > 0 ↔ S(0) > 0`,
  `E(t) ≥ E(0) e^{-σ t}`, `I(t) ≥ I(0) e^{-γ t}`. Positivity of the infected classes is not
  preserved compartment by compartment: `IsSolution.infected_pos_of_exposed_pos` (`E(0) > 0`
  forces `I(t) > 0` for `t > 0`, even if `I(0) = 0`) and
  `IsSolution.exposed_pos_of_infected_pos` (`S(0), I(0) > 0` force `E(t) > 0` for `t > 0`).
* `IsSolution.susceptible_mul_exp_eq`, `IsSolution.final_size`: `S e^{R₀ R / N}` is conserved,
  as for SIR, since `E` enters neither `S'` nor `R'`.
* `IsSolution.tendsto_final_size`: `S → S∞`, `E → 0`, `I → 0`, `R → R∞`, with
  `S∞ + R∞ = S(0) + E(0) + I(0) + R(0)` and the final-size relation
  `S∞ = S(0) e^{-R₀ (S(0) + E(0) + I(0) - S∞) / N}`; `IsSolution.final_size_eq_of_root`: for
  `E(0) + I(0) > 0` it determines `S∞`. The closed model has no endemic equilibrium.
* `newInfections`, `transfers`, `hasFDerivAt_newInfections`, `hasFDerivAt_transfers`,
  `hasFDerivAt_infectedField`: the next-generation splitting `ℱ - 𝒱` of the infected rates and
  its Jacobians `F = [[0, β], [0, 0]]`, `V = [[σ, 0], [-σ, γ]]` at the disease-free equilibrium.
* `R0_eq`, `R0_fderiv_eq`: `R₀ = ρ(F V⁻¹) = β / γ`; `isHurwitz_iff`, `exists_re_pos_iff`: the
  linearized threshold `β < γ` / `β > γ` for `F - V` (local spectral statements only).

## Proofs

`S` has the integrating-factor form `S(t) = S(0) e^{-∫₀ᵗ β I / N}`. The pair `(E, I)` is a
cooperative system, so integrating factors alone do not give `E, I ≥ 0`. Instead, perturbing both
by `ε e^{K t}`, with `K` above `β S / N` on `[0, T]`, gives a strict boundary condition, and a
continuous-induction argument (`IsClosed.Icc_subset_of_forall_mem_nhdsWithin`) keeps the
perturbed pair nonnegative; then `ε → 0`. Global existence follows the SIR pattern
(`SIR.exists_isSolution_nonneg`): the maximal solution of `ode_maximal_solution_exit_compact`
for the field `seirField` on `Fin 4 → ℝ` stays in the compact simplex, so it cannot leave every
compact set in finite forward time. For the limits, `S` and `S + E` (`(S + E)' = -σ E`) decrease
and `R` increases; a positive limit of `E` or `I` would make `S + E` or `R` unbounded.

## References

* H. W. Hethcote, *The mathematics of infectious diseases*, SIAM Review 42 (2000) 599–653.
* F. Brauer, *Compartmental models in epidemiology*, in *Mathematical Epidemiology*, Lecture
  Notes in Math. 1945, Springer (2008) 19–79.
* P. van den Driessche and J. Watmough, *Reproduction numbers and sub-threshold endemic
  equilibria for compartmental models of disease transmission*, Math. Biosci. 180 (2002)
  29–48.
-/

@[expose] public section

open Real Filter Set
open scoped Topology

namespace MathlibExt.Biology.Epidemiology.SEIR

/-- `(S, E, I, R)` solves the closed SEIR system with transmission rate `β`, rate `σ` of leaving
the latent class, removal rate `γ` and population size `N` for all times `t ≥ 0`:
`S' = -β S I / N`, `E' = β S I / N - σ E`, `I' = σ E - γ I`, `R' = γ I`. -/
structure IsSolution (β σ γ N : ℝ) (S E I R : ℝ → ℝ) : Prop where
  /-- Susceptibles are infected at rate `β S I / N`. -/
  hasDerivAt_susceptible : ∀ t, 0 ≤ t → HasDerivAt S (-(β * S t * I t / N)) t
  /-- Newly infected individuals enter the latent class, which they leave at rate `σ`. -/
  hasDerivAt_exposed : ∀ t, 0 ≤ t → HasDerivAt E (β * S t * I t / N - σ * E t) t
  /-- Latent individuals become infectious at rate `σ`; infectives are removed at rate `γ`. -/
  hasDerivAt_infected : ∀ t, 0 ≤ t → HasDerivAt I (σ * E t - γ * I t) t
  /-- Removed individuals accumulate at rate `γ I`. -/
  hasDerivAt_removed : ∀ t, 0 ≤ t → HasDerivAt R (γ * I t) t

/-- A function with zero derivative on `[0, ∞)` is constant there. -/
private theorem eq_zero_of_hasDerivAt {F : ℝ → ℝ} (hF : ∀ t, 0 ≤ t → HasDerivAt F 0 t)
    {t : ℝ} (ht : 0 ≤ t) : F t = F 0 :=
  constant_of_has_deriv_right_zero (b := t)
    (fun s hs => (hF s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hF s hs.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩

namespace IsSolution

variable {β σ γ N : ℝ} {S E I R : ℝ → ℝ}

/-- **Conservation of the population.** Along a solution, `S + E + I + R` is constant on
`[0, ∞)`. -/
theorem total_eq (h : IsSolution β σ γ N S E I R) {t : ℝ} (ht : 0 ≤ t) :
    S t + E t + I t + R t = S 0 + E 0 + I 0 + R 0 :=
  eq_zero_of_hasDerivAt (F := fun s => S s + E s + I s + R s) (fun s hs => by
    convert (((h.hasDerivAt_susceptible s hs).add (h.hasDerivAt_exposed s hs)).add
      (h.hasDerivAt_infected s hs)).add (h.hasDerivAt_removed s hs) using 1
    ring) ht

/-- **Infected subsystem.** The infected total `E + I` has derivative
`β S I / N - γ I = γ I (R₀ S / N - 1)` with `R₀ = β / γ` (`γ ≠ 0`, `N ≠ 0`): passing from `E`
to `I` does not change it. -/
theorem hasDerivAt_exposed_add_infected (h : IsSolution β σ γ N S E I R) (hγ : γ ≠ 0)
    (hN : N ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => E s + I s) (γ * I t * (β / γ * S t / N - 1)) t := by
  convert (h.hasDerivAt_exposed t ht).add (h.hasDerivAt_infected t ht) using 1
  field_simp
  ring

/-- **Threshold theorem.** If initially `I(0) > 0`, with `γ > 0` and `N > 0`, the infected
total `E + I` initially increases iff `R₀ S(0) / N > 1` with `R₀ = β / γ`. -/
theorem deriv_exposed_add_infected_pos_iff (h : IsSolution β σ γ N S E I R) (hγ : 0 < γ)
    (hN : 0 < N) (hI : 0 < I 0) :
    0 < deriv (fun s => E s + I s) 0 ↔ 1 < β / γ * S 0 / N := by
  rw [(h.hasDerivAt_exposed_add_infected hγ.ne' hN.ne' le_rfl).deriv,
    mul_pos_iff_of_pos_left (mul_pos hγ hI), sub_pos]

/-- **A latent seed becomes infectious.** If initially there are no infectives but `E(0) > 0`
(and `σ > 0`), the number of infectives initially increases: `I'(0) = σ E(0) > 0`. -/
theorem deriv_infected_pos_of_exposed (h : IsSolution β σ γ N S E I R) (hσ : 0 < σ)
    (hE : 0 < E 0) (hI : I 0 = 0) : 0 < deriv I 0 := by
  rw [(h.hasDerivAt_infected 0 le_rfl).deriv, hI, mul_zero, sub_zero]
  exact mul_pos hσ hE

/-- **Conserved quantity behind the final-size relation.** For `γ ≠ 0`, the quantity
`S(t) e^{R₀ R(t) / N}` (`R₀ = β / γ`) is constant along a solution on `[0, ∞)`, exactly as for
SIR: the latent class does not enter `S'` or `R'`. -/
theorem susceptible_mul_exp_eq (h : IsSolution β σ γ N S E I R) (hγ : γ ≠ 0) {t : ℝ}
    (ht : 0 ≤ t) :
    S t * exp (β / γ * R t / N) = S 0 * exp (β / γ * R 0 / N) :=
  eq_zero_of_hasDerivAt (F := fun s => S s * exp (β / γ * R s / N)) (fun s hs => by
    have hR := (((h.hasDerivAt_removed s hs).const_mul (β / γ)).div_const N).exp
    convert (h.hasDerivAt_susceptible s hs).mul hR using 1
    field_simp
    ring) ht

end IsSolution

/-! ### Forward invariance of the nonnegative orthant on `[0, T]` -/

/-- If `f` has a positive derivative at `x`, then `f x < f y` for all `y > x` close to `x`. -/
private theorem eventually_gt_of_hasDerivAt {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x)
    (hpos : 0 < f') : ∀ᶠ y in 𝓝[>] x, f x < f y := by
  have hs : ∀ᶠ y in 𝓝[>] x, 0 < slope f x y :=
    ((hasDerivAt_iff_tendsto_slope.1 hf).mono_left
      (nhdsWithin_mono _ fun y (hy : x < y) => hy.ne')).eventually (lt_mem_nhds hpos)
  filter_upwards [hs, self_mem_nhdsWithin] with y hy (hxy : x < y)
  rw [slope_def_field, div_pos_iff_of_pos_right (sub_pos.2 hxy)] at hy
  linarith

/-- **Strict boundary condition for a pair.** If `u` and `v` start nonnegative and, on
`[0, T)`, `u` has positive derivative whenever `u = 0 ≤ v` and `v` has positive derivative
whenever `v = 0 ≤ u`, then `u, v ≥ 0` on `[0, T]` (continuous induction). -/
private theorem nonneg_pair_of_hasDerivAt {u v u' v' : ℝ → ℝ} {T : ℝ}
    (hu : ∀ t ∈ Icc 0 T, HasDerivAt u (u' t) t) (hv : ∀ t ∈ Icc 0 T, HasDerivAt v (v' t) t)
    (hu0 : 0 ≤ u 0) (hv0 : 0 ≤ v 0)
    (hu' : ∀ t ∈ Ico 0 T, u t = 0 → 0 ≤ v t → 0 < u' t)
    (hv' : ∀ t ∈ Ico 0 T, v t = 0 → 0 ≤ u t → 0 < v' t) :
    ∀ t ∈ Icc 0 T, 0 ≤ u t ∧ 0 ≤ v t := by
  have hcont : ContinuousOn (fun t => (u t, v t)) (Icc 0 T) := fun t ht =>
    ((hu t ht).continuousAt.prodMk (hv t ht).continuousAt).continuousWithinAt
  have hclosed : IsClosed ({t : ℝ | 0 ≤ u t ∧ 0 ≤ v t} ∩ Icc 0 T) := by
    rw [inter_comm]
    exact hcont.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Ici.prod isClosed_Ici)
  have key : ∀ {w w' : ℝ → ℝ} {x : ℝ}, HasDerivAt w (w' x) x → 0 ≤ w x →
      (w x = 0 → 0 < w' x) → ∀ᶠ y in 𝓝[>] x, 0 ≤ w y := by
    intro w w' x hw hw0 hw'
    rcases hw0.eq_or_lt with h0 | hpos
    · exact (eventually_gt_of_hasDerivAt hw (hw' h0.symm)).mono fun y hy => h0 ▸ hy.le
    · exact ((hw.continuousAt.eventually (lt_mem_nhds hpos)).filter_mono
        nhdsWithin_le_nhds).mono fun y hy => hy.le
  intro t ht
  refine hclosed.Icc_subset_of_forall_mem_nhdsWithin ⟨hu0, hv0⟩
    (fun x ⟨⟨hux, hvx⟩, hx⟩ => ?_) ht
  have hxI : x ∈ Icc 0 T := Ico_subset_Icc_self hx
  exact (key (hu x hxI) hux fun h0 => hu' x hx h0 hvx).and
    (key (hv x hxI) hvx fun h0 => hv' x hx h0 hux)

section Forward

/-! The lemmas in this section only assume the SEIR equations, with two-sided derivatives, at
the times of `[0, T]`. They apply to solutions (`IsSolution`, with any `T`) and to the maximal
solution in the existence proof (with `T` in its interval of definition). -/

variable {β σ γ N : ℝ} {S E I R : ℝ → ℝ} {T : ℝ}
  (hd : ∀ t ∈ Icc 0 T, HasDerivAt S (-(β * S t * I t / N)) t ∧
    HasDerivAt E (β * S t * I t / N - σ * E t) t ∧ HasDerivAt I (σ * E t - γ * I t) t ∧
      HasDerivAt R (γ * I t) t)
include hd

private theorem continuousOn_S : ContinuousOn S (Icc 0 T) :=
  fun t ht => (hd t ht).1.continuousAt.continuousWithinAt

private theorem continuousOn_I : ContinuousOn I (Icc 0 T) :=
  fun t ht => (hd t ht).2.2.1.continuousAt.continuousWithinAt

/-- **Susceptibles, integrating-factor form.** `S(t) = S(0) e^{-∫₀ᵗ β I / N}` on `[0, T]`. -/
theorem susceptible_eq_mul_exp_of_hasDerivAt :
    ∀ t ∈ Icc 0 T, S t = S 0 * exp (∫ s in (0 : ℝ)..t, -(β * I s / N)) :=
  SIR.eq_mul_exp_integral_of_hasDerivAt (u := S) (g := fun s => -(β * I s / N))
    (by have := continuousOn_I hd; fun_prop) fun t ht => by
    convert (hd t ht).1 using 1
    ring

/-- **Conservation on `[0, T]`.** `S + E + I + R` is constant on `[0, T]`. -/
theorem total_eq_of_hasDerivAt :
    ∀ t ∈ Icc 0 T, S t + E t + I t + R t = S 0 + E 0 + I 0 + R 0 := by
  have hF : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => S s + E s + I s + R s) 0 t := fun t ht => by
    obtain ⟨h1, h2, h3, h4⟩ := hd t ht
    convert ((h1.add h2).add h3).add h4 using 1
    ring
  exact constant_of_has_deriv_right_zero (fun t ht => (hF t ht).continuousAt.continuousWithinAt)
    fun t ht => (hF t (Ico_subset_Icc_self ht)).hasDerivWithinAt

/-- The latent and infectious classes stay nonnegative on `[0, T]`. Proof: perturb both by
`ε e^{K t}` with `K` above the infection coefficient `β S / N` (bounded on `[0, T]`); the
perturbed pair satisfies a strict boundary condition (`nonneg_pair_of_hasDerivAt`), and
`ε → 0`. -/
private theorem exposed_infected_nonneg_of_hasDerivAt (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hγ : 0 ≤ γ)
    (hN : 0 ≤ N) (hS : 0 ≤ S 0) (hE : 0 ≤ E 0) (hI : 0 ≤ I 0) :
    ∀ t ∈ Icc 0 T, 0 ≤ E t ∧ 0 ≤ I t := by
  have hSnn : ∀ t ∈ Icc 0 T, 0 ≤ S t := fun t ht => by
    rw [susceptible_eq_mul_exp_of_hasDerivAt hd t ht]
    positivity
  have hc : ContinuousOn (fun t => β * S t / N) (Icc 0 T) := by
    have := continuousOn_S hd
    fun_prop
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  set K := |C| + σ + 1 with hK
  have hcK : ∀ t ∈ Icc 0 T, β * S t / N ≤ |C| := fun t ht =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hC t ht).trans (le_abs_self C))
  have hpert : ∀ ε > 0, ∀ t ∈ Icc 0 T,
      0 ≤ E t + ε * exp (K * t) ∧ 0 ≤ I t + ε * exp (K * t) := by
    intro ε hε
    have hexp : ∀ t, HasDerivAt (fun s => ε * exp (K * s)) (ε * exp (K * t) * K) t := fun t => by
      have := (((hasDerivAt_id' t).const_mul K).exp).const_mul ε
      convert this using 1
      ring
    refine nonneg_pair_of_hasDerivAt (fun t ht => (hd t ht).2.1.add (hexp t))
      (fun t ht => (hd t ht).2.2.1.add (hexp t)) (by positivity) (by positivity) ?_ ?_
    · intro t ht hu hv
      have ht' := Ico_subset_Icc_self ht
      have he : 0 < ε * exp (K * t) := by positivity
      have hc0 : 0 ≤ β * S t / N := by have := hSnn t ht'; positivity
      have h1 : β * S t / N * (-(ε * exp (K * t))) ≤ β * S t / N * I t :=
        mul_le_mul_of_nonneg_left (by linarith) hc0
      have h2 : β * S t * I t / N = β * S t / N * I t := by ring
      have h3 := mul_pos he (show 0 < K + σ - β * S t / N by linarith [hcK t ht', abs_nonneg C])
      nlinarith
    · intro t ht hv hu
      have he : 0 < ε * exp (K * t) := by positivity
      have h1 : σ * (-(ε * exp (K * t))) ≤ σ * E t := mul_le_mul_of_nonneg_left (by linarith) hσ
      have h3 := mul_pos he (show 0 < K - σ + γ by linarith [abs_nonneg C])
      nlinarith
  have hlim : ∀ {x : ℝ} {a : ℝ}, 0 < a → (∀ ε > 0, 0 ≤ x + ε * a) → 0 ≤ x := by
    intro x a ha h
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := h (ε / a) (div_pos hε ha)
    rwa [div_mul_cancel₀ _ ha.ne'] at this
  intro t ht
  exact ⟨hlim (exp_pos (K * t)) fun ε hε => (hpert ε hε t ht).1,
    hlim (exp_pos (K * t)) fun ε hε => (hpert ε hε t ht).2⟩

/-- **Forward nonnegativity on `[0, T]`.** For `β, σ, γ, N ≥ 0`, nonnegative initial
compartments stay nonnegative on `[0, T]`. (`N ≥ 0` matters: it makes the infection coefficient
`β S / N` nonnegative.) -/
theorem nonneg_of_hasDerivAt (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hγ : 0 ≤ γ) (hN : 0 ≤ N)
    (hS : 0 ≤ S 0) (hE : 0 ≤ E 0) (hI : 0 ≤ I 0) (hR : 0 ≤ R 0) :
    ∀ t ∈ Icc 0 T, 0 ≤ S t ∧ 0 ≤ E t ∧ 0 ≤ I t ∧ 0 ≤ R t := by
  have hEI := exposed_infected_nonneg_of_hasDerivAt hd hβ hσ hγ hN hS hE hI
  have hmono : MonotoneOn R (Icc 0 T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
      (fun t ht => (hd t ht).2.2.2.continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).2.2.2.hasDerivWithinAt)
      fun t ht => mul_nonneg hγ (hEI t (interior_subset ht)).2
  intro t ht
  refine ⟨?_, (hEI t ht).1, (hEI t ht).2, hR.trans (hmono ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1)⟩
  rw [susceptible_eq_mul_exp_of_hasDerivAt hd t ht]
  positivity

end Forward

/-- A function with derivative `f' t ≥ 0` at every `t > a` (and a derivative at every `t ≥ a`)
is monotone on `[a, ∞)`. -/
private theorem monotoneOn_Ici_of_hasDerivAt {f f' : ℝ → ℝ} {a : ℝ}
    (hf : ∀ t, a ≤ t → HasDerivAt f (f' t) t) (hf' : ∀ t, a < t → 0 ≤ f' t) :
    MonotoneOn f (Ici a) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a)
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hf t (interior_subset ht)).hasDerivWithinAt)
    fun t ht => hf' t (by rwa [interior_Ici] at ht)

/-- A function with derivative `f' t > 0` at every `t > 0` (and a derivative at every `t ≥ 0`)
is strictly monotone on `[0, ∞)`. -/
private theorem strictMonoOn_Ici_of_hasDerivAt {f f' : ℝ → ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivAt f (f' t) t) (hf' : ∀ t, 0 < t → 0 < f' t) :
    StrictMonoOn f (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici 0)
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt) fun t ht => by
      rw [interior_Ici] at ht
      rw [(hf t (le_of_lt ht)).deriv]
      exact hf' t ht

/-! ### Formulas along an arbitrary solution -/

namespace IsSolution

variable {β σ γ N : ℝ} {S E I R : ℝ → ℝ}

private theorem hasDerivAt_Icc (h : IsSolution β σ γ N S E I R) (T : ℝ) :
    ∀ t ∈ Icc 0 T, HasDerivAt S (-(β * S t * I t / N)) t ∧
      HasDerivAt E (β * S t * I t / N - σ * E t) t ∧ HasDerivAt I (σ * E t - γ * I t) t ∧
        HasDerivAt R (γ * I t) t :=
  fun t ht => ⟨h.hasDerivAt_susceptible t ht.1, h.hasDerivAt_exposed t ht.1,
    h.hasDerivAt_infected t ht.1, h.hasDerivAt_removed t ht.1⟩

/-- Along a solution, `S(t) = S(0) e^{-∫₀ᵗ β I / N}` for `t ≥ 0`. -/
theorem susceptible_eq_mul_exp (h : IsSolution β σ γ N S E I R) {t : ℝ} (ht : 0 ≤ t) :
    S t = S 0 * exp (∫ s in (0 : ℝ)..t, -(β * I s / N)) :=
  susceptible_eq_mul_exp_of_hasDerivAt (h.hasDerivAt_Icc t) t ⟨ht, le_rfl⟩

/-- Along a solution, `S(t) > 0` for `t ≥ 0` iff `S(0) > 0`. -/
theorem susceptible_pos_iff (h : IsSolution β σ γ N S E I R) {t : ℝ} (ht : 0 ≤ t) :
    0 < S t ↔ 0 < S 0 := by
  rw [h.susceptible_eq_mul_exp ht, mul_pos_iff_of_pos_right (exp_pos _)]

/-- Along a solution, `S(t) = 0` for `t ≥ 0` iff `S(0) = 0`. -/
theorem susceptible_eq_zero_iff (h : IsSolution β σ γ N S E I R) {t : ℝ} (ht : 0 ≤ t) :
    S t = 0 ↔ S 0 = 0 := by
  rw [h.susceptible_eq_mul_exp ht, mul_eq_zero, or_iff_left (exp_pos _).ne']

/-- **Forward invariance of the nonnegative orthant.** Along a solution with `β, σ, γ, N ≥ 0`
and nonnegative initial compartments, all compartments stay nonnegative for `t ≥ 0`. -/
theorem nonneg (h : IsSolution β σ γ N S E I R) (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hγ : 0 ≤ γ)
    (hN : 0 ≤ N) (hS : 0 ≤ S 0) (hE : 0 ≤ E 0) (hI : 0 ≤ I 0) (hR : 0 ≤ R 0) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ S t ∧ 0 ≤ E t ∧ 0 ≤ I t ∧ 0 ≤ R t :=
  nonneg_of_hasDerivAt (h.hasDerivAt_Icc t) hβ hσ hγ hN hS hE hI hR t ⟨ht, le_rfl⟩

/-- **Latent individuals leave no faster than at rate `σ`.** Under the hypotheses of `nonneg`,
`E(t) ≥ E(0) e^{-σ t}` for `t ≥ 0`: `E(t) e^{σ t}` is nondecreasing. -/
theorem exposed_ge (h : IsSolution β σ γ N S E I R) (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hγ : 0 ≤ γ)
    (hN : 0 ≤ N) (hS : 0 ≤ S 0) (hE : 0 ≤ E 0) (hI : 0 ≤ I 0) (hR : 0 ≤ R 0) {t : ℝ}
    (ht : 0 ≤ t) : E 0 * exp (-(σ * t)) ≤ E t := by
  have hm := monotoneOn_Ici_of_hasDerivAt (f := fun s => E s * exp (σ * s))
    (fun s hs => (h.hasDerivAt_exposed s hs).mul ((hasDerivAt_id' s).const_mul σ).exp)
    fun s hs => by
      obtain ⟨hSs, -, hIs, -⟩ := h.nonneg hβ hσ hγ hN hS hE hI hR hs.le
      have : 0 ≤ β * S s * I s / N * exp (σ * s) := by positivity
      linarith [show (β * S s * I s / N - σ * E s) * exp (σ * s) + E s * (exp (σ * s) * (σ * 1))
        = β * S s * I s / N * exp (σ * s) by ring]
  have := hm self_mem_Ici ht ht
  simp only [mul_zero, exp_zero, mul_one] at this
  rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _)]
  exact this

/-- **Infectives are removed no faster than at rate `γ`.** Under the hypotheses of `nonneg`,
`I(t) ≥ I(0) e^{-γ t}` for `t ≥ 0`: `I(t) e^{γ t}` is nondecreasing. -/
theorem infected_ge (h : IsSolution β σ γ N S E I R) (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hγ : 0 ≤ γ)
    (hN : 0 ≤ N) (hS : 0 ≤ S 0) (hE : 0 ≤ E 0) (hI : 0 ≤ I 0) (hR : 0 ≤ R 0) {t : ℝ}
    (ht : 0 ≤ t) : I 0 * exp (-(γ * t)) ≤ I t := by
  have hm := monotoneOn_Ici_of_hasDerivAt (f := fun s => I s * exp (γ * s))
    (fun s hs => (h.hasDerivAt_infected s hs).mul ((hasDerivAt_id' s).const_mul γ).exp)
    fun s hs => by
      obtain ⟨-, hEs, -, -⟩ := h.nonneg hβ hσ hγ hN hS hE hI hR hs.le
      have : 0 ≤ σ * E s * exp (γ * s) := by positivity
      linarith [show (σ * E s - γ * I s) * exp (γ * s) + I s * (exp (γ * s) * (γ * 1))
        = σ * E s * exp (γ * s) by ring]
  have := hm self_mem_Ici ht ht
  simp only [mul_zero, exp_zero, mul_one] at this
  rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _)]
  exact this

/-- **A latent seed makes the infectious class positive at once.** Under the hypotheses of
`nonneg`, if `σ > 0` and `E(0) > 0` then `I(t) > 0` for every `t > 0`, even when `I(0) = 0`. -/
theorem infected_pos_of_exposed_pos (h : IsSolution β σ γ N S E I R) (hβ : 0 ≤ β) (hσ : 0 < σ)
    (hγ : 0 ≤ γ) (hN : 0 ≤ N) (hS : 0 ≤ S 0) (hE : 0 < E 0) (hI : 0 ≤ I 0) (hR : 0 ≤ R 0)
    {t : ℝ} (ht : 0 < t) : 0 < I t := by
  have hm := strictMonoOn_Ici_of_hasDerivAt (f := fun s => I s * exp (γ * s))
    (fun s hs => (h.hasDerivAt_infected s hs).mul ((hasDerivAt_id' s).const_mul γ).exp)
    fun s hs => by
      have hEs := (h.exposed_ge hβ hσ.le hγ hN hS hE.le hI hR hs.le).trans_lt' (by positivity)
      have : 0 < σ * E s * exp (γ * s) := by positivity
      linarith [show (σ * E s - γ * I s) * exp (γ * s) + I s * (exp (γ * s) * (γ * 1))
        = σ * E s * exp (γ * s) by ring]
  have := hm self_mem_Ici ht.le ht
  simp only [mul_zero, exp_zero, mul_one] at this
  exact pos_of_mul_pos_left (hI.trans_lt this) (exp_pos _).le

/-- **An infectious seed makes the latent class positive at once.** Under the hypotheses of
`nonneg`, if `β > 0`, `N > 0`, `S(0) > 0` and `I(0) > 0`, then `E(t) > 0` for every `t > 0`,
even when `E(0) = 0`. -/
theorem exposed_pos_of_infected_pos (h : IsSolution β σ γ N S E I R) (hβ : 0 < β) (hσ : 0 ≤ σ)
    (hγ : 0 ≤ γ) (hN : 0 < N) (hS : 0 < S 0) (hE : 0 ≤ E 0) (hI : 0 < I 0) (hR : 0 ≤ R 0)
    {t : ℝ} (ht : 0 < t) : 0 < E t := by
  have hm := strictMonoOn_Ici_of_hasDerivAt (f := fun s => E s * exp (σ * s))
    (fun s hs => (h.hasDerivAt_exposed s hs).mul ((hasDerivAt_id' s).const_mul σ).exp)
    fun s hs => by
      have hIs := (h.infected_ge hβ.le hσ hγ hN.le hS.le hE hI.le hR hs.le).trans_lt'
        (by positivity)
      have hSs := (h.susceptible_pos_iff hs.le).2 hS
      have : 0 < β * S s * I s / N * exp (σ * s) := by positivity
      linarith [show (β * S s * I s / N - σ * E s) * exp (σ * s) + E s * (exp (σ * s) * (σ * 1))
        = β * S s * I s / N * exp (σ * s) by ring]
  have := hm self_mem_Ici ht.le ht
  simp only [mul_zero, exp_zero, mul_one] at this
  exact pos_of_mul_pos_left (hE.trans_lt this) (exp_pos _).le

end IsSolution

/-! ### The SEIR vector field -/

/-- The closed SEIR vector field on `Fin 4 → ℝ`, with coordinates `x 0 = S`, `x 1 = E`,
`x 2 = I`, `x 3 = R`: `S' = -β S I / N`, `E' = β S I / N - σ E`, `I' = σ E - γ I`,
`R' = γ I`. The field is autonomous; the time argument is ignored. -/
noncomputable def seirField (β σ γ N : ℝ) (_t : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-(β * x 0 * x 2 / N), β * x 0 * x 2 / N - σ * x 1, σ * x 1 - γ * x 2, γ * x 2]

/-- The packed curve has the field as two-sided derivative at `t` iff the four SEIR equations
hold at `t` with two-sided derivatives. -/
private theorem hasDerivAt_pack_iff {β σ γ N : ℝ} {S E I R : ℝ → ℝ} {t : ℝ} :
    HasDerivAt (fun s => ![S s, E s, I s, R s])
        (seirField β σ γ N t ![S t, E t, I t, R t]) t ↔
      HasDerivAt S (-(β * S t * I t / N)) t ∧ HasDerivAt E (β * S t * I t / N - σ * E t) t ∧
        HasDerivAt I (σ * E t - γ * I t) t ∧ HasDerivAt R (γ * I t) t := by
  rw [hasDerivAt_pi, Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_succ,
    Fin.forall_fin_succ]
  simp [seirField]

/-- The SEIR field is smooth in the state variable: its components are polynomials. -/
private theorem seirField_contDiff {β σ γ N : ℝ} {n : WithTop ℕ∞} (t : ℝ) :
    ContDiff ℝ n (seirField β σ γ N t) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · change ContDiff ℝ n fun x : Fin 4 → ℝ => -(β * x 0 * x 2 / N)
    fun_prop
  · change ContDiff ℝ n fun x : Fin 4 → ℝ => β * x 0 * x 2 / N - σ * x 1
    fun_prop
  · change ContDiff ℝ n fun x : Fin 4 → ℝ => σ * x 1 - γ * x 2
    fun_prop
  · change ContDiff ℝ n fun x : Fin 4 → ℝ => γ * x 2
    fun_prop

/-- The uncurried SEIR field satisfies the spacetime local Lipschitz hypothesis of
`ode_maximal_solution_exit_compact` on `U = univ`. -/
private theorem seirField_locallyLipschitz (β σ γ N : ℝ) (p : ℝ × (Fin 4 → ℝ)) :
    ∃ C : NNReal, ∃ s ∈ 𝓝 p, ∀ t : ℝ, ∀ x y : Fin 4 → ℝ,
      (t, x) ∈ s ∩ univ → (t, y) ∈ s ∩ univ →
        dist (Function.uncurry (seirField β σ γ N) (t, x))
          (Function.uncurry (seirField β σ γ N) (t, y)) ≤ C * dist x y := by
  obtain ⟨C, hC⟩ := ((seirField_contDiff (β := β) (σ := σ) (γ := γ) (N := N) (n := 1)
    0).contDiffOn (s := Metric.closedBall p.2 1)).exists_lipschitzOnWith one_ne_zero
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  refine ⟨C, univ ×ˢ Metric.closedBall p.2 1,
    prod_mem_nhds univ_mem (Metric.closedBall_mem_nhds _ one_pos), ?_⟩
  rintro t x y ⟨⟨-, hx⟩, -⟩ ⟨⟨-, hy⟩, -⟩
  exact hC.dist_le_mul x hx y hy

/-- The simplex `{x ≥ 0, x 0 + x 1 + x 2 + x 3 = P}` is compact. -/
private theorem isCompact_seirSimplex (P : ℝ) :
    IsCompact {x : Fin 4 → ℝ | (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 + x 3 = P} := by
  refine (isCompact_Icc (a := (0 : Fin 4 → ℝ)) (b := fun _ => P)).of_isClosed_subset ?_ ?_
  · exact (isClosed_Ici (a := (0 : Fin 4 → ℝ))).inter (isClosed_eq (by fun_prop) continuous_const)
  · rintro x ⟨hx, hsum⟩
    refine ⟨hx, fun i => ?_⟩
    have := hx 0; have := hx 1; have := hx 2; have := hx 3
    fin_cases i <;> simp <;> linarith

/-! ### Forward-global existence and uniqueness -/

/-- **Forward-global nonnegative SEIR solutions.** For `β, σ, γ, N ≥ 0` and every nonnegative
initial state `(S₀, E₀, I₀, R₀)`, the SEIR system has a solution with these initial values,
with two-sided derivatives at every `t ≥ 0`, whose compartments stay nonnegative and keep the
total `S₀ + E₀ + I₀ + R₀` for all `t ≥ 0`. The epidemiological domain `β ≥ 0`, `σ, γ, N > 0`,
`S₀ + E₀ + I₀ + R₀ = N` is a special case (`exists_isSolution_simplex`); uniqueness is
`IsSolution.eq_of_initial`.

Proof: the maximal solution of `ode_maximal_solution_exit_compact` (`U = univ`, `t₀ = 0`) stays,
over `[0, T]` inside its interval `J`, in the compact set `[0, T] ×ˢ simplex`
(`nonneg_of_hasDerivAt`, `total_eq_of_hasDerivAt`); if some `T ≥ 0` were not in `J`, the time
`max c 0` would contradict the forward exit from that compact set. -/
theorem exists_isSolution_nonneg {β σ γ N : ℝ} (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hγ : 0 ≤ γ)
    (hN : 0 ≤ N) {S₀ E₀ I₀ R₀ : ℝ} (hS₀ : 0 ≤ S₀) (hE₀ : 0 ≤ E₀) (hI₀ : 0 ≤ I₀)
    (hR₀ : 0 ≤ R₀) :
    ∃ S E I R : ℝ → ℝ, IsSolution β σ γ N S E I R ∧
      S 0 = S₀ ∧ E 0 = E₀ ∧ I 0 = I₀ ∧ R 0 = R₀ ∧
      (∀ t, 0 ≤ t → 0 ≤ S t ∧ 0 ≤ E t ∧ 0 ≤ I t ∧ 0 ≤ R t) ∧
      (∀ t, 0 ≤ t → S t + E t + I t + R t = S₀ + E₀ + I₀ + R₀) := by
  obtain ⟨J, α, hα0, hJo, h0J, hJc, hαd, hexit⟩ :=
    MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_maximal_solution_exit_compact univ
      (Function.uncurry (seirField β σ γ N)) 0 ![S₀, E₀, I₀, R₀] isOpen_univ trivial
      ((seirField_contDiff (β := β) (σ := σ) (γ := γ) (N := N) (n := 0) 0).continuous.comp
        continuous_snd).continuousOn
      fun p _ => seirField_locallyLipschitz β σ γ N p
  have hcomp : ∀ t ∈ J,
      HasDerivAt (α · 0) (-(β * α t 0 * α t 2 / N)) t ∧
        HasDerivAt (α · 1) (β * α t 0 * α t 2 / N - σ * α t 1) t ∧
          HasDerivAt (α · 2) (σ * α t 1 - γ * α t 2) t ∧ HasDerivAt (α · 3) (γ * α t 2) t := by
    intro t ht
    have hpack : (fun s => ![α s 0, α s 1, α s 2, α s 3]) = α := by
      funext s i
      fin_cases i <;> rfl
    have h := (hαd t ht).2
    rw [← hpack] at h
    exact hasDerivAt_pack_iff.1 h
  have hd : ∀ T ∈ J, ∀ t ∈ Icc 0 T,
      HasDerivAt (α · 0) (-(β * α t 0 * α t 2 / N)) t ∧
        HasDerivAt (α · 1) (β * α t 0 * α t 2 / N - σ * α t 1) t ∧
          HasDerivAt (α · 2) (σ * α t 1 - γ * α t 2) t ∧ HasDerivAt (α · 3) (γ * α t 2) t :=
    fun T hT t ht => hcomp t (hJc 0 h0J T hT ht)
  have hinit : α 0 0 = S₀ ∧ α 0 1 = E₀ ∧ α 0 2 = I₀ ∧ α 0 3 = R₀ := by simp [hα0]
  obtain ⟨hi0, hi1, hi2, hi3⟩ := hinit
  have hnn : ∀ T ∈ J, ∀ t ∈ Icc 0 T,
      0 ≤ α t 0 ∧ 0 ≤ α t 1 ∧ 0 ≤ α t 2 ∧ 0 ≤ α t 3 := fun T hT =>
    nonneg_of_hasDerivAt (hd T hT) hβ hσ hγ hN (hi0 ▸ hS₀) (hi1 ▸ hE₀) (hi2 ▸ hI₀)
      (hi3 ▸ hR₀)
  have htot : ∀ T ∈ J, ∀ t ∈ Icc 0 T,
      α t 0 + α t 1 + α t 2 + α t 3 = S₀ + E₀ + I₀ + R₀ := fun T hT t ht => by
    rw [total_eq_of_hasDerivAt (hd T hT) t ht, hi0, hi1, hi2, hi3]
  have hglobal : Ici 0 ⊆ J := by
    intro T hT0
    by_contra hTJ
    obtain ⟨⟨c, hcJ, hc⟩, -⟩ := hexit (Icc 0 T ×ˢ
      {x : Fin 4 → ℝ | (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 + x 3 = S₀ + E₀ + I₀ + R₀})
      (isCompact_Icc.prod (isCompact_seirSimplex _)) (subset_univ _)
    have htJ : max c 0 ∈ J := by rcases max_choice c 0 with h | h <;> rw [h] <;> assumption
    set t := max c 0
    have ht0 : 0 ≤ t := le_max_right _ _
    have htT : t ≤ T := by
      by_contra h
      exact hTJ (hJc 0 h0J t htJ ⟨hT0, (not_le.1 h).le⟩)
    refine hc t htJ (le_max_left _ _) ⟨⟨ht0, htT⟩, fun i => ?_, htot t htJ t ⟨ht0, le_rfl⟩⟩
    obtain ⟨h0, h1, h2, h3⟩ := hnn t htJ t ⟨ht0, le_rfl⟩
    fin_cases i <;> assumption
  have hsol : IsSolution β σ γ N (α · 0) (α · 1) (α · 2) (α · 3) :=
    ⟨fun t ht => (hcomp t (hglobal ht)).1, fun t ht => (hcomp t (hglobal ht)).2.1,
      fun t ht => (hcomp t (hglobal ht)).2.2.1, fun t ht => (hcomp t (hglobal ht)).2.2.2⟩
  exact ⟨(α · 0), (α · 1), (α · 2), (α · 3), hsol, hi0, hi1, hi2, hi3,
    fun t ht => hnn t (hglobal ht) t ⟨ht, le_rfl⟩, fun t ht => htot t (hglobal ht) t ⟨ht, le_rfl⟩⟩

/-- **Forward uniqueness.** Two solutions of the SEIR system (any real parameters) with the same
initial values agree at every time `t ≥ 0`.

Proof: on `[0, t]` both packed curves are continuous, hence lie in a common closed ball, on
which the `C¹` field is Lipschitz; apply Mathlib's `ODE_solution_unique_of_mem_Icc_right`. -/
theorem IsSolution.eq_of_initial {β σ γ N : ℝ} {S E I R S' E' I' R' : ℝ → ℝ}
    (h : IsSolution β σ γ N S E I R) (h' : IsSolution β σ γ N S' E' I' R') (hS : S 0 = S' 0)
    (hE : E 0 = E' 0) (hI : I 0 = I' 0) (hR : R 0 = R' 0) {t : ℝ} (ht : 0 ≤ t) :
    S t = S' t ∧ E t = E' t ∧ I t = I' t ∧ R t = R' t := by
  have hd : ∀ s, 0 ≤ s → HasDerivAt (fun s => ![S s, E s, I s, R s])
      (seirField β σ γ N s ![S s, E s, I s, R s]) s := fun s hs =>
    hasDerivAt_pack_iff.2 ⟨h.1 s hs, h.2 s hs, h.3 s hs, h.4 s hs⟩
  have hd' : ∀ s, 0 ≤ s → HasDerivAt (fun s => ![S' s, E' s, I' s, R' s])
      (seirField β σ γ N s ![S' s, E' s, I' s, R' s]) s := fun s hs =>
    hasDerivAt_pack_iff.2 ⟨h'.1 s hs, h'.2 s hs, h'.3 s hs, h'.4 s hs⟩
  have hc : ContinuousOn (fun s => ![S s, E s, I s, R s]) (Icc 0 t) :=
    fun s hs => (hd s hs.1).continuousAt.continuousWithinAt
  have hc' : ContinuousOn (fun s => ![S' s, E' s, I' s, R' s]) (Icc 0 t) :=
    fun s hs => (hd' s hs.1).continuousAt.continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hc'
  obtain ⟨K, hK⟩ := ((seirField_contDiff (β := β) (σ := σ) (γ := γ) (N := N) (n := 1)
    0).contDiffOn (s := Metric.closedBall 0 (max C₁ C₂))).exists_lipschitzOnWith one_ne_zero
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  have heq := ODE_solution_unique_of_mem_Icc_right
    (s := fun _ => Metric.closedBall 0 (max C₁ C₂))
    (fun _ _ => hK) hc (fun s hs => (hd s hs.1).hasDerivWithinAt)
    (fun s hs => mem_closedBall_zero_iff.2
      ((hC₁ s (Ico_subset_Icc_self hs)).trans (le_max_left _ _)))
    hc' (fun s hs => (hd' s hs.1).hasDerivWithinAt)
    (fun s hs => mem_closedBall_zero_iff.2
      ((hC₂ s (Ico_subset_Icc_self hs)).trans (le_max_right _ _)))
    (by simp [hS, hE, hI, hR]) ⟨ht, le_rfl⟩
  exact ⟨by simpa using congrFun heq 0, by simpa using congrFun heq 1,
    by simpa using congrFun heq 2, by simpa using congrFun heq 3⟩

/-- **Global solutions on the simplex.** For `β ≥ 0`, `σ, γ ≥ 0`, `N > 0` and nonnegative
initial compartments with `S₀ + E₀ + I₀ + R₀ = N`, the SEIR system has a solution with these
initial values whose compartments are nonnegative and sum to `N` for all `t ≥ 0`; it is unique
on `[0, ∞)` by `IsSolution.eq_of_initial`. -/
theorem exists_isSolution_simplex {β σ γ N : ℝ} (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hγ : 0 ≤ γ)
    (hN : 0 < N) {S₀ E₀ I₀ R₀ : ℝ} (hS₀ : 0 ≤ S₀) (hE₀ : 0 ≤ E₀) (hI₀ : 0 ≤ I₀)
    (hR₀ : 0 ≤ R₀) (hsum : S₀ + E₀ + I₀ + R₀ = N) :
    ∃ S E I R : ℝ → ℝ, IsSolution β σ γ N S E I R ∧
      S 0 = S₀ ∧ E 0 = E₀ ∧ I 0 = I₀ ∧ R 0 = R₀ ∧
      ∀ t, 0 ≤ t → 0 ≤ S t ∧ 0 ≤ E t ∧ 0 ≤ I t ∧ 0 ≤ R t ∧ S t + E t + I t + R t = N := by
  obtain ⟨S, E, I, R, h, h0, h1, h2, h3, hnn, htot⟩ :=
    exists_isSolution_nonneg hβ hσ hγ hN.le hS₀ hE₀ hI₀ hR₀
  exact ⟨S, E, I, R, h, h0, h1, h2, h3, fun t ht =>
    ⟨(hnn t ht).1, (hnn t ht).2.1, (hnn t ht).2.2.1, (hnn t ht).2.2.2, hsum ▸ htot t ht⟩⟩

/-! ### Long-time behaviour and final size -/

/-- If `g' = f` on `[0, ∞)`, `g` is bounded above and `f(t) → L ≥ 0`, then `L = 0`: otherwise
`g' ≥ L / 2` eventually and `g` would be unbounded. -/
private theorem limit_eq_zero_of_hasDerivAt {g f : ℝ → ℝ} {L B : ℝ}
    (hg : ∀ t, 0 ≤ t → HasDerivAt g (f t) t) (hf : Tendsto f atTop (𝓝 L)) (hL : 0 ≤ L)
    (hB : ∀ t, 0 ≤ t → g t ≤ B) : L = 0 := by
  by_contra hne
  have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hne)
  obtain ⟨t₁, ht₁⟩ := eventually_atTop.1 (hf.eventually_const_lt (half_lt_self hLpos))
  set a := max t₁ 0
  have hF := monotoneOn_Ici_of_hasDerivAt (f := fun t => g t - L / 2 * t)
    (f' := fun t => f t - L / 2) (a := a)
    (fun t ht => (hg t ((le_max_right t₁ 0).trans ht)).sub
      ((hasDerivAt_id t).const_mul (L / 2) |>.congr_deriv (mul_one _)))
    (fun t ht => by
      have := ht₁ t ((le_max_left _ _).trans ht.le)
      linarith)
  have hga := hB a (le_max_right _ _)
  set t := a + 2 * (B - g a + 1) / L
  have hat : a ≤ t := le_add_of_nonneg_right (by have : 0 ≤ B - g a + 1 := by linarith
                                                 positivity)
  have h1 := hF self_mem_Ici hat hat
  have h2 : L / 2 * (t - a) = B - g a + 1 := by
    simp only [t, add_sub_cancel_left]
    field_simp
  have h3 := hB t ((le_max_right _ _).trans hat)
  simp only at h1
  nlinarith

namespace IsSolution

variable {β σ γ N : ℝ} {S E I R : ℝ → ℝ}

/-- **Final-size relation.** If along a solution (`γ ≠ 0`) `S(t) → S∞` and `R(t) → R∞` as
`t → ∞`, then `S∞ = S(0) e^{-R₀ (R∞ - R(0)) / N}` with `R₀ = β / γ`. -/
theorem final_size (h : IsSolution β σ γ N S E I R) (hγ : γ ≠ 0) {Sinf Rinf : ℝ}
    (hS : Tendsto S atTop (𝓝 Sinf)) (hR : Tendsto R atTop (𝓝 Rinf)) :
    Sinf = S 0 * exp (-(β / γ * (Rinf - R 0) / N)) := by
  have hlim : Tendsto (fun t => S t * exp (β / γ * R t / N)) atTop
      (𝓝 (Sinf * exp (β / γ * Rinf / N))) :=
    hS.mul ((continuous_exp.tendsto _).comp ((hR.const_mul (β / γ)).div_const N))
  have hconst : Tendsto (fun t => S t * exp (β / γ * R t / N)) atTop
      (𝓝 (S 0 * exp (β / γ * R 0 / N))) :=
    tendsto_const_nhds.congr' (eventually_atTop.2 ⟨0, fun t ht =>
      (h.susceptible_mul_exp_eq hγ ht).symm⟩)
  have heq := tendsto_nhds_unique hlim hconst
  have hpos := exp_pos (β / γ * Rinf / N)
  rw [show -(β / γ * (Rinf - R 0) / N) = β / γ * R 0 / N - β / γ * Rinf / N by ring, exp_sub,
    ← mul_div_assoc, ← heq, mul_div_cancel_right₀ _ hpos.ne']

/-- **Limits and final size.** Along a solution with `β ≥ 0`, `σ, γ > 0`, `N ≥ 0` and
nonnegative initial compartments, `S(t) → S∞`, `E(t) → 0`, `I(t) → 0` and `R(t) → R∞` as
`t → ∞`, with `0 ≤ S∞ ≤ S(0)`, `S∞ + R∞ = S(0) + E(0) + I(0) + R(0)`, and the final-size relation
`S∞ = S(0) e^{-R₀ (S(0) + E(0) + I(0) - S∞) / N}` (`R₀ = β / γ`).

`S` and `S + E` decrease (`(S + E)' = -σ E`) and `R` increases, so all three converge; then
`E → 0` because `S + E ≥ 0` cannot decrease at a rate bounded away from `0`, and `I → 0`
because `R ≤ S(0) + E(0) + I(0) + R(0)` cannot increase at such a rate. -/
theorem tendsto_final_size (h : IsSolution β σ γ N S E I R) (hβ : 0 ≤ β) (hσ : 0 < σ)
    (hγ : 0 < γ) (hN : 0 ≤ N) (hS : 0 ≤ S 0) (hE : 0 ≤ E 0) (hI : 0 ≤ I 0) (hR : 0 ≤ R 0) :
    ∃ Sinf Rinf : ℝ, Tendsto S atTop (𝓝 Sinf) ∧ Tendsto E atTop (𝓝 0) ∧
      Tendsto I atTop (𝓝 0) ∧ Tendsto R atTop (𝓝 Rinf) ∧ 0 ≤ Sinf ∧ Sinf ≤ S 0 ∧
      Sinf + Rinf = S 0 + E 0 + I 0 + R 0 ∧
      Sinf = S 0 * exp (-(β / γ * (S 0 + E 0 + I 0 - Sinf) / N)) := by
  set P := S 0 + E 0 + I 0 + R 0 with hP
  have hnn := fun t (ht : 0 ≤ t) => h.nonneg hβ hσ.le hγ.le hN hS hE hI hR ht
  have hQd : ∀ t, 0 ≤ t → HasDerivAt (fun s => S s + E s) (-(σ * E t)) t := fun t ht => by
    convert (h.hasDerivAt_susceptible t ht).add (h.hasDerivAt_exposed t ht) using 1
    ring
  have hSanti : AntitoneOn S (Ici 0) := by
    have := monotoneOn_Ici_of_hasDerivAt (f := fun t => -S t)
      (fun t ht => (h.hasDerivAt_susceptible t ht).neg) (fun t ht => by
        obtain ⟨hSt, -, hIt, -⟩ := hnn t ht.le
        simp only [neg_neg]
        positivity)
    exact fun x hx y hy hxy => neg_le_neg_iff.1 (this hx hy hxy)
  have hQanti : AntitoneOn (fun t => S t + E t) (Ici 0) := by
    have := monotoneOn_Ici_of_hasDerivAt (f := fun t => -(S t + E t))
      (fun t ht => (hQd t ht).neg) (fun t ht => by
        have := (hnn t ht.le).2.1
        simp only [neg_neg]
        positivity)
    exact fun x hx y hy hxy => neg_le_neg_iff.1 (this hx hy hxy)
  have hRmono : MonotoneOn R (Ici 0) :=
    monotoneOn_Ici_of_hasDerivAt h.hasDerivAt_removed fun t ht =>
      mul_nonneg hγ.le (hnn t ht.le).2.2.1
  have hRle : ∀ t, 0 ≤ t → R t ≤ P := fun t ht => by
    have := h.total_eq ht
    have := hnn t ht
    linarith
  have hmax : ∀ t : ℝ, max t 0 ∈ Ici (0 : ℝ) := fun t => le_max_right t 0
  have hev : ∀ F : ℝ → ℝ, (fun t => F (max t 0)) =ᶠ[atTop] F :=
    fun F => eventually_atTop.2 ⟨0, fun t ht => by simp only [max_eq_left ht]⟩
  have hSlim : Tendsto S atTop (𝓝 (⨅ t, S (max t 0))) :=
    (tendsto_atTop_ciInf (f := fun t => S (max t 0))
      (fun a b hab => hSanti (hmax a) (hmax b) (max_le_max hab le_rfl))
      ⟨0, by rintro _ ⟨t, rfl⟩; exact (hnn _ (hmax t)).1⟩).congr' (hev S)
  have hQlim : Tendsto (fun t => S t + E t) atTop (𝓝 (⨅ t, (S (max t 0) + E (max t 0)))) :=
    (tendsto_atTop_ciInf (f := fun t => S (max t 0) + E (max t 0))
      (fun a b hab => hQanti (hmax a) (hmax b) (max_le_max hab le_rfl))
      ⟨0, by
        rintro _ ⟨t, rfl⟩
        have := hnn _ (hmax t)
        exact add_nonneg this.1 this.2.1⟩).congr' (hev fun t => S t + E t)
  have hRlim : Tendsto R atTop (𝓝 (⨆ t, R (max t 0))) :=
    (tendsto_atTop_ciSup (f := fun t => R (max t 0))
      (fun a b hab => hRmono (hmax a) (hmax b) (max_le_max hab le_rfl))
      ⟨P, by rintro _ ⟨t, rfl⟩; exact hRle _ (hmax t)⟩).congr' (hev R)
  set Sinf := ⨅ t, S (max t 0)
  set Qinf := ⨅ t, (S (max t 0) + E (max t 0))
  set Rinf := ⨆ t, R (max t 0)
  have hElim : Tendsto E atTop (𝓝 (Qinf - Sinf)) :=
    (hQlim.sub hSlim).congr fun t => by simp
  have hIlim : Tendsto I atTop (𝓝 (P - Qinf - Rinf)) :=
    ((tendsto_const_nhds.sub hQlim).sub hRlim).congr' (eventually_atTop.2 ⟨0, fun t ht => by
      have := h.total_eq ht
      linarith⟩)
  have hLE0 : 0 ≤ Qinf - Sinf :=
    ge_of_tendsto hElim (eventually_atTop.2 ⟨0, fun t ht => (hnn t ht).2.1⟩)
  have hLI0 : 0 ≤ P - Qinf - Rinf :=
    ge_of_tendsto hIlim (eventually_atTop.2 ⟨0, fun t ht => (hnn t ht).2.2.1⟩)
  have hLE : Qinf - Sinf = 0 := by
    have := limit_eq_zero_of_hasDerivAt (g := fun t => -(S t + E t)) (f := fun t => σ * E t)
      (B := 0) (fun t ht => by convert (hQd t ht).neg using 1; ring) (hElim.const_mul σ)
      (mul_nonneg hσ.le hLE0) (fun t ht => by
        have := hnn t ht
        simp only [neg_nonpos]
        linarith)
    exact (mul_eq_zero.1 this).resolve_left hσ.ne'
  have hLI : P - Qinf - Rinf = 0 := by
    have := limit_eq_zero_of_hasDerivAt (g := R) (f := fun t => γ * I t) h.hasDerivAt_removed
      (hIlim.const_mul γ) (mul_nonneg hγ.le hLI0) hRle
    exact (mul_eq_zero.1 this).resolve_left hγ.ne'
  refine ⟨Sinf, Rinf, hSlim, hLE ▸ hElim, hLI ▸ hIlim, hRlim,
    ge_of_tendsto hSlim (eventually_atTop.2 ⟨0, fun t ht => (hnn t ht).1⟩),
    le_of_tendsto hSlim (eventually_atTop.2 ⟨0, fun t ht => hSanti self_mem_Ici ht ht⟩),
    by linarith, ?_⟩
  have hfs := h.final_size hγ.ne' hSlim hRlim
  rwa [show Rinf - R 0 = S 0 + E 0 + I 0 - Sinf by linarith] at hfs

/-- **The final size is determined by the initial data.** Under the hypotheses of
`tendsto_final_size` with `N > 0` and a nonzero infected seed `E(0) + I(0) > 0`, the limit `S∞`
of `S` is the unique root `x ≤ S(0)` of the final-size equation
`x = S(0) e^{-R₀ (S(0) + E(0) + I(0) - x) / N}` (`R₀ = β / γ`). Via
`SIR.final_size_root_unique` with initial infected mass `E(0) + I(0)`. -/
theorem final_size_eq_of_root (h : IsSolution β σ γ N S E I R) (hβ : 0 ≤ β) (hσ : 0 < σ)
    (hγ : 0 < γ) (hN : 0 < N) (hS : 0 ≤ S 0) (hE : 0 ≤ E 0) (hI : 0 ≤ I 0) (hR : 0 ≤ R 0)
    (hEI : 0 < E 0 + I 0) {Sinf x : ℝ} (hSinf : Tendsto S atTop (𝓝 Sinf)) (hx : x ≤ S 0)
    (hxe : x = S 0 * exp (-(β / γ * (S 0 + E 0 + I 0 - x) / N))) : Sinf = x := by
  obtain ⟨S', -, hS', -, -, -, -, hle, -, hroot⟩ :=
    h.tendsto_final_size hβ hσ hγ hN.le hS hE hI hR
  rw [tendsto_nhds_unique hSinf hS']
  rw [add_assoc (S 0)] at hroot hxe
  exact SIR.final_size_root_unique hβ hγ hN hS hEI hle hx hroot hxe

end IsSolution

/-! ### The next-generation matrix at the disease-free equilibrium

SEIR has two infected compartments, `E` and `I`. In the convention of `NextGenerationMatrix`
(van den Driessche–Watmough), with infected coordinates `x 0 = E`, `x 1 = I`, the infected rates
`(E', I') = ℱ - 𝒱` split into new infections `ℱ = (β S I / N, 0)` (`newInfections`) and other
transfers `𝒱 = (σ E, -σ E + γ I)` (`transfers`). At the disease-free equilibrium `S = N`,
`E = I = 0`, their Jacobians in `(E, I)` are

  `F = [[0, β], [0, 0]]`,   `V = [[σ, 0], [-σ, γ]]`,

(`hasFDerivAt_newInfections`, needing `N ≠ 0`: for `N = 0`, Lean's `x / 0 = 0` makes `ℱ ≡ 0`;
`hasFDerivAt_transfers`), `F V⁻¹ = [[β / γ, β / γ], [0, 0]]` and `R₀ = ρ(F V⁻¹) = β / γ`
(`R0_eq`): the latent period delays infections but, with no deaths in the latent class, does not
change `R₀`.

The threshold statements `isHurwitz_iff`, `exists_re_pos_iff` are the **local, linearized**
ones for the infected block `F - V`. Theorem 2 of van den Driessche–Watmough
(`NextGenerationMatrix.globalSolution_decay_of_R0_lt_one`) does not apply to this closed model:
its uninfected block (`S`, `R`) of the Jacobian at a disease-free state is `0`, not Hurwitz,
because every `(S, 0, 0, R)` is an equilibrium. The long-time behaviour of the closed model is
`IsSolution.tendsto_final_size`: the epidemic always dies out, whatever `R₀`. -/

/-- The **new-infection rates** `ℱ(S; E, I) = (β S I / N, 0)` of the infected compartments
`(E, I)` (coordinates `x 0 = E`, `x 1 = I`), at susceptible level `S`. -/
noncomputable def newInfections (β N S : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![β * S * x 1 / N, 0]

/-- The **transfer rates** `𝒱(E, I) = (σ E, -σ E + γ I)` of the infected compartments
`(E, I)`: out of `E` at rate `σ E`, into `I` at rate `σ E`, out of `I` at rate `γ I`. -/
def transfers (σ γ : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![σ * x 0, -(σ * x 0) + γ * x 1]

/-- The infected components of the SEIR field are `ℱ - 𝒱`: for the state
`(S, E, I, R) = (x 0, x 1, x 2, x 3)`, `E' = ℱ₀ - 𝒱₀` and `I' = ℱ₁ - 𝒱₁`. -/
theorem seirField_infected_eq (β σ γ N t : ℝ) (x : Fin 4 → ℝ) :
    seirField β σ γ N t x 1 = newInfections β N (x 0) ![x 1, x 2] 0 - transfers σ γ ![x 1, x 2] 0 ∧
      seirField β σ γ N t x 2 =
        newInfections β N (x 0) ![x 1, x 2] 1 - transfers σ γ ![x 1, x 2] 1 := by
  simp only [seirField, newInfections, transfers]
  refine ⟨by simp, by simp; ring⟩

/-- **`F` is the Jacobian of `ℱ` at the disease-free equilibrium.** With `S = N` held at its
disease-free value, `ℱ` has derivative `F = [[0, β], [0, 0]]` in `(E, I)` at `E = I = 0`
(`N ≠ 0`). -/
theorem hasFDerivAt_newInfections {β N : ℝ} (hN : N ≠ 0) :
    HasFDerivAt (newInfections β N N)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' !![0, β; 0, 0])) 0 := by
  have : newInfections β N N =
      ⇑(LinearMap.toContinuousLinearMap (Matrix.toLin' !![(0 : ℝ), β; 0, 0])) := by
    funext x i
    fin_cases i
    · simp [newInfections, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp
    · simp [newInfections, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [this]
  exact ContinuousLinearMap.hasFDerivAt _

/-- **`V` is the Jacobian of `𝒱`.** `𝒱` is linear with matrix `V = [[σ, 0], [-σ, γ]]`. -/
theorem hasFDerivAt_transfers (σ γ : ℝ) :
    HasFDerivAt (transfers σ γ)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' !![σ, 0; -σ, γ])) 0 := by
  have : transfers σ γ =
      ⇑(LinearMap.toContinuousLinearMap (Matrix.toLin' !![σ, 0; -σ, γ])) := by
    funext x i
    fin_cases i <;> simp [transfers, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [this]
  exact ContinuousLinearMap.hasFDerivAt _

/-- **The infected-block Jacobian is `F - V`.** The SEIR infected rates `(E', I')` of
`seirField`, as functions of `(E, I)` with `S = N` (and any `R`), have derivative
`F - V = [[-σ, β], [σ, -γ]]` at `E = I = 0` (`N ≠ 0`). -/
theorem hasFDerivAt_infectedField {β σ γ N : ℝ} (t r : ℝ) (hN : N ≠ 0) :
    HasFDerivAt (fun x : Fin 2 → ℝ => ![seirField β σ γ N t ![N, x 0, x 1, r] 1,
        seirField β σ γ N t ![N, x 0, x 1, r] 2])
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (!![0, β; 0, 0] - !![σ, 0; -σ, γ]))) 0 := by
  have : (fun x : Fin 2 → ℝ => ![seirField β σ γ N t ![N, x 0, x 1, r] 1,
      seirField β σ γ N t ![N, x 0, x 1, r] 2]) =
      fun x => newInfections β N N x - transfers σ γ x := by
    funext x i
    fin_cases i
    · simp [seirField, newInfections, transfers]
    · simp [seirField, newInfections, transfers]
      ring
  rw [this, map_sub, map_sub]
  exact (hasFDerivAt_newInfections hN).sub (hasFDerivAt_transfers σ γ)

/-- The complex eigenvalues of a real `2 × 2` matrix are the roots of its characteristic
polynomial `(μ - M₀₀)(μ - M₁₁) - M₀₁ M₁₀`. -/
private theorem mem_spectrum_fin_two_iff {M : Matrix (Fin 2) (Fin 2) ℝ} {μ : ℂ} :
    μ ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)) ↔
      (μ - M 0 0) * (μ - M 1 1) - M 0 1 * M 1 0 = 0 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    Matrix.det_fin_two]
  simp [Matrix.algebraMap_matrix_apply]

/-- `F = [[0, β], [0, 0]]` is entrywise nonnegative for `β ≥ 0`. -/
theorem ngmF_nonneg {β : ℝ} (hβ : 0 ≤ β) (i j : Fin 2) :
    0 ≤ (!![0, β; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  fin_cases i <;> fin_cases j <;> simp [hβ]

/-- `V = [[σ, 0], [-σ, γ]]` is a nonsingular M-matrix for `σ, γ > 0`: its off-diagonal entries
are `≤ 0` and its eigenvalues `σ`, `γ` are positive. -/
theorem ngmV_isNonsingularMMatrix {σ γ : ℝ} (hσ : 0 < σ) (hγ : 0 < γ) :
    (!![σ, 0; -σ, γ] : Matrix (Fin 2) (Fin 2) ℝ).IsNonsingularMMatrix := by
  refine ⟨fun i j hij => ?_, fun μ hμ => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [hσ.le] at hij ⊢
  · rw [mem_spectrum_fin_two_iff] at hμ
    simp only [Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, neg_zero,
      Complex.ofReal_zero, Complex.ofReal_neg, zero_mul, sub_zero, sub_neg_eq_add] at hμ
    rcases mul_eq_zero.1 hμ with h | h
    · rw [eq_neg_of_add_eq_zero_left h]
      simpa using hσ
    · rw [eq_neg_of_add_eq_zero_left h]
      simpa using hγ

/-- `V⁻¹ = [[1 / σ, 0], [1 / γ, 1 / γ]]` for `σ, γ ≠ 0`. -/
private theorem ngmV_inv {σ γ : ℝ} (hσ : σ ≠ 0) (hγ : γ ≠ 0) :
    (!![σ, 0; -σ, γ] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = !![σ⁻¹, 0; γ⁻¹, γ⁻¹] := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [hσ, hγ]

/-- **`R₀ = β / γ` for SEIR**: the spectral radius of the next-generation matrix
`F V⁻¹ = [[β / γ, β / γ], [0, 0]]`, whose eigenvalues are `β / γ` and `0` (`β ≥ 0`,
`σ, γ > 0`), with `F`, `V` the Jacobians of `hasFDerivAt_newInfections` and
`hasFDerivAt_transfers`. -/
theorem R0_eq {β σ γ : ℝ} (hβ : 0 ≤ β) (hσ : 0 < σ) (hγ : 0 < γ) :
    NextGenerationMatrix.R0 !![0, β; 0, 0] !![σ, 0; -σ, γ] = β / γ := by
  have hK : (!![0, β; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![σ, 0; -σ, γ]⁻¹ =
      !![β / γ, β / γ; 0, 0] := by
    rw [ngmV_inv hσ.ne' hγ.ne', Matrix.mul_fin_two]
    simp [div_eq_mul_inv]
  have hspec : spectrum ℂ ((!![β / γ, β / γ; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).map
      (algebraMap ℝ ℂ)) = {((β / γ : ℝ) : ℂ), 0} := by
    ext μ
    rw [mem_spectrum_fin_two_iff]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Complex.ofReal_zero, mul_zero, sub_zero,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [mul_eq_zero, sub_eq_zero, or_comm]
  rw [NextGenerationMatrix.R0, hK, spectralRadius, quasispectrum_eq_spectrum_union_zero, hspec,
    Set.union_singleton, Set.insert_eq_of_mem (by simp), iSup_insert, iSup_singleton]
  simp [abs_of_nonneg hβ, abs_of_pos hγ]

/-- **`R₀` from the derivatives.** With `F` and `V` the matrices of the derivatives at the
disease-free equilibrium of `ℱ` (at `S = N`) and `𝒱`, `R₀ = ρ(F V⁻¹) = β / γ` (`β ≥ 0`,
`σ, γ > 0`, `N ≠ 0`). -/
theorem R0_fderiv_eq {β σ γ N : ℝ} (hβ : 0 ≤ β) (hσ : 0 < σ) (hγ : 0 < γ) (hN : N ≠ 0) :
    NextGenerationMatrix.R0 (LinearMap.toMatrix' (fderiv ℝ (newInfections β N N) 0 :
        (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ))
      (LinearMap.toMatrix' (fderiv ℝ (transfers σ γ) 0 : (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ)) =
      β / γ := by
  rw [(hasFDerivAt_newInfections hN).fderiv, (hasFDerivAt_transfers σ γ).fderiv,
    LinearMap.coe_toContinuousLinearMap, LinearMap.coe_toContinuousLinearMap,
    LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLin']
  exact R0_eq hβ hσ hγ

/-- **Linearized threshold, stable side.** For `β ≥ 0`, `σ, γ > 0`, every eigenvalue of the
infected-block Jacobian `F - V` has negative real part iff `β < γ`, i.e. iff `R₀ < 1`
(`NextGenerationMatrix.isHurwitz_sub_iff_R0_lt_one` with `R0_eq`). This is the local spectral
statement only, not a stability theorem for the closed model. -/
theorem isHurwitz_iff {β σ γ : ℝ} (hβ : 0 ≤ β) (hσ : 0 < σ) (hγ : 0 < γ) :
    (!![0, β; 0, 0] - !![σ, 0; -σ, γ] : Matrix (Fin 2) (Fin 2) ℝ).IsHurwitz ↔ β < γ := by
  rw [NextGenerationMatrix.isHurwitz_sub_iff_R0_lt_one (ngmF_nonneg hβ)
    (ngmV_isNonsingularMMatrix hσ hγ), R0_eq hβ hσ hγ, div_lt_one hγ]

/-- **Linearized threshold, unstable side.** For `β ≥ 0`, `σ, γ > 0`, `F - V` has an eigenvalue
with positive real part iff `γ < β`, i.e. iff `R₀ > 1`
(`NextGenerationMatrix.exists_re_pos_iff_one_lt_R0` with `R0_eq`). This is the local spectral
statement only. -/
theorem exists_re_pos_iff {β σ γ : ℝ} (hβ : 0 ≤ β) (hσ : 0 < σ) (hγ : 0 < γ) :
    (∃ μ ∈ spectrum ℂ ((!![0, β; 0, 0] - !![σ, 0; -σ, γ] : Matrix (Fin 2) (Fin 2) ℝ).map
      (algebraMap ℝ ℂ)), 0 < μ.re) ↔ γ < β := by
  rw [NextGenerationMatrix.exists_re_pos_iff_one_lt_R0 (ngmF_nonneg hβ)
    (ngmV_isNonsingularMMatrix hσ hγ), R0_eq hβ hσ hγ, one_lt_div hγ]

end MathlibExt.Biology.Epidemiology.SEIR
