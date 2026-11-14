/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.ComplexBalanced
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import MathlibExt.Probability.Distributions.ExponentialMoments

/-!
# Non-explosion of stochastic reaction networks: a Foster–Lyapunov criterion

A stochastic chemical reaction network (CRN) is a continuous-time Markov chain on the count
vectors `x : S → ℕ`: reaction `r` fires at rate `λ_r(x)` (its *propensity*) and moves the state
from `x` to `x - src r + prod r`. On the countable state space `ℕ^S` the chain may *explode*:
infinitely many reactions may fire in finite time (e.g. `2X → 3X` with propensity `x (x - 1)`).
This file proves the Foster–Lyapunov criterion for non-explosion: if a function `V ≥ 0` satisfies
the drift bound `L V ≤ a V + b` for the generator
`L V(x) = ∑_r λ_r(x) (V(x - src r + prod r) - V(x))`, and the total propensity is bounded on
each sublevel set `{V < m}`, then almost surely the jump times of the chain tend to `∞`
(finite-time blow-up has probability `0`).

## The chain

The chain is built by the jump chain / holding time construction (Norris 1997, §2.6), on a
countable state space `S` with exit rates `q : S → ℝ`, `q > 0`, and jump kernel `P : S → PMF S`.
The randomness is an i.i.d. sequence of steps `ω n = (ξ n, E n)` under `inputMeasure P`, where
`ξ n : S → S` has independent coordinates `ξ n x ∼ P x` and `E n` is an independent `Exp(1)`
clock. The jump chain is `Y 0 = x₀`, `Y (n + 1) = ξ n (Y n)` (Mathlib-extension
`ProbabilityTheory.ctmcJumpChain`, reused from the finite-state construction), the holding
times are `E n / q (Y n)` and the jump times are their partial sums. Self-loops of `P` are
allowed; for a CRN an absorbing state (total propensity `0`) is given the fictitious rate `1`
and the jump `x ↦ x`, which does not change the path.

## Main definitions

* `JumpHold.inputMeasure P`, `JumpHold.holdingTime`, `JumpHold.jumpTime`: the countable-state
  jump–hold chain.
* `StochasticCRN S ρ`: a reaction network (`ComplexBalanced.ReactionNetwork`) with propensities
  that vanish when a reaction lacks its reactants.
* `StochasticCRN.generator`: the generator `L V(x) = ∑_r λ_r(x) (V(jump r x) - V(x))`.

## Main results

* `JumpHold.lintegral_discountedStop_le`: under the one-step drift condition
  `q(x) · E[V(ξ x)] ≤ (q(x) + c) V(x)` (that is, `L V ≤ c V`), the stopped discounted process is a
  supermartingale: `E[e^{-c T_{n ∧ σ}} V(Y_{n ∧ σ})] ≤ V(x₀)` for the first entrance `σ` into any
  set `A`. With `A = ∅` this is the discounted moment bound
  `JumpHold.lintegral_exp_jumpTime_mul_le`.
* `JumpHold.measure_reach_le`: the probability of reaching `{V ≥ m}` by time `t` is at most
  `e^{c t} V(x₀) / m`.
* `JumpHold.ae_tendsto_jumpTime_atTop`: **non-explosion** of the generic chain.
* `JumpHold.lintegral_path_le`: the **fixed-time moment bound** `E[V(X_t)] ≤ e^{c t} V(x₀)`
  for the path `X` (`JumpHold.path`, identified with the jump chain by
  `JumpHold.path_eq_ctmcJumpChain`).
* `StochasticCRN.ae_tendsto_jumpTime_atTop`: **non-explosion of a stochastic CRN** under
  `L V ≤ a V + b` with total propensity bounded on sublevel sets of `V`;
  `StochasticCRN.ae_tendsto_jumpTime_atTop_of_coercive` replaces the last condition by
  `∑_s x_s ≤ V(x)`; `StochasticCRN.lintegral_path_le` is the fixed-time moment bound.

## Proof outline

The recursion on the first step and the independence of the first step from the rest
(`JumpHold.inputMeasure_map_first`) reduce the supermartingale bound to one step, where the
Laplace transform `E[e^{-c E / q}] = q / (q + c)` of the clock cancels the drift factor
`(q + c) / q`. On the event that the jump times stay below `t`, either the chain enters
`{V ≥ m}` (probability at most `e^{c t} V(x₀) / m` by Markov's inequality applied to the stopped
process) or it stays in `{V < m}`, where the rates are at most some `K`, so the jump times are at
least `(E 0 + ⋯ + E (n - 1)) / K → ∞` almost surely (strong law of large numbers). Letting
`m → ∞` gives probability `0`.

## References

* S. P. Meyn and R. L. Tweedie, *Stability of Markovian processes III: Foster–Lyapunov criteria
  for continuous-time processes*, Adv. Appl. Probab. 25 (1993), 518–548, Theorem 2.1
  (criterion (CD0): `L V ≤ c V` with `V` norm-like implies non-explosion).
* A. Gupta, C. Briat and M. Khammash, *A scalable computational framework for establishing
  long-term behavior of stochastic reaction networks*, PLoS Comput. Biol. 10 (2014), e1003669
  (non-explosivity of CRNs from `L V ≤ c₁ + c₂ V`).
* D. F. Anderson and T. G. Kurtz, *Stochastic Analysis of Biochemical Systems*, Springer, 2015,
  ch. 2–3 (propensities and the generator of a stochastic CRN).
* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §2.6–2.7.
-/

@[expose] public section

open Finset MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion

/-! ### The countable-state jump–hold chain -/

namespace JumpHold

variable {S : Type*}

section Measure

variable [MeasurableSpace S]

/-- The law of one step `(ξ, E)`: `ξ : S → S` has independent coordinates with `ξ x ∼ P x`, and
`E` is an independent exponential clock of rate `1`. -/
noncomputable def stepMeasure (P : S → PMF S) : Measure ((S → S) × ℝ) :=
  (Measure.infinitePi fun x => (P x).toMeasure).prod (expMeasure 1)

instance (P : S → PMF S) : IsProbabilityMeasure (stepMeasure P) := by
  have := isProbabilityMeasure_expMeasure (r := 1) one_pos
  unfold stepMeasure
  infer_instance

/-- The law of the i.i.d. step sequence `ω : ℕ → (S → S) × ℝ` driving the chain. -/
noncomputable def inputMeasure (P : S → PMF S) : Measure (ℕ → (S → S) × ℝ) :=
  Measure.infinitePi fun _ => stepMeasure P

instance (P : S → PMF S) : IsProbabilityMeasure (inputMeasure P) := by
  unfold inputMeasure
  infer_instance

end Measure

/-- The `n`-th holding time `E n / q (Y n)` of the chain started at `x`. -/
noncomputable def holdingTime (q : S → ℝ) (x : S) (ω : ℕ → (S → S) × ℝ) (n : ℕ) : ℝ :=
  (ω n).2 / q (ctmcJumpChain x ω n)

/-- The `n`-th jump time `T n = S 0 + ⋯ + S (n - 1)` of the chain started at `x`. -/
noncomputable def jumpTime (q : S → ℝ) (x : S) (ω : ℕ → (S → S) × ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, holdingTime q x ω k

/-- The jump chain one step later is the jump chain of the shifted steps started at `ξ 0 x`. -/
theorem ctmcJumpChain_succ_eq (x : S) (ω : ℕ → (S → S) × ℝ) (j : ℕ) :
    ctmcJumpChain x ω (j + 1) = ctmcJumpChain ((ω 0).1 x) (ctmcShift 1 ω) j := by
  rw [show ((ω 0).1 x) = ctmcJumpChain x ω 1 from rfl, ctmcJumpChain_shift, Nat.add_comm]

/-- First-step decomposition of the jump times. -/
theorem jumpTime_succ_eq (q : S → ℝ) (x : S) (ω : ℕ → (S → S) × ℝ) (j : ℕ) :
    jumpTime q x ω (j + 1) = (ω 0).2 / q x + jumpTime q ((ω 0).1 x) (ctmcShift 1 ω) j := by
  simp only [jumpTime, sum_range_succ', holdingTime, ctmcJumpChain_succ_eq]
  simp only [ctmcShift, Nat.add_comm 1, ctmcJumpChain, add_comm]

open scoped Classical in
/-- The **stopped discounted Lyapunov process** `e^{-c T_{n ∧ σ}} V(Y_{n ∧ σ})`, where `σ` is
the first entrance of the jump chain into `A`, defined by recursion on the first step. -/
noncomputable def discountedStop (q : S → ℝ) (V : S → ℝ≥0∞) (c : ℝ) (A : Set S) :
    ℕ → S → (ℕ → (S → S) × ℝ) → ℝ≥0∞
  | 0, x, _ => V x
  | n + 1, x, ω =>
    if x ∈ A then V x
    else ENNReal.ofReal (Real.exp (-(c * ((ω 0).2 / q x)))) *
      discountedStop q V c A n ((ω 0).1 x) (ctmcShift 1 ω)

variable {q : S → ℝ} {V : S → ℝ≥0∞} {c : ℝ} {A : Set S}

/-- Before the first entrance into `A`, the stopped process is `e^{-c T_n} V(Y_n)`. -/
theorem discountedStop_eq_of_forall_notMem (n : ℕ) :
    ∀ (x : S) (ω : ℕ → (S → S) × ℝ), (∀ j < n, ctmcJumpChain x ω j ∉ A) →
      discountedStop q V c A n x ω =
        ENNReal.ofReal (Real.exp (-(c * jumpTime q x ω n))) * V (ctmcJumpChain x ω n) := by
  induction n with
  | zero => intro x ω _; simp [discountedStop, jumpTime, ctmcJumpChain]
  | succ n ih =>
    intro x ω h
    have hx : x ∉ A := h 0 (Nat.succ_pos n)
    have h' : ∀ j < n, ctmcJumpChain ((ω 0).1 x) (ctmcShift 1 ω) j ∉ A := fun j hj => by
      rw [← ctmcJumpChain_succ_eq]; exact h (j + 1) (by omega)
    simp only [discountedStop, hx, ite_false, ih _ _ h', jumpTime_succ_eq,
      ctmcJumpChain_succ_eq, ← mul_assoc]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 3
    ring

/-- After the first entrance `k ≤ n` into `A`, the stopped process is frozen at
`e^{-c T_k} V(Y_k)`. -/
theorem discountedStop_eq_of_hit (n : ℕ) :
    ∀ (x : S) (ω : ℕ → (S → S) × ℝ) (k : ℕ), k ≤ n → (∀ j < k, ctmcJumpChain x ω j ∉ A) →
      ctmcJumpChain x ω k ∈ A →
      discountedStop q V c A n x ω =
        ENNReal.ofReal (Real.exp (-(c * jumpTime q x ω k))) * V (ctmcJumpChain x ω k) := by
  induction n with
  | zero =>
    intro x ω k hk _ _
    obtain rfl : k = 0 := by omega
    simp [discountedStop, jumpTime, ctmcJumpChain]
  | succ n ih =>
    intro x ω k hk hlt hA
    by_cases hx : x ∈ A
    · obtain rfl : k = 0 := by
        by_contra hk0
        exact hlt 0 (Nat.pos_of_ne_zero hk0) hx
      simp [discountedStop, hx, jumpTime, ctmcJumpChain]
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := by
        rcases k with _ | k
        · exact absurd hA hx
        · exact ⟨k, rfl⟩
      have hlt' : ∀ j < k, ctmcJumpChain ((ω 0).1 x) (ctmcShift 1 ω) j ∉ A := fun j hj => by
        rw [← ctmcJumpChain_succ_eq]; exact hlt (j + 1) (by omega)
      rw [ctmcJumpChain_succ_eq] at hA
      simp only [discountedStop, hx, ite_false, ih _ _ k (by omega) hlt' hA, jumpTime_succ_eq,
        ctmcJumpChain_succ_eq, ← mul_assoc]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 3
      ring

section Integral

variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] {P : S → PMF S}

omit [Countable S] [MeasurableSingletonClass S] in
/-- The first step and the remaining steps are independent, with the step law and the input
law respectively (`ctmc_map_first_infinitePi` for the step law `stepMeasure P`). -/
theorem inputMeasure_map_first (P : S → PMF S) :
    (inputMeasure P).map (fun ω => (ω 0, ctmcShift 1 ω)) =
      (stepMeasure P).prod (inputMeasure P) :=
  ctmc_map_first_infinitePi (stepMeasure P)

omit [Countable S] [MeasurableSingletonClass S] in
/-- The clock coordinate of the step law is `Exp(1)`. -/
theorem stepMeasure_map_snd (P : S → PMF S) : (stepMeasure P).map Prod.snd = expMeasure 1 := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  rw [stepMeasure, Measure.map_snd_prod, measure_univ, one_smul]

omit [Countable S] [MeasurableSingletonClass S] in
/-- The clock coordinates `E n` have law `Exp(1)` (`ctmc_map_clock_infinitePi` for the step law
`stepMeasure P`). -/
theorem inputMeasure_map_clock (P : S → PMF S) (k : ℕ) :
    (inputMeasure P).map (fun ω : ℕ → (S → S) × ℝ => (ω k).2) = expMeasure 1 :=
  ctmc_map_clock_infinitePi (stepMeasure P) (stepMeasure_map_snd P) k

/-- The Laplace transform of `Exp(1)`: `∫ e^{-a E} = 1 / (1 + a)` for `a ≥ 0`. -/
theorem lintegral_exp_neg_mul_expMeasure_one {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ e, ENNReal.ofReal (Real.exp (-(a * e))) ∂expMeasure 1 = ENNReal.ofReal (1 / (1 + a)) := by
  have hneg : -(1 + a) < 0 := by linarith
  have hfun : (fun x : ℝ => 1 * Real.exp (-(1 * x)) * Real.exp (-(a * x))) =
      fun x => Real.exp (-(1 + a) * x) := by
    funext x; rw [one_mul, one_mul, ← Real.exp_add]; ring_nf
  have hint : Integrable (fun e : ℝ => Real.exp (-(a * e))) (expMeasure 1) := by
    rw [integrable_expMeasure_iff one_pos, hfun]
    exact integrableOn_exp_mul_Ioi hneg 0
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun e => (Real.exp_pos _).le),
    integral_expMeasure_eq_setIntegral one_pos, hfun, integral_exp_mul_Ioi hneg]
  congr 1
  simp only [mul_zero, Real.exp_zero]
  field_simp

omit [Countable S] [MeasurableSingletonClass S] in
/-- The clocks are almost surely nonnegative. -/
theorem ae_clock_nonneg (P : S → PMF S) :
    ∀ᵐ ω ∂inputMeasure P, ∀ k, 0 ≤ (ω k).2 := by
  rw [ae_all_iff]
  intro k
  have h0 : expMeasure 1 (Set.Iio 0) = 0 := by
    rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
    refine (setLIntegral_congr_fun measurableSet_Iio fun x hx => gammaPDF_of_neg hx).trans ?_
    simp
  have hm : Measurable fun ω : ℕ → (S → S) × ℝ => (ω k).2 := (measurable_pi_apply k).snd
  have : (inputMeasure P) ((fun ω : ℕ → (S → S) × ℝ => (ω k).2) ⁻¹' Set.Iio 0) = 0 := by
    rw [← Measure.map_apply hm measurableSet_Iio, inputMeasure_map_clock, h0]
  rw [ae_iff]
  have hset : {ω : ℕ → (S → S) × ℝ | ¬ 0 ≤ (ω k).2} = (fun ω => (ω k).2) ⁻¹' Set.Iio 0 := by
    ext ω; simp
  rw [hset, this]

omit [Countable S] [MeasurableSingletonClass S] in
private lemma measurable_eval_first (x : S) :
    Measurable fun ω : ℕ → (S → S) × ℝ => (ω 0).1 x :=
  (measurable_pi_apply x).comp (measurable_pi_apply 0).fst

/-- The stopped discounted process is measurable in the steps. -/
theorem measurable_discountedStop (n : ℕ) :
    ∀ x : S, Measurable fun ω => discountedStop q V c A n x ω := by
  induction n with
  | zero => exact fun x => measurable_const
  | succ n ih =>
    intro x
    classical
    simp only [discountedStop]
    split_ifs
    · exact measurable_const
    · have hg : Measurable fun p : S × (ℕ → (S → S) × ℝ) => discountedStop q V c A n p.1 p.2 :=
        measurable_from_prod_countable_right fun y => ih y
      have hsh : Measurable (ctmcShift (ι := S) 1) :=
        Measurable.of_eval fun j => measurable_pi_apply (1 + j)
      refine Measurable.mul ?_ (hg.comp ((measurable_eval_first x).prodMk hsh))
      exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        ((((measurable_pi_apply 0).snd.div_const _).const_mul c).neg))

/-- **Supermartingale bound for the stopped discounted Lyapunov process.** If off `A` the
one-step drift condition `q(x) · E[V(ξ x)] ≤ (q(x) + c) V(x)` holds (for the generator
`L V(x) = q(x) (∑_y P x y V(y) - V(x))` this is `L V ≤ c V`), then
`E[e^{-c T_{n ∧ σ}} V(Y_{n ∧ σ})] ≤ V(x)` for every `n`, where `σ` is the first entrance into
`A`. -/
theorem lintegral_discountedStop_le (hq : ∀ x, 0 < q x) (hc : 0 ≤ c)
    (hdrift : ∀ x ∉ A, ENNReal.ofReal (q x) * ∫⁻ y, V y ∂(P x).toMeasure ≤
      ENNReal.ofReal (q x + c) * V x)
    (n : ℕ) (x : S) : ∫⁻ ω, discountedStop q V c A n x ω ∂inputMeasure P ≤ V x := by
  induction n generalizing x with
  | zero => simp [discountedStop]
  | succ n ih =>
    classical
    have := isProbabilityMeasure_expMeasure (r := 1) one_pos
    by_cases hx : x ∈ A
    · simp [discountedStop, hx]
    set g : ℝ → ℝ≥0∞ := fun e => ENNReal.ofReal (Real.exp (-(c * (e / q x)))) with hg_def
    set F : ((S → S) × ℝ) × (ℕ → (S → S) × ℝ) → ℝ≥0∞ :=
      fun p => g p.1.2 * discountedStop q V c A n (p.1.1 x) p.2 with hF_def
    have hgm : Measurable g := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((measurable_id.div_const _).const_mul c).neg))
    have hFm : Measurable F := by
      have hD : Measurable fun p : S × (ℕ → (S → S) × ℝ) => discountedStop q V c A n p.1 p.2 :=
        measurable_from_prod_countable_right fun y => measurable_discountedStop n y
      refine (hgm.comp (measurable_fst.snd)).mul (hD.comp (Measurable.prodMk ?_ measurable_snd))
      exact (measurable_pi_apply x).comp measurable_fst.fst
    have hmap : Measurable fun ω : ℕ → (S → S) × ℝ => (ω 0, ctmcShift 1 ω) :=
      (measurable_pi_apply 0).prodMk (Measurable.of_eval fun j => measurable_pi_apply (1 + j))
    have heq : ∫⁻ ω, discountedStop q V c A (n + 1) x ω ∂inputMeasure P =
        ∫⁻ p, F p ∂(stepMeasure P).prod (inputMeasure P) := by
      rw [← inputMeasure_map_first, lintegral_map hFm hmap]
      exact lintegral_congr fun ω => by simp [discountedStop, hx, F, g]
    rw [heq, lintegral_prod _ hFm.aemeasurable]
    have hstep : ∀ a : (S → S) × ℝ,
        ∫⁻ ω', F (a, ω') ∂inputMeasure P ≤ g a.2 * V (a.1 x) := by
      intro a
      simp only [F]
      rw [lintegral_const_mul _ (measurable_discountedStop n _)]
      exact mul_le_mul_right (ih _) _
    calc ∫⁻ a, ∫⁻ ω', F (a, ω') ∂inputMeasure P ∂stepMeasure P
        ≤ ∫⁻ a, V (a.1 x) * g a.2 ∂stepMeasure P :=
          lintegral_mono fun a => (hstep a).trans_eq (mul_comm _ _)
      _ = (∫⁻ f, V (f x) ∂Measure.infinitePi fun y => (P y).toMeasure) *
            ∫⁻ e, g e ∂expMeasure 1 :=
          lintegral_prod_mul (f := fun f : S → S => V (f x))
            ((measurable_of_countable V).comp
              (measurable_pi_apply x : Measurable fun f : S → S => f x)).aemeasurable
            hgm.aemeasurable
      _ = (∫⁻ y, V y ∂(P x).toMeasure) * ENNReal.ofReal (q x / (q x + c)) := by
          congr 1
          · rw [← Measure.infinitePi_map_eval (fun y => (P y).toMeasure) x,
              lintegral_map (measurable_of_countable V) (measurable_pi_apply x)]
          · have hqx := hq x
            have h := lintegral_exp_neg_mul_expMeasure_one (div_nonneg hc hqx.le)
            have hg' : g = fun e => ENNReal.ofReal (Real.exp (-(c / q x * e))) := by
              funext e; simp only [g]; ring_nf
            rw [hg', h]
            congr 1
            field_simp
      _ ≤ V x := by
          have hqc : 0 < q x + c := by linarith [hq x]
          rw [ENNReal.ofReal_div_of_pos hqc, ← mul_div_assoc,
            ENNReal.div_le_iff (by simpa using hqc) ENNReal.ofReal_ne_top,
            mul_comm (∫⁻ y, V y ∂(P x).toMeasure), mul_comm (V x)]
          exact hdrift x hx

/-- **Discounted moment bound** (`A = ∅`): under `L V ≤ c V`,
`E[e^{-c T_n} V(Y_n)] ≤ V(x)` for every `n`. -/
theorem lintegral_exp_jumpTime_mul_le (hq : ∀ x, 0 < q x) (hc : 0 ≤ c)
    (hdrift : ∀ x, ENNReal.ofReal (q x) * ∫⁻ y, V y ∂(P x).toMeasure ≤
      ENNReal.ofReal (q x + c) * V x)
    (n : ℕ) (x : S) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-(c * jumpTime q x ω n))) * V (ctmcJumpChain x ω n)
      ∂inputMeasure P ≤ V x := by
  have h := lintegral_discountedStop_le (A := ∅) (P := P) hq hc (fun x _ => hdrift x) n x
  refine le_of_eq_of_le (lintegral_congr fun ω => ?_) h
  exact (discountedStop_eq_of_forall_notMem n x ω fun j _ => Set.notMem_empty _).symm

/-- **Exit bound.** Under `L V ≤ c V` (one-step form), the probability that the chain started at
`x₀` reaches `{V ≥ m}` by time `t` is at most `e^{c t} V(x₀) / m`. The event is phrased with the
first entrance `k` into `{V ≥ m}`. -/
theorem measure_reach_le {V : S → ℝ≥0} (hq : ∀ x, 0 < q x) (hc : 0 ≤ c)
    (hdrift : ∀ x, ENNReal.ofReal (q x) * ∫⁻ y, (V y : ℝ≥0∞) ∂(P x).toMeasure ≤
      ENNReal.ofReal (q x + c) * V x)
    {m : ℝ≥0} (hm : 0 < m) (t : ℝ) (x₀ : S) :
    inputMeasure P {ω | ∃ k, m ≤ V (ctmcJumpChain x₀ ω k) ∧
        (∀ j < k, V (ctmcJumpChain x₀ ω j) < m) ∧ jumpTime q x₀ ω k ≤ t} ≤
      ENNReal.ofReal (Real.exp (c * t)) * V x₀ / m := by
  classical
  set A : Set S := {y | m ≤ V y}
  set C : ℕ → Set (ℕ → (S → S) × ℝ) := fun n => {ω | ∃ k ≤ n, m ≤ V (ctmcJumpChain x₀ ω k) ∧
    (∀ j < k, V (ctmcJumpChain x₀ ω j) < m) ∧ jumpTime q x₀ ω k ≤ t}
  have hU : {ω | ∃ k, m ≤ V (ctmcJumpChain x₀ ω k) ∧
      (∀ j < k, V (ctmcJumpChain x₀ ω j) < m) ∧ jumpTime q x₀ ω k ≤ t} = ⋃ n, C n := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, C]
    exact ⟨fun ⟨k, h⟩ => ⟨k, k, le_rfl, h⟩, fun ⟨_, k, _, h⟩ => ⟨k, h⟩⟩
  have hmono : Monotone C := fun a b hab ω ⟨k, hk, h⟩ => ⟨k, hk.trans hab, h⟩
  rw [hU, hmono.measure_iUnion]
  refine iSup_le fun n => ?_
  set ε : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(c * t))) * m
  have hε0 : ε ≠ 0 :=
    mul_ne_zero (by simp [Real.exp_pos]) (by simpa using hm.ne')
  have hεtop : ε ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  have hsub : C n ⊆ {ω | ε ≤ discountedStop q (fun y => (V y : ℝ≥0∞)) c A n x₀ ω} := by
    rintro ω ⟨k, hk, hmk, hlt, hT⟩
    simp only [Set.mem_ofPred_eq]
    rw [discountedStop_eq_of_hit n x₀ ω k hk (fun j hj => by simpa [A] using hlt j hj)
      (by simpa [A] using hmk)]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) (by exact_mod_cast hmk)
    exact neg_le_neg (mul_le_mul_of_nonneg_left hT hc)
  calc inputMeasure P (C n)
      ≤ inputMeasure P {ω | ε ≤ discountedStop q (fun y => (V y : ℝ≥0∞)) c A n x₀ ω} :=
        measure_mono hsub
    _ ≤ (∫⁻ ω, discountedStop q (fun y => (V y : ℝ≥0∞)) c A n x₀ ω ∂inputMeasure P) / ε :=
        meas_ge_le_lintegral_div (measurable_discountedStop n x₀).aemeasurable hε0 hεtop
    _ ≤ V x₀ / ε := by
        gcongr
        exact lintegral_discountedStop_le hq hc (fun x _ => hdrift x) n x₀
    _ = ENNReal.ofReal (Real.exp (c * t)) * V x₀ / m := by
        have hinv : (ENNReal.ofReal (Real.exp (-(c * t))))⁻¹ =
            ENNReal.ofReal (Real.exp (c * t)) := by
          rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg, neg_neg]
        simp only [ε, div_eq_mul_inv]
        rw [ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.ofReal_ne_top), hinv]
        ring

/-- **Non-explosion** (Foster–Lyapunov criterion; Meyn–Tweedie 1993, Theorem 2.1). Let `q > 0`
and let `V ≥ 0` satisfy the one-step drift condition `q(x) · E[V(ξ x)] ≤ (q(x) + c) V(x)`
(that is, `L V ≤ c V`) with `c ≥ 0`, and let the rates be bounded on each sublevel set
`{V < m}`. Then almost surely the jump times of the chain started at any `x₀` tend to `∞`. -/
theorem ae_tendsto_jumpTime_atTop {V : S → ℝ≥0} (hq : ∀ x, 0 < q x) (hc : 0 ≤ c)
    (hdrift : ∀ x, ENNReal.ofReal (q x) * ∫⁻ y, (V y : ℝ≥0∞) ∂(P x).toMeasure ≤
      ENNReal.ofReal (q x + c) * V x)
    (hbdd : ∀ m : ℝ≥0, ∃ K : ℝ, ∀ x, V x < m → q x ≤ K) (x₀ : S) :
    ∀ᵐ ω ∂inputMeasure P, Tendsto (jumpTime q x₀ ω) atTop atTop := by
  have hB : ∀ t : ℕ, inputMeasure P {ω | ∀ n, jumpTime q x₀ ω n ≤ t} = 0 := by
    intro t
    have hle : ∀ m : ℝ≥0, 0 < m → inputMeasure P {ω | ∀ n, jumpTime q x₀ ω n ≤ t} ≤
        ENNReal.ofReal (Real.exp (c * t)) * V x₀ / m := by
      intro m hm
      obtain ⟨K, hK⟩ := hbdd m
      refine (measure_mono_ae ?_).trans (measure_reach_le hq hc hdrift hm t x₀)
      filter_upwards [ae_clock_nonneg P,
        (ae_tendsto_sum_clock_infinitePi (stepMeasure P) (stepMeasure_map_snd P) :
          ∀ᵐ ω ∂inputMeasure P, Tendsto (fun n => ∑ k ∈ range n, (ω k).2) atTop atTop)]
        with ω hE hsum hBω'
      have hBω : ∀ n, jumpTime q x₀ ω n ≤ t := hBω'
      change ∃ k, m ≤ V (ctmcJumpChain x₀ ω k) ∧ (∀ j < k, V (ctmcJumpChain x₀ ω j) < m) ∧
        jumpTime q x₀ ω k ≤ t
      by_contra hno
      have hall : ∀ k, V (ctmcJumpChain x₀ ω k) < m := by
        intro k
        induction k using Nat.strong_induction_on with
        | _ k ih =>
          by_contra hk
          exact hno ⟨k, not_lt.mp hk, fun j hj => ih j hj, hBω k⟩
      have hK1 : (0 : ℝ) < max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
      have hlow : ∀ n, (∑ k ∈ range n, (ω k).2) / max K 1 ≤ jumpTime q x₀ ω n := by
        intro n
        rw [sum_div]
        refine sum_le_sum fun k _ => ?_
        exact div_le_div_of_nonneg_left (hE k) (hq _)
          ((hK _ (hall k)).trans (le_max_left _ _))
      have htend : Tendsto (jumpTime q x₀ ω) atTop atTop :=
        tendsto_atTop_mono hlow (hsum.atTop_div_const hK1)
      obtain ⟨n, hn⟩ := (htend.eventually_gt_atTop (t : ℝ)).exists
      exact absurd (hBω n) (not_le.mpr hn)
    refine le_antisymm ?_ zero_le
    have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (c * t)) * V x₀ * (n : ℝ≥0∞)⁻¹)
        atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
        (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top))
          (a := ENNReal.ofReal (Real.exp (c * t)) * V x₀)
      simpa using this
    refine ge_of_tendsto htend ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have := hle (n : ℝ≥0) (by exact_mod_cast hn)
    simpa [div_eq_mul_inv] using this
  have hae : ∀ᵐ ω ∂inputMeasure P, ∀ t : ℕ, ω ∉ {ω | ∀ n, jumpTime q x₀ ω n ≤ t} :=
    ae_all_iff.2 fun t => measure_eq_zero_iff_ae_notMem.1 (hB t)
  filter_upwards [hae, ae_clock_nonneg P] with ω hω hE
  have hmono : Monotone (jumpTime q x₀ ω) := monotone_nat_of_le_succ fun n => by
    simp only [jumpTime, sum_range_succ]
    exact le_add_of_nonneg_right (div_nonneg (hE n) (hq _).le)
  refine tendsto_atTop_atTop.2 fun b => ?_
  obtain ⟨n, hn⟩ : ∃ n, (⌈b⌉₊ : ℝ) < jumpTime q x₀ ω n := by
    have := hω ⌈b⌉₊
    simpa [not_forall, not_le] using this
  exact ⟨n, fun k hk => (Nat.le_ceil b).trans (hn.le.trans (hmono hk))⟩

/-! #### The path and a fixed-time moment bound -/

/-- The state at time `s` of the chain started at `x` and stopped after `n` jumps, by recursion
on the first step. -/
noncomputable def stateAt (q : S → ℝ) : ℕ → S → ℝ → (ℕ → (S → S) × ℝ) → S
  | 0, x, _, _ => x
  | n + 1, x, s, ω =>
    if s < (ω 0).2 / q x then x
    else stateAt q n ((ω 0).1 x) (s - (ω 0).2 / q x) (ctmcShift 1 ω)

omit [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- Once `s < T m`, running more jumps does not change the state at time `s`. -/
theorem stateAt_eq_of_lt (m : ℕ) :
    ∀ (n : ℕ) (x : S) (s : ℝ) (ω : ℕ → (S → S) × ℝ), 0 ≤ s → s < jumpTime q x ω m → m ≤ n →
      stateAt q n x s ω = stateAt q m x s ω := by
  induction m with
  | zero => intro n x s ω hs hlt _; simp [jumpTime] at hlt; linarith
  | succ m ih =>
    intro n x s ω hs hlt hmn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [stateAt]
    split_ifs with h
    · rfl
    · rw [jumpTime_succ_eq] at hlt
      exact ih n _ _ _ (by linarith [not_lt.mp h]) (by linarith) (by omega)

omit [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- With nonnegative clocks the jump times are nonnegative. -/
theorem jumpTime_nonneg (hq : ∀ x, 0 < q x) {ω : ℕ → (S → S) × ℝ} (hE : ∀ k, 0 ≤ (ω k).2)
    (x : S) (n : ℕ) : 0 ≤ jumpTime q x ω n :=
  sum_nonneg fun k _ => div_nonneg (hE k) (hq _).le

omit [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- With nonnegative clocks, if `T k ≤ s < T (k + 1)` and `k < n`, then the state at time `s`
is `Y k`. -/
theorem stateAt_eq_ctmcJumpChain (hq : ∀ x, 0 < q x) (n : ℕ) :
    ∀ (x : S) (s : ℝ) (ω : ℕ → (S → S) × ℝ) (k : ℕ), (∀ j, 0 ≤ (ω j).2) → k < n →
      jumpTime q x ω k ≤ s → s < jumpTime q x ω (k + 1) →
      stateAt q n x s ω = ctmcJumpChain x ω k := by
  induction n with
  | zero => intro x s ω k _ hk; omega
  | succ n ih =>
    intro x s ω k hE hk h₁ h₂
    have hE' : ∀ j, 0 ≤ (ctmcShift 1 ω j).2 := fun j => hE (1 + j)
    simp only [stateAt]
    split_ifs with h
    · rcases k with _ | k
      · rfl
      · rw [jumpTime_succ_eq] at h₁
        linarith [jumpTime_nonneg hq hE' ((ω 0).1 x) k]
    · rcases k with _ | k
      · rw [show jumpTime q x ω (0 + 1) = (ω 0).2 / q x by
          simp [jumpTime, holdingTime, ctmcJumpChain]] at h₂
        exact absurd h₂ h
      · rw [jumpTime_succ_eq] at h₁ h₂
        rw [ih _ _ _ k hE' (by omega) (by linarith) (by linarith), ctmcJumpChain_succ_eq]

open scoped Classical in
/-- The **path** `X s` of the chain started at `x`: the state at time `s` after enough jumps.
If `s` is at or after the explosion time (a null event under the hypotheses of
`ae_tendsto_jumpTime_atTop`), the value is the junk state `x`. -/
noncomputable def path (q : S → ℝ) (x : S) (ω : ℕ → (S → S) × ℝ) (s : ℝ) : S :=
  if h : ∃ n, s < jumpTime q x ω n then stateAt q (Nat.find h) x s ω else x

omit [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- If `0 ≤ s < T n`, the path at time `s` is the state at time `s` after `n` jumps. -/
theorem stateAt_eq_path {n : ℕ} {x : S} {ω : ℕ → (S → S) × ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hn : s < jumpTime q x ω n) : stateAt q n x s ω = path q x ω s := by
  classical
  have h : ∃ n, s < jumpTime q x ω n := ⟨n, hn⟩
  simp only [path, h, ↓reduceDIte]
  exact stateAt_eq_of_lt _ n x s ω hs (Nat.find_spec h) (Nat.find_min' h hn)

omit [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- With nonnegative clocks, `X s = Y k` for `T k ≤ s < T (k + 1)`. -/
theorem path_eq_ctmcJumpChain (hq : ∀ x, 0 < q x) {x : S} {ω : ℕ → (S → S) × ℝ}
    (hE : ∀ j, 0 ≤ (ω j).2) {s : ℝ} {k : ℕ} (h₁ : jumpTime q x ω k ≤ s)
    (h₂ : s < jumpTime q x ω (k + 1)) : path q x ω s = ctmcJumpChain x ω k := by
  rw [← stateAt_eq_path ((jumpTime_nonneg hq hE x k).trans h₁) h₂]
  exact stateAt_eq_ctmcJumpChain hq (k + 1) x s ω k hE (Nat.lt_succ_self k) h₁ h₂

/-- The state at time `s` after `n` jumps is jointly measurable in `s` and the steps. -/
theorem measurable_stateAt (n : ℕ) :
    ∀ x : S, Measurable fun p : ℝ × (ℕ → (S → S) × ℝ) => stateAt q n x p.1 p.2 := by
  induction n with
  | zero => exact fun x => measurable_const
  | succ n ih =>
    intro x
    have hg : Measurable fun z : S × (ℝ × (ℕ → (S → S) × ℝ)) => stateAt q n z.1 z.2.1 z.2.2 :=
      measurable_from_prod_countable_right fun y => ih y
    have hE : Measurable fun p : ℝ × (ℕ → (S → S) × ℝ) => (p.2 0).2 / q x :=
      (((measurable_pi_apply 0).comp measurable_snd).snd).div_const (q x)
    have hsh : Measurable (ctmcShift (ι := S) 1) :=
      Measurable.of_eval fun j => measurable_pi_apply (1 + j)
    change Measurable fun p : ℝ × (ℕ → (S → S) × ℝ) =>
      if p.1 < (p.2 0).2 / q x then x
      else stateAt q n ((p.2 0).1 x) (p.1 - (p.2 0).2 / q x) (ctmcShift 1 p.2)
    refine Measurable.ite (measurableSet_lt measurable_fst hE) measurable_const ?_
    exact hg.comp (((measurable_eval_first x).comp measurable_snd).prodMk
      ((measurable_fst.sub hE).prodMk (hsh.comp measurable_snd)))

private lemma integral_exp_neg_mul_interval {k s : ℝ} (hk : 0 < k) :
    ∫ u in (0 : ℝ)..s, Real.exp (-(k * u)) = (1 - Real.exp (-(k * s))) / k := by
  have hd : ∀ u ∈ Set.uIcc (0 : ℝ) s,
      HasDerivAt (fun u => -Real.exp (-(k * u)) / k) (Real.exp (-(k * u))) u := by
    intro u _
    have h1 : HasDerivAt (fun u => -(k * u)) (-k) u := by
      convert ((hasDerivAt_id u).const_mul k).neg using 1
      · funext v; simp
      · simp
    convert (h1.exp).neg.div_const k using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  ring

/-- One step of the fixed-time moment recursion, integrated against `Exp(1)`. -/
private lemma lintegral_expMeasure_ite {q c s A B : ℝ} (hq : 0 < q) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∫⁻ e, ENNReal.ofReal (if s < e / q then A else Real.exp (c * (s - e / q)) * B)
        ∂expMeasure 1 =
      ENNReal.ofReal (A * Real.exp (-(q * s)) +
        B * q / (q + c) * (Real.exp (c * s) - Real.exp (-(q * s)))) := by
  set g : ℝ → ℝ := fun e => if s < e / q then A else Real.exp (c * (s - e / q)) * B with hg
  set M : ℝ := max A (Real.exp (c * s) * B)
  have hgm : Measurable g := Measurable.ite (measurableSet_lt measurable_const
    (measurable_id.div_const _)) measurable_const (by fun_prop)
  have hg0 : ∀ e, 0 ≤ g e := fun e => by
    simp only [g]; split_ifs
    · exact hA
    · positivity
  have hgM : ∀ e, 0 ≤ e → g e ≤ M := fun e he => by
    simp only [g]; split_ifs
    · exact le_max_left _ _
    · refine le_trans ?_ (le_max_right _ _)
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hB
      have : 0 ≤ e / q := div_nonneg he hq.le
      nlinarith
  have hint : Integrable g (expMeasure 1) := by
    rw [integrable_expMeasure_iff one_pos]
    refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul M)
      (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hg0 x)), one_mul,
      mul_comm M, show Real.exp (-1 * x) = Real.exp (-(1 * x)) by ring_nf]
    exact mul_le_mul_of_nonneg_left (hgM x (le_of_lt hx)) (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hg0),
    integral_expMeasure_renewal hq hs hint (f := fun u => Real.exp (c * u) * B)
      (fun e _ => rfl)]
  congr 1
  have hfun : (fun u => Real.exp (-(q * u)) * (Real.exp (c * (s - u)) * B)) =
      fun u => (B * Real.exp (c * s)) * Real.exp (-((q + c) * u)) := by
    funext u
    rw [mul_comm B, mul_assoc, ← mul_assoc (Real.exp (-(q * u))), ← Real.exp_add,
      mul_comm (Real.exp (c * s)), mul_assoc, ← Real.exp_add]
    ring_nf
  rw [hfun, intervalIntegral.integral_const_mul,
    integral_exp_neg_mul_interval (by linarith : 0 < q + c)]
  have he : Real.exp (c * s) * Real.exp (-((q + c) * s)) = Real.exp (-(q * s)) := by
    rw [← Real.exp_add]; ring_nf
  have hqc : q + c ≠ 0 := by linarith
  rw [← he]
  field_simp

/-- **Fixed-time moment bound, stopped after `n` jumps.** Under `L V ≤ c V` (one-step form),
`E[V(X_s^{(n)})] ≤ e^{c s} V(x)` for every `s ≥ 0` and `n`, where `X^{(n)}` is the chain stopped
after `n` jumps. -/
theorem lintegral_stateAt_le {V : S → ℝ≥0} (hq : ∀ x, 0 < q x) (hc : 0 ≤ c)
    (hdrift : ∀ x, ENNReal.ofReal (q x) * ∫⁻ y, (V y : ℝ≥0∞) ∂(P x).toMeasure ≤
      ENNReal.ofReal (q x + c) * V x) (n : ℕ) :
    ∀ (x : S) {s : ℝ}, 0 ≤ s → ∫⁻ ω, (V (stateAt q n x s ω) : ℝ≥0∞) ∂inputMeasure P ≤
      ENNReal.ofReal (Real.exp (c * s)) * V x := by
  induction n with
  | zero =>
    intro x s hs
    simp only [stateAt, lintegral_const, measure_univ, mul_one]
    calc (V x : ℝ≥0∞) = 1 * V x := (one_mul _).symm
      _ ≤ _ := mul_le_mul_left (by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hc hs))) _
  | succ n ih =>
    intro x s hs
    have := isProbabilityMeasure_expMeasure (r := 1) one_pos
    have hqx := hq x
    have hVm : Measurable fun y : S => (V y : ℝ≥0∞) := measurable_of_countable _
    set F : ((S → S) × ℝ) × (ℕ → (S → S) × ℝ) → ℝ≥0∞ := fun p =>
      if s < p.1.2 / q x then (V x : ℝ≥0∞)
      else V (stateAt q n (p.1.1 x) (s - p.1.2 / q x) p.2) with hF
    have hFm : Measurable F := by
      have hg : Measurable fun z : S × (ℝ × (ℕ → (S → S) × ℝ)) =>
          stateAt q n z.1 z.2.1 z.2.2 :=
        measurable_from_prod_countable_right fun y => measurable_stateAt n y
      have hE : Measurable fun p : ((S → S) × ℝ) × (ℕ → (S → S) × ℝ) => p.1.2 / q x :=
        measurable_fst.snd.div_const _
      refine Measurable.ite (measurableSet_lt measurable_const hE) measurable_const ?_
      exact hVm.comp (hg.comp (((measurable_pi_apply x).comp measurable_fst.fst).prodMk
        ((measurable_const.sub hE).prodMk measurable_snd)))
    have hmap : Measurable fun ω : ℕ → (S → S) × ℝ => (ω 0, ctmcShift 1 ω) :=
      (measurable_pi_apply 0).prodMk (Measurable.of_eval fun j => measurable_pi_apply (1 + j))
    have heq : ∫⁻ ω, (V (stateAt q (n + 1) x s ω) : ℝ≥0∞) ∂inputMeasure P =
        ∫⁻ p, F p ∂(stepMeasure P).prod (inputMeasure P) := by
      rw [← inputMeasure_map_first, lintegral_map hFm hmap]
      refine lintegral_congr fun ω => ?_
      simp only [stateAt, F]
      split_ifs <;> rfl
    rw [heq, lintegral_prod _ hFm.aemeasurable]
    set G : (S → S) × ℝ → ℝ≥0∞ := fun a => if s < a.2 / q x then (V x : ℝ≥0∞)
      else ENNReal.ofReal (Real.exp (c * (s - a.2 / q x))) * V (a.1 x) with hG
    have hinner : ∀ a, ∫⁻ ω', F (a, ω') ∂inputMeasure P ≤ G a := by
      intro a
      simp only [F, G]
      split_ifs with h
      · simp
      · exact ih _ (by rw [sub_nonneg]; exact not_lt.mp h)
    refine (lintegral_mono hinner).trans ?_
    have hGm : Measurable G := by
      refine Measurable.ite (measurableSet_lt measurable_const (measurable_snd.div_const _))
        measurable_const ?_
      exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul
        (hVm.comp ((measurable_pi_apply x).comp measurable_fst))
    rw [stepMeasure, lintegral_prod_symm _ hGm.aemeasurable]
    have hPV : ∫⁻ f, (V (f x) : ℝ≥0∞) ∂Measure.infinitePi (fun y => (P y).toMeasure) =
        ∫⁻ y, (V y : ℝ≥0∞) ∂(P x).toMeasure := by
      rw [← Measure.infinitePi_map_eval (fun y => (P y).toMeasure) x,
        lintegral_map hVm (measurable_pi_apply x)]
    have hqc : 0 < q x + c := by linarith
    have hPVle : ∫⁻ y, (V y : ℝ≥0∞) ∂(P x).toMeasure ≤
        ENNReal.ofReal ((q x + c) / q x * V x) := by
      have h := hdrift x
      have hr : ENNReal.ofReal ((q x + c) / q x * V x) =
          ENNReal.ofReal (q x + c) * V x / ENNReal.ofReal (q x) := by
        rw [div_mul_eq_mul_div, ENNReal.ofReal_div_of_pos hqx, ENNReal.ofReal_mul hqc.le,
          ENNReal.ofReal_coe_nnreal]
      rw [hr, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hqx))
        (Or.inl ENNReal.ofReal_ne_top), mul_comm]
      exact h
    have hin2 : ∀ e, ∫⁻ f, G (f, e) ∂Measure.infinitePi (fun y => (P y).toMeasure) ≤
        ENNReal.ofReal (if s < e / q x then (V x : ℝ)
          else Real.exp (c * (s - e / q x)) * ((q x + c) / q x * V x)) := by
      intro e
      simp only [G]
      split_ifs with h
      · simp
      · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hPV,
          ENNReal.ofReal_mul (Real.exp_pos _).le]
        exact mul_le_mul_right hPVle _
    refine (lintegral_mono hin2).trans ?_
    rw [lintegral_expMeasure_ite hqx hc hs (NNReal.coe_nonneg (V x)) (by positivity),
      ← ENNReal.ofReal_coe_nnreal (p := V x), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    field_simp
    ring

/-- **Fixed-time moment bound** (Meyn–Tweedie 1993, Theorem 2.1(iii)). Under the
hypotheses of `ae_tendsto_jumpTime_atTop`, the path satisfies `E[V(X_t)] ≤ e^{c t} V(x₀)` for
every `t ≥ 0`. -/
theorem lintegral_path_le {V : S → ℝ≥0} (hq : ∀ x, 0 < q x) (hc : 0 ≤ c)
    (hdrift : ∀ x, ENNReal.ofReal (q x) * ∫⁻ y, (V y : ℝ≥0∞) ∂(P x).toMeasure ≤
      ENNReal.ofReal (q x + c) * V x)
    (hbdd : ∀ m : ℝ≥0, ∃ K : ℝ, ∀ x, V x < m → q x ≤ K) (x₀ : S) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (V (path q x₀ ω t) : ℝ≥0∞) ∂inputMeasure P ≤
      ENNReal.ofReal (Real.exp (c * t)) * V x₀ := by
  have hev : ∀ᵐ ω ∂inputMeasure P, (V (path q x₀ ω t) : ℝ≥0∞) =
      liminf (fun n => (V (stateAt q n x₀ t ω) : ℝ≥0∞)) atTop := by
    filter_upwards [ae_tendsto_jumpTime_atTop hq hc hdrift hbdd x₀] with ω hω
    have : ∀ᶠ n in atTop, (V (stateAt q n x₀ t ω) : ℝ≥0∞) = V (path q x₀ ω t) := by
      filter_upwards [hω.eventually_gt_atTop t] with n hn
      rw [stateAt_eq_path ht hn]
    rw [liminf_congr this, liminf_const]
  rw [lintegral_congr_ae hev]
  refine (lintegral_liminf_le' fun n => ?_).trans ?_
  · exact ((measurable_of_countable (fun y : S => (V y : ℝ≥0∞))).comp
      ((measurable_stateAt (q := q) n x₀).comp (measurable_const.prodMk measurable_id :
        Measurable fun ω : ℕ → (S → S) × ℝ => (t, ω)))).aemeasurable
  · exact liminf_le_of_frequently_le'
      (Frequently.of_forall fun n => lintegral_stateAt_le hq hc hdrift n x₀ ht)

end Integral

end JumpHold

/-! ### Stochastic reaction networks -/

/-- A **stochastic chemical reaction network** on the species `S` with reactions `ρ`: a reaction
network (source and product complexes) together with propensities `λ_r : ℕ^S → ℝ`, `λ_r ≥ 0`,
that vanish when the state lacks the reactants of `r` (as mass-action propensities
`κ_r ∏_s x_s! / (x_s - src_r s)!` do). Reaction `r` fires at rate `λ_r(x)` and moves the state
to `x - src r + prod r` (Anderson–Kurtz 2015, ch. 2). -/
structure StochasticCRN (S ρ : Type*) where
  /-- The underlying reaction network. -/
  network : ComplexBalanced.ReactionNetwork S ρ
  /-- The propensity `λ_r(x)` of reaction `r` at the state `x`. -/
  propensity : ρ → (S → ℕ) → ℝ
  propensity_nonneg : ∀ r x, 0 ≤ propensity r x
  propensity_eq_zero : ∀ r x, ¬ network.src r ≤ x → propensity r x = 0

namespace StochasticCRN

variable {S ρ : Type*} (N : StochasticCRN S ρ)

/-- The state after reaction `r` fires at `x`: `x - src r + prod r`. -/
def jump (r : ρ) (x : S → ℕ) : S → ℕ := x - N.network.src r + N.network.prod r

variable [Fintype ρ]

/-- The total propensity `λ(x) = ∑_r λ_r(x)`. -/
noncomputable def totalRate (x : S → ℕ) : ℝ := ∑ r, N.propensity r x

/-- The holding rate of the jump–hold chain: the total propensity, or the fictitious rate `1` at
an absorbing state (total propensity `0`), where the chain then jumps `x ↦ x`. -/
noncomputable def holdRate (x : S → ℕ) : ℝ := if N.totalRate x = 0 then 1 else N.totalRate x

/-- The **generator** of the CRN: `L V(x) = ∑_r λ_r(x) (V(x - src r + prod r) - V(x))`. -/
noncomputable def generator (V : (S → ℕ) → ℝ) (x : S → ℕ) : ℝ :=
  ∑ r, N.propensity r x * (V (N.jump r x) - V x)

theorem totalRate_nonneg (x : S → ℕ) : 0 ≤ N.totalRate x :=
  sum_nonneg fun r _ => N.propensity_nonneg r x

theorem holdRate_pos (x : S → ℕ) : 0 < N.holdRate x := by
  unfold holdRate
  split_ifs with h
  · exact one_pos
  · exact lt_of_le_of_ne (N.totalRate_nonneg x) (Ne.symm h)

/-- Which reaction fires at a state with positive total propensity: `r` with probability
`λ_r(x) / λ(x)`. -/
noncomputable def reactionPMF (x : S → ℕ) (h : N.totalRate x ≠ 0) : PMF ρ :=
  PMF.ofFintype (fun r => ENNReal.ofReal (N.propensity r x / N.totalRate x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun r _ =>
      div_nonneg (N.propensity_nonneg r x) (N.totalRate_nonneg x), ← sum_div]
    change ENNReal.ofReal (N.totalRate x / N.totalRate x) = 1
    rw [div_self h, ENNReal.ofReal_one])

/-- The jump kernel of the CRN: the law of the next state, `x - src r + prod r` with
probability `λ_r(x) / λ(x)`; an absorbing state jumps to itself. -/
noncomputable def jumpPMF (x : S → ℕ) : PMF (S → ℕ) :=
  if h : N.totalRate x = 0 then PMF.pure x else (N.reactionPMF x h).map (N.jump · x)

/-- The law of the steps driving the CRN chain. -/
noncomputable def inputMeasure [Finite S] : Measure (ℕ → ((S → ℕ) → (S → ℕ)) × ℝ) :=
  JumpHold.inputMeasure N.jumpPMF

instance [Finite S] : IsProbabilityMeasure N.inputMeasure := by
  unfold inputMeasure; infer_instance

/-- The `n`-th jump time of the CRN chain started at `x₀`. -/
noncomputable def jumpTime (x₀ : S → ℕ) (ω : ℕ → ((S → ℕ) → (S → ℕ)) × ℝ) (n : ℕ) : ℝ :=
  JumpHold.jumpTime N.holdRate x₀ ω n

/-- Adding a constant to `V` does not change its generator. -/
theorem generator_add_const (V : (S → ℕ) → ℝ) (b : ℝ) (x : S → ℕ) :
    N.generator (fun y => V y + b) x = N.generator V x := by
  simp only [generator, add_sub_add_right_eq_sub]

/-- The rate-weighted mean of `V` after one jump: `λ(x) · E[V(next)] = L V(x) + λ(x) V(x)`. -/
theorem sum_propensity_mul_jump (V : (S → ℕ) → ℝ) (x : S → ℕ) :
    ∑ r, N.propensity r x * V (N.jump r x) = N.generator V x + N.totalRate x * V x := by
  simp only [generator, totalRate, mul_sub, sum_sub_distrib, sum_mul]
  ring

variable [Finite S]

/-- **Bridge from the generator to the one-step drift condition**: `L V ≤ c V` at `x` gives
`q(x) · E[V(next)] ≤ (q(x) + c) V(x)` for the jump–hold chain of the CRN. -/
theorem drift_of_generator_le (V : (S → ℕ) → ℝ≥0) {c : ℝ} (hc : 0 ≤ c) (x : S → ℕ)
    (h : N.generator (fun y => (V y : ℝ)) x ≤ c * V x) :
    ENNReal.ofReal (N.holdRate x) * ∫⁻ y, (V y : ℝ≥0∞) ∂(N.jumpPMF x).toMeasure ≤
      ENNReal.ofReal (N.holdRate x + c) * V x := by
  by_cases h0 : N.totalRate x = 0
  · have hj : N.jumpPMF x = PMF.pure x := by simp [jumpPMF, h0]
    have hh : N.holdRate x = 1 := by simp [holdRate, h0]
    rw [hj, hh, PMF.toMeasure_pure, lintegral_dirac]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ 1 + c)) _
  · let _ : MeasurableSpace ρ := ⊤
    have hT : 0 < N.totalRate x := lt_of_le_of_ne (N.totalRate_nonneg x) (Ne.symm h0)
    have hj : N.jumpPMF x = (N.reactionPMF x h0).map (N.jump · x) := by simp [jumpPMF, h0]
    have hh : N.holdRate x = N.totalRate x := by simp [holdRate, h0]
    rw [hj, hh, ← PMF.toMeasure_map _ _ measurable_from_top,
      lintegral_map (measurable_of_countable _) measurable_from_top, lintegral_fintype, mul_sum]
    have hterm : ∀ r, ENNReal.ofReal (N.totalRate x) *
        ((V (N.jump r x) : ℝ≥0∞) * (N.reactionPMF x h0).toMeasure {r}) =
        ENNReal.ofReal (N.propensity r x * V (N.jump r x)) := by
      intro r
      rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton r), reactionPMF,
        PMF.ofFintype_apply, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul hT.le]
      congr 1
      field_simp
    rw [sum_congr rfl fun r _ => hterm r, ← ENNReal.ofReal_sum_of_nonneg
      (f := fun r => N.propensity r x * V (N.jump r x)) fun r _ =>
      mul_nonneg (N.propensity_nonneg r x) (V _).2, ← ENNReal.ofReal_coe_nnreal (p := V x),
      ← ENNReal.ofReal_mul (by linarith)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [N.sum_propensity_mul_jump (fun y => (V y : ℝ))]
    linarith

omit [Finite S] in
/-- Bounded total propensity on sublevel sets gives bounded holding rates on them. -/
theorem holdRate_bdd (V : (S → ℕ) → ℝ≥0)
    (hbdd : ∀ m : ℝ, ∃ K, ∀ x, (V x : ℝ) < m → N.totalRate x ≤ K) (m : ℝ≥0) :
    ∃ K : ℝ, ∀ x, V x < m → N.holdRate x ≤ K := by
  obtain ⟨K, hK⟩ := hbdd m
  refine ⟨max K 1, fun x hx => ?_⟩
  unfold holdRate
  split_ifs
  · exact le_max_right _ _
  · exact (hK x (by exact_mod_cast hx)).trans (le_max_left _ _)

/-- **Discounted moment bound for a stochastic CRN**: if `L V ≤ c V` with `c ≥ 0`, then
`E[e^{-c T_n} V(Y_n)] ≤ V(x₀)` for every number `n` of reactions. -/
theorem lintegral_exp_jumpTime_mul_le (V : (S → ℕ) → ℝ≥0) {c : ℝ} (hc : 0 ≤ c)
    (hdrift : ∀ x, N.generator (fun y => (V y : ℝ)) x ≤ c * V x) (n : ℕ) (x₀ : S → ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-(c * N.jumpTime x₀ ω n))) * V (ctmcJumpChain x₀ ω n)
      ∂N.inputMeasure ≤ V x₀ :=
  JumpHold.lintegral_exp_jumpTime_mul_le (V := fun y => (V y : ℝ≥0∞)) N.holdRate_pos hc
    (fun x => N.drift_of_generator_le V hc x (hdrift x)) n x₀

/-- **Non-explosion of a stochastic CRN** (Foster–Lyapunov criterion; Meyn–Tweedie 1993,
Theorem 2.1; Gupta–Briat–Khammash 2014). If `V ≥ 0` satisfies the drift bound
`L V ≤ a V + b` with `a, b ≥ 0`, and the total propensity is bounded on each sublevel set
`{V < m}`, then from every initial state the jump times tend to `∞` almost surely: finite-time
blow-up has probability `0`. -/
theorem ae_tendsto_jumpTime_atTop (V : (S → ℕ) → ℝ≥0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdrift : ∀ x, N.generator (fun y => (V y : ℝ)) x ≤ a * V x + b)
    (hbdd : ∀ m : ℝ, ∃ K, ∀ x, (V x : ℝ) < m → N.totalRate x ≤ K) (x₀ : S → ℕ) :
    ∀ᵐ ω ∂N.inputMeasure, Tendsto (N.jumpTime x₀ ω) atTop atTop := by
  set W : (S → ℕ) → ℝ≥0 := fun y => V y + ⟨b, hb⟩
  have hW : ∀ y, (W y : ℝ) = V y + b := fun y => rfl
  have hWdrift : ∀ x, N.generator (fun y => (W y : ℝ)) x ≤ (a + 1) * W x := by
    intro x
    have h1 : N.generator (fun y => (W y : ℝ)) x = N.generator (fun y => (V y : ℝ)) x := by
      simp only [hW]; exact N.generator_add_const _ b x
    rw [h1, hW]
    have := hdrift x
    nlinarith [mul_nonneg ha hb, NNReal.coe_nonneg (V x)]
  refine JumpHold.ae_tendsto_jumpTime_atTop (V := W) N.holdRate_pos (by linarith)
    (fun x => N.drift_of_generator_le W (by linarith) x (hWdrift x))
    (N.holdRate_bdd W fun m => ?_) x₀
  obtain ⟨K, hK⟩ := hbdd m
  refine ⟨K, fun x hx => hK x ?_⟩
  rw [hW] at hx
  linarith

/-- On a finite set of species, a function bounding the total count from above has sublevel
sets with bounded total propensity. -/
theorem bddRate_of_coercive [Fintype S] (V : (S → ℕ) → ℝ)
    (hcoer : ∀ x, (∑ s, (x s : ℝ)) ≤ V x) (m : ℝ) :
    ∃ K, ∀ x, V x < m → N.totalRate x ≤ K := by
  have hfin : (Set.pi Set.univ fun _ : S => Set.Iic ⌈m⌉₊).Finite :=
    Set.Finite.pi fun _ => Set.finite_Iic _
  obtain ⟨K, hK⟩ := (hfin.image N.totalRate).bddAbove
  refine ⟨K, fun x hx => hK ⟨x, fun s _ => ?_, rfl⟩⟩
  have hs : (x s : ℝ) ≤ ∑ s, (x s : ℝ) :=
    single_le_sum (f := fun s => (x s : ℝ)) (fun _ _ => Nat.cast_nonneg _) (mem_univ s)
  have : (x s : ℝ) ≤ ⌈m⌉₊ := by
    linarith [hcoer x, Nat.le_ceil m]
  exact Set.mem_Iic.mpr (by exact_mod_cast this)

/-- **Non-explosion with a coercive Lyapunov function**: if `∑_s x_s ≤ V(x)` and
`L V ≤ a V + b` with `a, b ≥ 0`, the CRN chain is non-explosive from every initial state. -/
theorem ae_tendsto_jumpTime_atTop_of_coercive [Fintype S] (V : (S → ℕ) → ℝ≥0) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hdrift : ∀ x, N.generator (fun y => (V y : ℝ)) x ≤ a * V x + b)
    (hcoer : ∀ x, (∑ s, (x s : ℝ)) ≤ V x) (x₀ : S → ℕ) :
    ∀ᵐ ω ∂N.inputMeasure, Tendsto (N.jumpTime x₀ ω) atTop atTop :=
  N.ae_tendsto_jumpTime_atTop V ha hb hdrift (N.bddRate_of_coercive (fun y => V y) hcoer) x₀

/-- The process stays finite at every finite time: almost surely, for every `t`, some jump time
exceeds `t`, so the path `X t` is defined by finitely many reactions. -/
theorem ae_forall_exists_lt_jumpTime (V : (S → ℕ) → ℝ≥0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdrift : ∀ x, N.generator (fun y => (V y : ℝ)) x ≤ a * V x + b)
    (hbdd : ∀ m : ℝ, ∃ K, ∀ x, (V x : ℝ) < m → N.totalRate x ≤ K) (x₀ : S → ℕ) :
    ∀ᵐ ω ∂N.inputMeasure, ∀ t : ℝ, ∃ n, t < N.jumpTime x₀ ω n := by
  filter_upwards [N.ae_tendsto_jumpTime_atTop V ha hb hdrift hbdd x₀] with ω hω t
  exact (hω.eventually_gt_atTop t).exists

/-- The path `X t` of the CRN chain started at `x₀` (`JumpHold.path`). -/
noncomputable def path (x₀ : S → ℕ) (ω : ℕ → ((S → ℕ) → (S → ℕ)) × ℝ) (t : ℝ) : S → ℕ :=
  JumpHold.path N.holdRate x₀ ω t

/-- **Fixed-time moment bound for a stochastic CRN**: if `L V ≤ c V` with `c ≥ 0` and the total
propensity is bounded on sublevel sets of `V`, then `E[V(X_t)] ≤ e^{c t} V(x₀)` for `t ≥ 0`. -/
theorem lintegral_path_le (V : (S → ℕ) → ℝ≥0) {c : ℝ} (hc : 0 ≤ c)
    (hdrift : ∀ x, N.generator (fun y => (V y : ℝ)) x ≤ c * V x)
    (hbdd : ∀ m : ℝ, ∃ K, ∀ x, (V x : ℝ) < m → N.totalRate x ≤ K) (x₀ : S → ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫⁻ ω, (V (N.path x₀ ω t) : ℝ≥0∞) ∂N.inputMeasure ≤
      ENNReal.ofReal (Real.exp (c * t)) * V x₀ :=
  JumpHold.lintegral_path_le N.holdRate_pos hc
    (fun x => N.drift_of_generator_le V hc x (hdrift x)) (N.holdRate_bdd V hbdd) x₀ ht

end StochasticCRN

end MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion
