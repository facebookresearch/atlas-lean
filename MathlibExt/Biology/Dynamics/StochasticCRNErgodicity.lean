/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.SystemsBiology
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Ergodicity of complex-balanced stochastic reaction networks

A chemical reaction network `N` on species `S` (`ComplexBalanced.ReactionNetwork`) with rate
constants `κ` defines, under **stochastic mass-action kinetics**, a continuous-time Markov chain
on molecule counts `x ∈ ℕ^S`: reaction `r` fires at rate
`SystemsBiology.propensity N κ r x = κ r ∏_s x_s! / (x_s - y_s)!` (`y = src r`) and moves `x`
to `SystemsBiology.fire N r x = x - src r + prod r`. Its **stationary chemical master
equation** (`IsStationaryMasterSolution`) balances, at every state, the probability flux out
against the flux in from the unique predecessors `SystemsBiology.unfire N r x`
(`fire_eq_iff`).

Anderson, Craciun and Kurtz (2010) showed that if the deterministic mass-action system has a
complex-balanced equilibrium `c` (`ReactionNetwork.IsComplexBalanced`), the product-form
Poisson weights `π_c(x) = ∏_s c_s^{x_s} e^{-c_s} / x_s!` (`SystemsBiology.poissonWeight`)
solve that equation; `MathlibExt.Biology.Dynamics.SystemsBiology` proves this global balance
and the stationarity of the normalized weights on finite closed classes. This file adds
normalization on the whole infinite state space and the ergodic theorem: positive recurrence,
and almost sure convergence of time averages to `π_c`-expectations.

## Main results

Product form (no hypotheses beyond complex balance):

* `isStationaryMasterSolution_poissonWeight`: **Anderson–Craciun–Kurtz.** Complex balance of
  `c` implies that `π_c` solves the stationary master equation at every state of `ℕ^S` (this is
  `SystemsBiology.poissonWeight_mul_sum_propensity`, restated as a predicate).
* `hasSum_poissonWeight`, `poissonWeight_pos`: for `c ≥ 0`, `π_c` sums to `1` over all of
  `ℕ^S`; for `c > 0` it charges every state.
* `fire_eq_iff`: the predecessor of a state along a reaction is unique, which justifies the
  inflow term of `IsStationaryMasterSolution`.

Ergodic theory of regenerative processes (for a process `X` on any state space, with
`occupation X f t ω = ∫₀ᵗ f (X s ω) ds`):

* `tendsto_div_of_renewal`, `tendsto_div_zero_of_renewal`: deterministic renewal lemmas.
* `ae_tendsto_occupation_div`: the **renewal–reward theorem**. If the cycles between the
  regeneration times `R k` have i.i.d. lengths with finite mean and i.i.d. rewards, then
  `t⁻¹ ∫₀ᵗ f (X s) ds → E[reward] / E[length]` almost surely (Mathlib's strong law).
* `ae_tendsto_avg_atTop_of_not_integrable`: the strong law for nonnegative i.i.d. variables with
  infinite mean (averages tend to `∞`).
* `isPositiveRecurrent_of_stationary`: a regenerative process with a stationary law `ν`
  charging the regeneration state `x₀` is **positive recurrent** (finite mean cycle length).
* `integral_div_eq_of_stationary`, `IsRegenerative.ergodic`: under the stationary law the
  renewal–reward limit is `∫ f dν`, so time averages converge almost surely to `∫ f dν`.
* `IsRegenerative.ergodic_of_identDistrib`: the same limit for a second regenerative process
  with the same cycle laws (for example the chain started from a fixed state).

The ergodic theorem for complex-balanced networks:

* `ergodic_of_isComplexBalanced`: for a complex-balanced `c > 0` and the stochastic chain
  started from `π_c`, non-explosion, the forward-equation step and regeneration (the hypotheses
  below) give positive recurrence and almost sure convergence of the time averages of every
  bounded observable `f` to `∑ₓ π_c(x) f(x)`.
* `ergodic_of_isComplexBalanced_of_identDistrib`: the same limit from any start whose cycles
  have the stationary cycle laws.

## Hypotheses taken, not proved

The repository has no countable-state continuous-time Markov chain: the chains in
`MathlibExt.Probability.Process.ContinuousTimeMarkovChain` live on finite state spaces, while
`ℕ^S` is infinite. The chain `X` is therefore taken as given, a jointly measurable path process
`ℝ → Ω → (S → ℕ)`, and three standard properties of it are explicit hypotheses:

* `NoExplosion P X`: finite-time blow-up has probability `0`. This is the conclusion of the
  sibling non-explosion task (Foster–Lyapunov criteria), which is not imported.
* `htransfer`: under non-explosion, a probability solution of the stationary master equation,
  used as the initial law, is a stationary law of the chain (`π Q = 0 ⇒ π P(t) = π`; Norris
  1997, Theorem 3.5.5). For explosive chains this step fails.
* `IsRegenerative`: the chain regenerates at the successive entrance times into a state `x₀`,
  with i.i.d. cycle lengths and cycle rewards (the strong Markov property; Norris 1997,
  proof of Theorem 3.8.1).

Positive recurrence and the almost sure limit are proved from these, not assumed: positive
recurrence from the stationary law by the infinite-mean strong law, and the value of the limit
by bounded convergence under the stationary law. Irreducibility of the network enters only
through the regeneration hypothesis (a reducible chain need not return to `x₀`). Convergence of
the transition probabilities `P(X_t = x) → π_c(x)` from an arbitrary start, and unbounded
observables (for example the mean molecule count), are not treated.

## References

* D. F. Anderson, G. Craciun, T. G. Kurtz, *Product-form stationary distributions for
  deficiency zero chemical reaction networks*, Bull. Math. Biol. 72 (2010) 1947–1970,
  Theorem 4.1.
* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §3.4–3.8 (Theorems 3.5.3,
  3.5.5 and 3.8.1).
* S. Asmussen, *Applied Probability and Queues*, 2nd ed., Springer (2003), §VI.3
  (renewal–reward theorem).
-/

@[expose] public section

open Finset Real

namespace MathlibExt.Biology.Dynamics.StochasticCRNErgodicity

open MathlibExt.Biology.Dynamics.ComplexBalanced MathlibExt.Biology.Dynamics.SystemsBiology

variable {S ρ : Type*}

section Network

variable (N : ComplexBalanced.ReactionNetwork S ρ)

/-- The predecessor of `x` along reaction `r` is unique: a state `w ≥ src r` fires to `x`
exactly when `prod r ≤ x` and `w = unfire N r x`. So the inflow of the master equation at `x`
has one term per reaction `r` with `prod r ≤ x`. -/
theorem fire_eq_iff {r : ρ} {w x : S → ℕ} (hw : N.src r ≤ w) :
    fire N r w = x ↔ N.prod r ≤ x ∧ w = unfire N r x := by
  constructor
  · rintro rfl
    refine ⟨fun s => by simp [fire], funext fun s => ?_⟩
    have : N.src r s ≤ w s := hw s
    simp only [fire, unfire]
    omega
  · rintro ⟨hx, rfl⟩
    funext s
    have : N.prod r s ≤ x s := hx s
    simp only [fire, unfire]
    omega

/-- `p` solves the **stationary chemical master equation** (the stationary Kolmogorov forward
equation `p Q = 0`) of the stochastic mass-action chain with rate constants `κ`: at every state
`x` the probability flux out, `p x ∑_r λ_r(x)`, equals the flux in, one term
`p w λ_r(w)` for each reaction `r` with `prod r ≤ x` from its unique predecessor
`w = unfire N r x` (`fire_eq_iff`). -/
def IsStationaryMasterSolution [Fintype S] [Fintype ρ] (κ : ρ → ℝ) (p : (S → ℕ) → ℝ) : Prop :=
  ∀ x, p x * ∑ r, propensity N κ r x =
    ∑ r ∈ univ.filter (fun r => N.prod r ≤ x), p (unfire N r x) * propensity N κ r (unfire N r x)

/-- **Anderson–Craciun–Kurtz product-form theorem.** If `c` is complex balanced for the rate
constants `κ`, the product-form Poisson weights `π_c(x) = ∏_s c_s^{x_s} e^{-c_s} / x_s!`
(`poissonWeight`) solve the stationary chemical master equation at every state of `ℕ^S`.
This is `poissonWeight_mul_sum_propensity` (Anderson, Craciun & Kurtz 2010, Theorem 4.1),
restated as the predicate used below. -/
theorem isStationaryMasterSolution_poissonWeight [Fintype S] [Fintype ρ] {κ : ρ → ℝ}
    {c : S → ℝ} (h : N.IsComplexBalanced κ c) :
    IsStationaryMasterSolution N κ (poissonWeight c) :=
  poissonWeight_mul_sum_propensity N h

end Network

theorem poissonWeight_pos [Fintype S] {c : S → ℝ} (hc : ∀ s, 0 < c s) (x : S → ℕ) :
    0 < poissonWeight c x :=
  Finset.prod_pos fun s _ => by have := hc s; positivity

theorem poissonWeight_nonneg [Fintype S] {c : S → ℝ} (hc : ∀ s, 0 ≤ c s) (x : S → ℕ) :
    0 ≤ poissonWeight c x :=
  Finset.prod_nonneg fun s _ => by have := hc s; positivity

/-! ### The product-form law is a probability law -/

/-- A product of nonnegative summable families over a finite index set is summable on
`S → ℕ`, with the product of the sums. -/
theorem hasSum_prod_pi [Fintype S] {g : S → ℕ → ℝ} {a : S → ℝ} (hg : ∀ s n, 0 ≤ g s n)
    (ha : ∀ s, HasSum (g s) (a s)) :
    HasSum (fun x : S → ℕ => ∏ s, g s (x s)) (∏ s, a s) := by
  classical
  refine hasSum_of_isLUB_of_nonneg _ (fun x => Finset.prod_nonneg fun s _ => hg s _) ⟨?_, ?_⟩
  · rintro _ ⟨T, rfl⟩
    obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ x ∈ T, ∀ s, x s < K :=
      ⟨T.sup (fun x => ∑ s, x s) + 1, fun x hx s => Nat.lt_succ_of_le
        ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)).trans
          (Finset.le_sup (f := fun x => ∑ s, x s) hx))⟩
    have hsub : T ⊆ Fintype.piFinset fun _ => Finset.range K := fun x hx =>
      Fintype.mem_piFinset.2 fun s => Finset.mem_range.2 (hK x hx s)
    calc ∑ x ∈ T, ∏ s, g s (x s)
        ≤ ∑ x ∈ Fintype.piFinset (fun _ => Finset.range K), ∏ s, g s (x s) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ =>
            Finset.prod_nonneg fun s _ => hg s _
      _ = ∏ s, ∑ n ∈ Finset.range K, g s n := (Finset.prod_univ_sum _ _).symm
      _ ≤ ∏ s, a s := Finset.prod_le_prod₀ (fun s _ => Finset.sum_nonneg fun n _ => hg s n)
          (fun s _ => sum_le_hasSum _ (fun n _ => hg s n) (ha s))
  · intro b hb
    have hlim : Filter.Tendsto (fun K : ℕ => ∏ s, ∑ n ∈ Finset.range K, g s n) Filter.atTop
        (nhds (∏ s, a s)) :=
      tendsto_finsetProd _ fun s _ => (ha s).tendsto_sum_nat
    refine le_of_tendsto' hlim fun K => ?_
    rw [Finset.prod_univ_sum]
    exact hb ⟨_, rfl⟩

/-- For nonnegative means `c`, the product-form Poisson weights sum to `1` over all of `ℕ^S`:
`π_c` is a probability law on the whole (infinite) state space. -/
theorem hasSum_poissonWeight [Fintype S] {c : S → ℝ} (hc : ∀ s, 0 ≤ c s) :
    HasSum (poissonWeight c) 1 := by
  have h := hasSum_prod_pi (g := fun s n => c s ^ n * Real.exp (-c s) / n.factorial)
    (a := fun _ => 1) (fun s n => by have := hc s; positivity) fun s => by
      have h1 : HasSum (fun n : ℕ => c s ^ n / n.factorial) (Real.exp (c s)) := by
        rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp (c s)
      have h2 := h1.mul_right (Real.exp (-c s))
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2
      refine h2.congr_fun fun n => ?_
      ring
  unfold poissonWeight
  simpa only [Finset.prod_const_one] using h

/-! ### Deterministic renewal lemmas -/

section Renewal

open Filter Topology

/-- For a strictly increasing `R` with `R n → ∞`, the index `j t` of the cycle containing `t`:
`R (j t) ≤ t < R (j t + 1)` once `t ≥ R 1`, and `j t → ∞`. -/
private theorem exists_cycleIndex {R : ℕ → ℝ} (hR : StrictMono R)
    (hRtop : Tendsto R atTop atTop) :
    ∃ j : ℝ → ℕ, Tendsto j atTop atTop ∧
      ∀ t, R 1 ≤ t → 1 ≤ j t ∧ R (j t) ≤ t ∧ t < R (j t + 1) := by
  classical
  have hex : ∀ t : ℝ, ∃ n, t < R n := fun t => (hRtop.eventually_gt_atTop t).exists
  have hidx : ∀ t, R 1 ≤ t → 2 ≤ Nat.find (hex t) := by
    intro t ht
    by_contra h
    push Not at h
    have hspec := Nat.find_spec (hex t)
    have : R (Nat.find (hex t)) ≤ R 1 := hR.monotone (by omega)
    linarith
  refine ⟨fun t => Nat.find (hex t) - 1, ?_, fun t ht => ?_⟩
  · refine tendsto_atTop.2 fun K => ?_
    filter_upwards [eventually_ge_atTop (R (K + 1))] with t ht
    have hspec := Nat.find_spec (hex t)
    by_contra h
    push Not at h
    have : R (Nat.find (hex t)) ≤ R (K + 1) := hR.monotone (by omega)
    linarith
  · have h2 := hidx t ht
    refine ⟨show 1 ≤ Nat.find (hex t) - 1 by omega, ?_, ?_⟩
    · exact not_lt.1 (Nat.find_min (hex t) (by omega : Nat.find (hex t) - 1 < Nat.find (hex t)))
    · rw [Nat.sub_add_cancel (by omega)]
      exact Nat.find_spec (hex t)

/-- `R n / n → m > 0` forces `R n → ∞`. -/
private theorem tendsto_atTop_of_div {R : ℕ → ℝ} {m : ℝ} (hm : 0 < m)
    (hRlim : Tendsto (fun n : ℕ => R n / n) atTop (𝓝 m)) : Tendsto R atTop atTop := by
  have h := hRlim.pos_mul_atTop hm tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  field_simp

/-- **Renewal–reward, deterministic form.** Let `F` be `B`-Lipschitz on `[0, ∞)` with
`F 0 = 0`, and let `0 ≤ R 0 < R 1 < ⋯` with `R n / n → m > 0` and `F (R n) / n → w`.
Then `F t / t → w / m` as `t → ∞`. -/
theorem tendsto_div_of_renewal {F : ℝ → ℝ} {R : ℕ → ℝ} {B m w : ℝ} (hF0 : F 0 = 0)
    (hF : ∀ s t, 0 ≤ s → s ≤ t → |F t - F s| ≤ B * (t - s)) (hR0 : 0 ≤ R 0)
    (hR : StrictMono R) (hm : 0 < m) (hRlim : Tendsto (fun n : ℕ => R n / n) atTop (𝓝 m))
    (hFlim : Tendsto (fun n : ℕ => F (R n) / n) atTop (𝓝 w)) :
    Tendsto (fun t => F t / t) atTop (𝓝 (w / m)) := by
  have hB : 0 ≤ B := by
    have := hF 0 1 le_rfl zero_le_one
    linarith [abs_nonneg (F 1 - F 0)]
  have hRpos : ∀ n, 1 ≤ n → 0 < R n := fun n hn => hR0.trans_lt (hR (by omega))
  obtain ⟨j, hjtop, hj⟩ := exists_cycleIndex hR (tendsto_atTop_of_div hm hRlim)
  -- `G n = F (R n) / R n → w / m`
  have hG : Tendsto (fun n : ℕ => F (R n) / R n) atTop (𝓝 (w / m)) := by
    refine (hFlim.div hRlim hm.ne').congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have := (hRpos n hn).ne'
    simp only [Pi.div_apply]
    field_simp
  -- `D n = (R (n + 1) - R n) / R n → 0`
  have hD : Tendsto (fun n : ℕ => (R (n + 1) - R n) / R n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => R (n + 1) / ((n : ℝ) + 1)) atTop (𝓝 m) := by
      have := hRlim.comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n => ?_
      simp [Function.comp, Nat.cast_add, Nat.cast_one]
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
      have := (tendsto_one_div_atTop_nhds_zero_nat).const_add (1 : ℝ)
      rw [add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp
    have h3 := ((h1.mul h2).div hRlim hm.ne').sub_const 1
    rw [mul_one, div_self hm.ne', sub_self] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have := (hRpos n hn).ne'
    simp only [Pi.div_apply]
    field_simp
  -- the error bound
  have hbound : ∀ t, R 1 ≤ t →
      |F t / t - F (R (j t)) / R (j t)| ≤ 2 * B * ((R (j t + 1) - R (j t)) / R (j t)) := by
    intro t ht
    obtain ⟨hj1, hjle, hjlt⟩ := hj t ht
    have hRj := hRpos _ hj1
    have ht0 : 0 < t := hRj.trans_le hjle
    have h1 : |F t - F (R (j t))| ≤ B * (t - R (j t)) := hF _ _ hRj.le hjle
    have h2 : |F (R (j t))| ≤ B * R (j t) := by
      simpa [hF0] using hF 0 (R (j t)) le_rfl hRj.le
    have hsplit : F t / t - F (R (j t)) / R (j t) =
        (F t - F (R (j t))) / t - F (R (j t)) * (t - R (j t)) / (t * R (j t)) := by
      field_simp
      ring
    rw [hsplit]
    have hnum : 0 ≤ t - R (j t) := by linarith
    calc |(F t - F (R (j t))) / t - F (R (j t)) * (t - R (j t)) / (t * R (j t))|
        ≤ |(F t - F (R (j t))) / t| + |F (R (j t)) * (t - R (j t)) / (t * R (j t))| :=
          abs_sub _ _
      _ ≤ B * (t - R (j t)) / t + B * R (j t) * (t - R (j t)) / (t * R (j t)) := by
          gcongr
          · rw [abs_div, abs_of_pos ht0]
            exact div_le_div_of_nonneg_right h1 ht0.le
          · rw [abs_div, abs_mul, abs_of_nonneg hnum, abs_of_pos (mul_pos ht0 hRj)]
            gcongr
      _ = 2 * B * ((t - R (j t)) / t) := by
          field_simp
          ring
      _ ≤ 2 * B * ((R (j t + 1) - R (j t)) / R (j t)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc (t - R (j t)) / t ≤ (R (j t + 1) - R (j t)) / t :=
                div_le_div_of_nonneg_right (by linarith) ht0.le
            _ ≤ (R (j t + 1) - R (j t)) / R (j t) :=
                div_le_div_of_nonneg_left (by linarith) hRj hjle
  have herr : Tendsto (fun t => F t / t - F (R (j t)) / R (j t)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun t => 2 * B * ((R (j t + 1) - R (j t)) / R (j t))) atTop (𝓝 0) := by
      simpa using (hD.comp hjtop).const_mul (2 * B)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (R 1)] with t ht
    exact (Real.norm_eq_abs _).symm ▸ hbound t ht
  have := herr.add (hG.comp hjtop)
  rw [zero_add] at this
  exact this.congr fun t => by simp

/-- **Renewal, infinite mean, deterministic form.** Let `F` be nondecreasing on `[0, ∞)` with
`F 0 = 0`, and let `0 ≤ R 0 < R 1 < ⋯` with `R n / n → ∞` and `F (R n) / n → w`. Then
`F t / t → 0`. -/
theorem tendsto_div_zero_of_renewal {F : ℝ → ℝ} {R : ℕ → ℝ} {w : ℝ} (hF0 : F 0 = 0)
    (hF : MonotoneOn F (Set.Ici 0)) (hR0 : 0 ≤ R 0) (hR : StrictMono R)
    (hRlim : Tendsto (fun n : ℕ => R n / n) atTop atTop)
    (hFlim : Tendsto (fun n : ℕ => F (R n) / n) atTop (𝓝 w)) :
    Tendsto (fun t => F t / t) atTop (𝓝 0) := by
  have hRpos : ∀ n, 1 ≤ n → 0 < R n := fun n hn => hR0.trans_lt (hR (by omega))
  have hRtop : Tendsto R atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (hRlim.atTop_mul_atTop₀ tendsto_natCast_atTop_atTop)
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [div_mul_cancel₀ _ hn']
  obtain ⟨j, hjtop, hj⟩ := exists_cycleIndex hR hRtop
  -- `H n = F (R (n + 1)) / (n + 1) * ((n + 1) / R n) → w * 0`
  have hH : Tendsto (fun n : ℕ => F (R (n + 1)) / ((n : ℝ) + 1) * (((n : ℝ) + 1) / R n))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => F (R (n + 1)) / ((n : ℝ) + 1)) atTop (𝓝 w) := by
      refine (hFlim.comp (tendsto_add_atTop_nat 1)).congr fun n => ?_
      simp [Function.comp, Nat.cast_add, Nat.cast_one]
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
      have := (tendsto_one_div_atTop_nhds_zero_nat).const_add (1 : ℝ)
      rw [add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp
    have h3 : Tendsto (fun n : ℕ => (n : ℝ) / R n) atTop (𝓝 0) := by
      refine hRlim.inv_tendsto_atTop.congr fun n => ?_
      simp [inv_div]
    have := h1.mul (h2.mul h3)
    rw [mul_zero, mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have := (hRpos n hn).ne'
    field_simp
  refine squeeze_zero' ?_ ?_ (hH.comp hjtop)
  · filter_upwards [eventually_ge_atTop (R 1)] with t ht
    have ht0 : 0 ≤ t := (hRpos 1 le_rfl).le.trans ht
    have := hF (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht0) ht0
    rw [hF0] at this
    exact div_nonneg this ht0
  · filter_upwards [eventually_ge_atTop (R 1)] with t ht
    obtain ⟨hj1, hjle, hjlt⟩ := hj t ht
    have hRj := hRpos _ hj1
    have ht0 : 0 < t := hRj.trans_le hjle
    have hFt : 0 ≤ F t := by
      have := hF (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht0.le) ht0.le
      rwa [hF0] at this
    have hFle : F t ≤ F (R (j t + 1)) :=
      hF (Set.mem_Ici.2 ht0.le) (Set.mem_Ici.2 (ht0.le.trans hjlt.le)) hjlt.le
    have hj1' : ((j t : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    simp only [Function.comp]
    rw [div_mul_div_cancel₀ hj1']
    calc F t / t ≤ F (R (j t + 1)) / t := by gcongr
      _ ≤ F (R (j t + 1)) / R (j t) := by
          gcongr
          exact hFt.trans hFle

end Renewal

/-! ### Regenerative processes: occupation times and the strong law -/

section Regenerative

open MeasureTheory ProbabilityTheory Filter Topology Function

variable {Ω σ : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace σ]

/-- The length `R (k + 1) - R k` of the `k`-th regeneration cycle. -/
def cycleLength (R : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ := R (k + 1) ω - R k ω

/-- The occupation integral `∫₀ᵗ f (X s) ds` of the observable `f` along the path `X · ω`.
Divided by `t`, it is the time average of `f` up to time `t`. -/
noncomputable def occupation (X : ℝ → Ω → σ) (f : σ → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..t, f (X s ω)

/-- The reward `∫_{R k}^{R (k + 1)} f (X s) ds` collected by `f` during the `k`-th cycle. -/
noncomputable def cycleReward (X : ℝ → Ω → σ) (R : ℕ → Ω → ℝ) (f : σ → ℝ) (k : ℕ)
    (ω : Ω) : ℝ :=
  ∫ s in R k ω..R (k + 1) ω, f (X s ω)

/-- The process `X` **regenerates at the state `x₀`** at the times `0 ≤ R 0 < R 1 < ⋯`: it is
in `x₀` at each `R k`, the cycle lengths are pairwise independent and identically distributed,
and so are the rewards collected along the cycles by every bounded measurable observable;
the time spent in `x₀` during a cycle has finite mean.

For a continuous-time Markov chain on a countable state space and `R` the successive entrance
times into `x₀`, this is the strong Markov property at the times `R k` (Norris 1997, §3.4 and
Theorem 1.10.1, proof of Theorem 3.8.1): the cycle segments of the path are i.i.d. The time
spent in `x₀` during a cycle is one holding time there, exponential of rate `q(x₀)`. -/
structure IsRegenerative (P : Measure Ω) (X : ℝ → Ω → σ) (R : ℕ → Ω → ℝ) (x₀ : σ) : Prop where
  nonneg : ∀ ω, 0 ≤ R 0 ω
  strictMono : ∀ ω, StrictMono (R · ω)
  mem : ∀ k ω, X (R k ω) ω = x₀
  indep_length : Pairwise ((· ⟂ᵢ[P] ·) on cycleLength R)
  identDistrib_length : ∀ k, IdentDistrib (cycleLength R k) (cycleLength R 0) P P
  indep_reward : ∀ f : σ → ℝ, Measurable f → (∃ B, ∀ x, |f x| ≤ B) →
    Pairwise ((· ⟂ᵢ[P] ·) on cycleReward X R f)
  identDistrib_reward : ∀ f : σ → ℝ, Measurable f → (∃ B, ∀ x, |f x| ≤ B) →
    ∀ k, IdentDistrib (cycleReward X R f k) (cycleReward X R f 0) P P
  integrable_sojourn : Integrable (cycleReward X R (Set.indicator {x₀} 1) 0) P

/-- **Positive recurrence**: the mean regeneration-cycle (return) time is finite. -/
def IsPositiveRecurrent (P : Measure Ω) (R : ℕ → Ω → ℝ) : Prop :=
  Integrable (cycleLength R 0) P

variable {P : Measure Ω} {X : ℝ → Ω → σ} {f : σ → ℝ} {B : ℝ}

private theorem measurable_path (hX : Measurable (uncurry X)) (ω : Ω) :
    Measurable fun s => X s ω :=
  hX.comp (measurable_id.prodMk measurable_const)

private theorem measurable_path' (hX : Measurable (uncurry X)) (s : ℝ) :
    Measurable (X s) :=
  hX.comp (measurable_const.prodMk measurable_id)

private theorem intervalIntegrable_obs (hX : Measurable (uncurry X)) (hf : Measurable f)
    (hB : ∀ x, |f x| ≤ B) (ω : Ω) (a b : ℝ) :
    IntervalIntegrable (fun s => f (X s ω)) MeasureTheory.volume a b :=
  (intervalIntegrable_const (c := B)).mono_fun'
    (hf.comp (measurable_path hX ω)).aestronglyMeasurable
    (ae_of_all _ fun s => by simpa [Real.norm_eq_abs] using hB (X s ω))

private theorem abs_occupation_sub_le (hX : Measurable (uncurry X)) (hf : Measurable f)
    (hB : ∀ x, |f x| ≤ B) (ω : Ω) {s t : ℝ} (hst : s ≤ t) :
    |occupation X f t ω - occupation X f s ω| ≤ B * (t - s) := by
  unfold occupation
  rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_obs hX hf hB ω _ _)
    (intervalIntegrable_obs hX hf hB ω _ _), ← Real.norm_eq_abs]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t) (C := B)
    (f := fun s => f (X s ω)) fun x _ => by simpa [Real.norm_eq_abs] using hB (X x ω)
  rwa [abs_of_nonneg (sub_nonneg.2 hst)] at this

omit [MeasurableSpace σ] in
private theorem occupation_zero (ω : Ω) : occupation X f 0 ω = 0 := by
  simp [occupation]

private theorem occupation_R (hX : Measurable (uncurry X)) (hf : Measurable f)
    (hB : ∀ x, |f x| ≤ B) (R : ℕ → Ω → ℝ) (ω : Ω) (n : ℕ) :
    occupation X f (R n ω) ω =
      occupation X f (R 0 ω) ω + ∑ k ∈ range n, cycleReward X R f k ω := by
  unfold occupation cycleReward
  rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun k => R k ω)
    fun k _ => intervalIntegrable_obs hX hf hB ω _ _,
    intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_obs hX hf hB ω _ _)
    (intervalIntegrable_obs hX hf hB ω _ _)]

private theorem R_eq_sum (R : ℕ → Ω → ℝ) (ω : Ω) (n : ℕ) :
    R n ω = R 0 ω + ∑ k ∈ range n, cycleLength R k ω := by
  simp only [cycleLength]
  rw [Finset.sum_range_sub (fun k => R k ω)]
  ring

/-- If `a n = c + ∑_{k<n} d k` and the averages of `d` converge to `μ`, then `a n / n → μ`. -/
private theorem tendsto_div_of_eq_add_sum {a d : ℕ → ℝ} {c μ : ℝ}
    (h : ∀ n, a n = c + ∑ k ∈ range n, d k)
    (hd : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ k ∈ range n, d k) atTop (𝓝 μ)) :
    Tendsto (fun n : ℕ => a n / n) atTop (𝓝 μ) := by
  have := (tendsto_const_div_atTop_nhds_zero_nat c).add hd
  rw [zero_add] at this
  refine this.congr fun n => ?_
  rw [h, smul_eq_mul, add_div, div_eq_inv_mul (∑ k ∈ range n, d k)]

private theorem cycleLength_pos {R : ℕ → Ω → ℝ} (hR : ∀ ω, StrictMono (R · ω)) (k : ℕ)
    (ω : Ω) : 0 < cycleLength R k ω :=
  sub_pos.2 (hR ω (Nat.lt_succ_self k))

omit [MeasurableSpace σ] in
private theorem integrable_cycleReward [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ}
    (hB : ∀ x, |f x| ≤ B)
    (hR : ∀ ω, StrictMono (R · ω)) (hLint : Integrable (cycleLength R 0) P)
    (hWm : AEMeasurable (cycleReward X R f 0) P) : Integrable (cycleReward X R f 0) P := by
  refine (hLint.const_mul B).mono' hWm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := R 0 ω) (b := R 1 ω) (C := B)
    (f := fun s => f (X s ω)) fun x _ => by simpa [Real.norm_eq_abs] using hB (X x ω)
  rw [abs_of_pos (sub_pos.2 (hR ω zero_lt_one))] at this
  simpa [cycleReward, cycleLength] using this

/-- **Renewal–reward theorem.** If the cycle lengths of `X` are i.i.d. with finite mean and the
rewards of a bounded observable `f` are i.i.d., then almost surely the time averages of `f`
converge to `E[reward] / E[cycle length]`. -/
theorem ae_tendsto_occupation_div [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ}
    (hX : Measurable (uncurry X)) (hf : Measurable f) (hB : ∀ x, |f x| ≤ B)
    (hR0 : ∀ ω, 0 ≤ R 0 ω) (hR : ∀ ω, StrictMono (R · ω))
    (hLint : Integrable (cycleLength R 0) P)
    (hLind : Pairwise ((· ⟂ᵢ[P] ·) on cycleLength R))
    (hLid : ∀ k, IdentDistrib (cycleLength R k) (cycleLength R 0) P P)
    (hWind : Pairwise ((· ⟂ᵢ[P] ·) on cycleReward X R f))
    (hWid : ∀ k, IdentDistrib (cycleReward X R f k) (cycleReward X R f 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun t => occupation X f t ω / t) atTop
      (𝓝 (P[cycleReward X R f 0] / P[cycleLength R 0])) := by
  have hWint := integrable_cycleReward hB hR hLint (hWid 0).aemeasurable_fst
  have hm : 0 < P[cycleLength R 0] := by
    rw [integral_pos_iff_support_of_nonneg (fun ω => (cycleLength_pos hR 0 ω).le) hLint]
    have : support (cycleLength R 0) = Set.univ :=
      Set.eq_univ_of_forall fun ω => (cycleLength_pos hR 0 ω).ne'
    simp [this]
  filter_upwards [strong_law_ae _ hLint hLind hLid, strong_law_ae _ hWint hWind hWid]
    with ω hL hW
  exact tendsto_div_of_renewal (occupation_zero ω)
    (fun s t hs hst => abs_occupation_sub_le hX hf hB ω hst) (hR0 ω) (hR ω) hm
    (tendsto_div_of_eq_add_sum (R_eq_sum R ω) hL)
    (tendsto_div_of_eq_add_sum (occupation_R hX hf hB R ω) hW)

/-- **Strong law, infinite mean.** For pairwise independent, identically distributed
nonnegative `L k` with `E L 0 = ∞`, the averages `n⁻¹ ∑_{k<n} L k` tend to `∞` almost surely
(by the strong law for the truncations `min (L k) M` and monotone convergence). -/
theorem ae_tendsto_avg_atTop_of_not_integrable [IsProbabilityMeasure P] {L : ℕ → Ω → ℝ}
    (hL0 : ∀ k ω, 0 ≤ L k ω) (hint : ¬ Integrable (L 0) P)
    (hind : Pairwise ((· ⟂ᵢ[P] ·) on L)) (hid : ∀ k, IdentDistrib (L k) (L 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ range n, L k ω) atTop atTop := by
  set T : ℕ → ℕ → Ω → ℝ := fun M k ω => min (L k ω) M with hT
  have hmin : ∀ M : ℕ, Measurable fun x : ℝ => min x (M : ℝ) :=
    fun M => measurable_id.min measurable_const
  have hTind : ∀ M, Pairwise ((· ⟂ᵢ[P] ·) on T M) := fun M i j hij =>
    (hind hij).comp (hmin M) (hmin M)
  have hTid : ∀ M k, IdentDistrib (T M k) (T M 0) P P := fun M k => (hid k).comp (hmin M)
  have hTint : ∀ M, Integrable (T M 0) P := fun M =>
    Integrable.of_bound (hTid M 0).aemeasurable_fst.aestronglyMeasurable M
      (ae_of_all _ fun ω => by
        simp only [hT, Real.norm_eq_abs]
        rw [abs_of_nonneg (le_min (hL0 0 ω) (Nat.cast_nonneg M))]
        exact min_le_right _ _)
  -- the truncated means are unbounded
  have hunb : ∀ A : ℝ, ∃ M, A < P[T M 0] := by
    intro A
    by_contra hcon
    push Not at hcon
    apply hint
    have hm : AEMeasurable (L 0) P := (hid 0).aemeasurable_fst
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hL0 0))]
    have hsup : (fun ω => ENNReal.ofReal (L 0 ω)) =
        fun ω => ⨆ M : ℕ, ENNReal.ofReal (T M 0 ω) := by
      funext ω
      refine le_antisymm ?_ (iSup_le fun M => ENNReal.ofReal_le_ofReal (min_le_left _ _))
      obtain ⟨M, hM⟩ := exists_nat_ge (L 0 ω)
      exact le_iSup_of_le M (by simp [hT, min_eq_left hM])
    rw [hsup, lintegral_iSup' (fun M => ((hTid M 0).aemeasurable_fst).ennreal_ofReal)
      (ae_of_all _ fun ω M M' hMM' => ENNReal.ofReal_le_ofReal
        (min_le_min_left _ (by exact_mod_cast hMM')))]
    refine lt_of_le_of_lt (iSup_le fun M => ?_) (ENNReal.ofReal_lt_top (r := A))
    rw [← ofReal_integral_eq_lintegral_ofReal (hTint M)
      (ae_of_all _ fun ω => le_min (hL0 0 ω) (Nat.cast_nonneg M))]
    exact ENNReal.ofReal_le_ofReal (hcon M)
  have hslln : ∀ᵐ ω ∂P, ∀ M, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ k ∈ range n, T M k ω)
      atTop (𝓝 P[T M 0]) := ae_all_iff.2 fun M => strong_law_ae _ (hTint M) (hTind M) (hTid M)
  filter_upwards [hslln] with ω hω
  refine tendsto_atTop.2 fun A => ?_
  obtain ⟨M, hM⟩ := hunb A
  filter_upwards [(hω M).eventually_const_lt hM] with n hn
  refine hn.le.trans ?_
  rw [smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => min_le_left _ _)
    (inv_nonneg.2 (Nat.cast_nonneg n))

/-! ### Stationarity: positive recurrence and the value of the limit -/

/-- Under a stationary law `ν` (`X t` has law `ν` for every `t ≥ 0`), the mean occupation
integral is `E ∫₀ᵗ f (X s) ds = t ∫ f dν` (Fubini). -/
theorem integral_occupation [IsProbabilityMeasure P] (hX : Measurable (uncurry X))
    (hf : Measurable f) (hB : ∀ x, |f x| ≤ B) {ν : Measure σ}
    (hstat : ∀ t, 0 ≤ t → P.map (X t) = ν) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, occupation X f t ω ∂P = t * ∫ x, f x ∂ν := by
  have hint : Integrable (uncurry fun ω s => f (X s ω))
      (P.prod (MeasureTheory.volume.restrict (Set.Ioc 0 t))) := by
    have : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)) :=
      ⟨by simp⟩
    refine Integrable.of_bound ?_ B (ae_of_all _ fun z => ?_)
    · exact (hf.comp (hX.comp measurable_swap)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hB _
  simp only [occupation, intervalIntegral.integral_of_le ht]
  rw [integral_integral_swap hint]
  have hconst : ∀ s ∈ Set.Ioc (0 : ℝ) t, ∫ ω, f (X s ω) ∂P = ∫ x, f x ∂ν := by
    intro s hs
    rw [← hstat s hs.1.le, integral_map (measurable_path' hX s).aemeasurable
      hf.aestronglyMeasurable]
  rw [setIntegral_congr_fun measurableSet_Ioc hconst, setIntegral_const,
    Real.volume_real_Ioc_of_le ht, sub_zero, smul_eq_mul]

private theorem aestronglyMeasurable_occupation (hX : Measurable (uncurry X))
    (hf : Measurable f) {t : ℝ} (ht : 0 ≤ t) : AEStronglyMeasurable (occupation X f t) P := by
  have h : StronglyMeasurable fun ω =>
      ∫ s, f (X s ω) ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)) :=
    StronglyMeasurable.integral_prod_right (f := fun ω s => f (X s ω))
      (hf.comp (hX.comp measurable_swap)).stronglyMeasurable
  refine h.aestronglyMeasurable.congr (ae_of_all _ fun ω => ?_)
  simp [occupation, intervalIntegral.integral_of_le ht]

/-- Bounded convergence: almost sure convergence of the time averages to a constant `ℓ`
gives convergence of their means along integer times. -/
private theorem tendsto_integral_occupation_div [IsProbabilityMeasure P]
    (hX : Measurable (uncurry X)) (hf : Measurable f) (hB : ∀ x, |f x| ≤ B) {ℓ : ℝ}
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun t => occupation X f t ω / t) atTop (𝓝 ℓ)) :
    Tendsto (fun n : ℕ => ∫ ω, occupation X f n ω / n ∂P) atTop (𝓝 ℓ) := by
  have h := tendsto_integral_of_dominated_convergence (μ := P)
    (F := fun (n : ℕ) ω => occupation X f n ω / n) (f := fun _ => ℓ) (fun _ => B)
    (fun n => ((aestronglyMeasurable_occupation (P := P) hX hf
      (Nat.cast_nonneg n)).aemeasurable.div_const _).aestronglyMeasurable)
    (integrable_const B) (fun n => ae_of_all _ fun ω => ?_)
    (by filter_upwards [hlim] with ω hω using hω.comp tendsto_natCast_atTop_atTop)
  · simpa using h
  · rw [Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using (abs_nonneg _).trans (hB (X 0 ω))
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have := abs_occupation_sub_le hX hf hB ω hn'.le
      rw [occupation_zero, sub_zero, sub_zero] at this
      rw [abs_div, abs_of_pos hn', div_le_iff₀ hn']
      exact this

/-- Under a stationary law the mean of the time average up to an integer time `n ≥ 1` is the
space average. -/
private theorem integral_occupation_div [IsProbabilityMeasure P] (hX : Measurable (uncurry X))
    (hf : Measurable f) (hB : ∀ x, |f x| ≤ B) {ν : Measure σ}
    (hstat : ∀ t, 0 ≤ t → P.map (X t) = ν) {n : ℕ} (hn : 1 ≤ n) :
    ∫ ω, occupation X f n ω / n ∂P = ∫ x, f x ∂ν := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [integral_div, integral_occupation hX hf hB hstat (Nat.cast_nonneg n)]
  field_simp

/-- **Identification of the limit.** Under a stationary law `ν` and a regeneration structure
with finite mean cycle length, the renewal–reward limit `E[reward] / E[cycle length]` of a
bounded observable `f` is its space average `∫ f dν`. -/
theorem integral_div_eq_of_stationary [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ}
    (hX : Measurable (uncurry X)) (hf : Measurable f) (hB : ∀ x, |f x| ≤ B)
    (hR0 : ∀ ω, 0 ≤ R 0 ω) (hR : ∀ ω, StrictMono (R · ω))
    (hLint : Integrable (cycleLength R 0) P)
    (hLind : Pairwise ((· ⟂ᵢ[P] ·) on cycleLength R))
    (hLid : ∀ k, IdentDistrib (cycleLength R k) (cycleLength R 0) P P)
    (hWind : Pairwise ((· ⟂ᵢ[P] ·) on cycleReward X R f))
    (hWid : ∀ k, IdentDistrib (cycleReward X R f k) (cycleReward X R f 0) P P)
    {ν : Measure σ} (hstat : ∀ t, 0 ≤ t → P.map (X t) = ν) :
    P[cycleReward X R f 0] / P[cycleLength R 0] = ∫ x, f x ∂ν := by
  have h := tendsto_integral_occupation_div hX hf hB
    (ae_tendsto_occupation_div hX hf hB hR0 hR hLint hLind hLid hWind hWid)
  refine tendsto_nhds_unique h (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (integral_occupation_div hX hf hB hstat hn).symm

/-- **Positive recurrence from a stationary law.** If `X` regenerates at `x₀` and has a
stationary law `ν` charging `x₀`, then the mean cycle length is finite.

Otherwise the strong law gives `R n / n → ∞`, so the long-run fraction of time spent in `x₀`
vanishes almost surely; by bounded convergence its mean vanishes too, but under `ν` that mean
is `ν {x₀} > 0` at every time. -/
theorem isPositiveRecurrent_of_stationary [IsProbabilityMeasure P] [MeasurableSingletonClass σ]
    {R : ℕ → Ω → ℝ} {x₀ : σ} (hreg : IsRegenerative P X R x₀) (hX : Measurable (uncurry X))
    {ν : Measure σ} (hstat : ∀ t, 0 ≤ t → P.map (X t) = ν) (hx₀ : ν {x₀} ≠ 0) :
    IsPositiveRecurrent P R := by
  by_contra hL
  set f₀ : σ → ℝ := Set.indicator {x₀} 1 with hf₀def
  have hf₀ : Measurable f₀ := measurable_one.indicator (measurableSet_singleton x₀)
  have hf₀0 : ∀ x, 0 ≤ f₀ x := fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hf₀B : ∀ x, |f₀ x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (hf₀0 x)]
    exact Set.indicator_le_self' (fun _ _ => zero_le_one) x |>.trans (by simp)
  have hlen := ae_tendsto_avg_atTop_of_not_integrable
    (fun k ω => (cycleLength_pos hreg.strictMono k ω).le) hL hreg.indep_length
    hreg.identDistrib_length
  have hrew := strong_law_ae _ hreg.integrable_sojourn (hreg.indep_reward f₀ hf₀ ⟨1, hf₀B⟩)
    (hreg.identDistrib_reward f₀ hf₀ ⟨1, hf₀B⟩)
  have hzero : ∀ᵐ ω ∂P, Tendsto (fun t => occupation X f₀ t ω / t) atTop (𝓝 0) := by
    filter_upwards [hlen, hrew] with ω hLω hWω
    have hRtop : Tendsto (fun n : ℕ => R n ω / n) atTop atTop := by
      refine tendsto_atTop_mono' atTop ?_ hLω
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [R_eq_sum R ω n, add_div, inv_mul_eq_div]
      exact le_add_of_nonneg_left (div_nonneg (hreg.nonneg ω) hn'.le)
    refine tendsto_div_zero_of_renewal (occupation_zero ω) (fun a ha b hb hab => ?_)
      (hreg.nonneg ω) (hreg.strictMono ω) hRtop
      (tendsto_div_of_eq_add_sum (occupation_R hX hf₀ hf₀B R ω) hWω)
    have hsub := intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_obs hX hf₀ hf₀B ω 0 b) (intervalIntegrable_obs hX hf₀ hf₀B ω 0 a)
    have hnn : 0 ≤ ∫ s in a..b, f₀ (X s ω) :=
      intervalIntegral.integral_nonneg hab fun s _ => hf₀0 _
    simp only [occupation] at hsub ⊢
    linarith
  have h := tendsto_integral_occupation_div hX hf₀ hf₀B hzero
  have hconst : Tendsto (fun n : ℕ => ∫ ω, occupation X f₀ n ω / n ∂P) atTop
      (𝓝 (ν.real {x₀})) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [integral_occupation_div hX hf₀ hf₀B hstat hn, hf₀def,
      integral_indicator_one (measurableSet_singleton x₀)]
  have hprob : IsProbabilityMeasure ν := by
    rw [← hstat 0 le_rfl]
    infer_instance
  have := tendsto_nhds_unique hconst h
  exact hx₀ ((measureReal_eq_zero_iff (measure_ne_top ν _)).1 this)

/-- **Ergodic theorem for a stationary regenerative process.** If `X` regenerates at `x₀` and
has a stationary law `ν` with `ν {x₀} > 0`, then `X` is positive recurrent and, for every
bounded measurable observable `f`, the time averages `t⁻¹ ∫₀ᵗ f (X s) ds` converge almost
surely to the space average `∫ f dν`. -/
theorem IsRegenerative.ergodic [IsProbabilityMeasure P] [MeasurableSingletonClass σ]
    {R : ℕ → Ω → ℝ} {x₀ : σ} (hreg : IsRegenerative P X R x₀) (hX : Measurable (uncurry X))
    {ν : Measure σ} (hstat : ∀ t, 0 ≤ t → P.map (X t) = ν) (hx₀ : ν {x₀} ≠ 0) :
    IsPositiveRecurrent P R ∧ ∀ f : σ → ℝ, Measurable f → ∀ B, (∀ x, |f x| ≤ B) →
      ∀ᵐ ω ∂P, Tendsto (fun t => occupation X f t ω / t) atTop (𝓝 (∫ x, f x ∂ν)) := by
  have hpr := isPositiveRecurrent_of_stationary hreg hX hstat hx₀
  refine ⟨hpr, fun f hf B hB => ?_⟩
  have hfb : ∃ B, ∀ x, |f x| ≤ B := ⟨B, hB⟩
  have h := ae_tendsto_occupation_div hX hf hB hreg.nonneg hreg.strictMono hpr
    hreg.indep_length hreg.identDistrib_length (hreg.indep_reward f hf hfb)
    (hreg.identDistrib_reward f hf hfb)
  rwa [integral_div_eq_of_stationary hX hf hB hreg.nonneg hreg.strictMono hpr
    hreg.indep_length hreg.identDistrib_length (hreg.indep_reward f hf hfb)
    (hreg.identDistrib_reward f hf hfb) hstat] at h

/-- **Ergodic theorem from an arbitrary start.** A second regenerative process `X'` (for
instance the same chain started from a fixed state instead of from `ν`) whose cycle lengths
and cycle rewards have the same laws as those of a stationary regenerative `X` has the same
almost sure time-average limits `∫ f dν`. -/
theorem IsRegenerative.ergodic_of_identDistrib [IsProbabilityMeasure P]
    [MeasurableSingletonClass σ] {R : ℕ → Ω → ℝ} {x₀ : σ} (hreg : IsRegenerative P X R x₀)
    (hX : Measurable (uncurry X)) {ν : Measure σ} (hstat : ∀ t, 0 ≤ t → P.map (X t) = ν)
    (hx₀ : ν {x₀} ≠ 0) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X' : ℝ → Ω' → σ} {R' : ℕ → Ω' → ℝ} {x₀' : σ}
    (hreg' : IsRegenerative P' X' R' x₀') (hX' : Measurable (uncurry X'))
    (hlen : IdentDistrib (cycleLength R' 0) (cycleLength R 0) P' P)
    (hrew : ∀ f : σ → ℝ, Measurable f → (∃ B, ∀ x, |f x| ≤ B) →
      IdentDistrib (cycleReward X' R' f 0) (cycleReward X R f 0) P' P)
    (f : σ → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    ∀ᵐ ω ∂P', Tendsto (fun t => occupation X' f t ω / t) atTop (𝓝 (∫ x, f x ∂ν)) := by
  have hpr := isPositiveRecurrent_of_stationary hreg hX hstat hx₀
  have hfb : ∃ B, ∀ x, |f x| ≤ B := ⟨B, hB⟩
  have h := ae_tendsto_occupation_div hX' hf hB hreg'.nonneg hreg'.strictMono
    (hlen.integrable_iff.2 hpr) hreg'.indep_length hreg'.identDistrib_length
    (hreg'.indep_reward f hf hfb) (hreg'.identDistrib_reward f hf hfb)
  rwa [hlen.integral_eq, (hrew f hf hfb).integral_eq,
    integral_div_eq_of_stationary hX hf hB hreg.nonneg hreg.strictMono hpr
    hreg.indep_length hreg.identDistrib_length (hreg.indep_reward f hf hfb)
    (hreg.identDistrib_reward f hf hfb) hstat] at h

end Regenerative

/-! ### The ergodic theorem for complex-balanced stochastic reaction networks -/

section CRN

open MeasureTheory ProbabilityTheory Filter Topology Function

variable {S ρ : Type*}

/-- The law on `ℕ^S` with mass function `p` (a probability measure when `p ≥ 0` and
`∑ p = 1`, `isProbabilityMeasure_countLaw`). -/
noncomputable def countLaw (p : (S → ℕ) → ℝ) : Measure (S → ℕ) :=
  Measure.sum fun x => ENNReal.ofReal (p x) • Measure.dirac x

theorem countLaw_singleton [Finite S] (p : (S → ℕ) → ℝ) (x : S → ℕ) :
    countLaw p {x} = ENNReal.ofReal (p x) := by
  classical
  rw [countLaw, Measure.sum_apply _ (measurableSet_singleton x)]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton x),
    Set.indicator, Set.mem_singleton_iff, Pi.one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  exact tsum_ite_eq x _

theorem isProbabilityMeasure_countLaw {p : (S → ℕ) → ℝ} (hp : ∀ x, 0 ≤ p x) (h1 : HasSum p 1) :
    IsProbabilityMeasure (countLaw p) := by
  constructor
  rw [countLaw, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg hp h1.summable, h1.tsum_eq, ENNReal.ofReal_one]

/-- Integrals against `countLaw p` are the weighted sums `∑ₓ p x f x`. -/
theorem integral_countLaw [Finite S] {p : (S → ℕ) → ℝ} (hp : ∀ x, 0 ≤ p x) (h1 : HasSum p 1)
    {f : (S → ℕ) → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    ∫ x, f x ∂(countLaw p) = ∑' x, p x * f x := by
  have := isProbabilityMeasure_countLaw hp h1
  have hint : Integrable f (countLaw p) :=
    Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable B
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hB x)
  rw [integral_countable hint]
  refine tsum_congr fun x => ?_
  rw [measureReal_def, countLaw_singleton, ENNReal.toReal_ofReal (hp x), smul_eq_mul]

/-- **Non-explosion** of a path process on `ℕ^S`: almost surely, the total molecule count
stays bounded on every finite time interval (no blow-up in finite time). This is the
conclusion of the Foster–Lyapunov criteria of the sibling task on non-explosion of
stochastic reaction networks, used here only as a hypothesis. -/
def NoExplosion [Fintype S] {Ω : Type*} {_ : MeasurableSpace Ω} (P : Measure Ω)
    (X : ℝ → Ω → (S → ℕ)) : Prop :=
  ∀ᵐ ω ∂P, ∀ t, BddAbove ((fun s => ∑ i, X s ω i) '' Set.Icc 0 t)

variable [Fintype S] [Fintype ρ] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **Ergodic theorem for complex-balanced stochastic reaction networks.**

Let the concentrations `c > 0` be complex balanced for the rate constants `κ`, and let `X` be
the stochastic mass-action chain of the network on `ℕ^S`, started from the product-form
Poisson law `π_c` (`hinit`). Assume

* `hnonexp`: the chain does not explode (the sibling non-explosion task's conclusion);
* `htransfer`: for this chain, non-explosion makes every probability solution of the
  stationary master equation, used as the initial law, a stationary law of the chain (the
  forward-equation step `π Q = 0 ⇒ π P(t) = π` of Norris 1997, Theorem 3.5.5, which fails for
  explosive chains);
* `hreg`: the chain regenerates at a state `x₀` (the strong Markov property at the
  successive entrance times `R k` into `x₀`).

Then the chain is positive recurrent (finite mean return time to `x₀`), and for every bounded
observable `f` the time averages `t⁻¹ ∫₀ᵗ f (X s) ds` converge almost surely to the
product-form mean `∑ₓ π_c(x) f(x)`.

The product-form law enters through `isStationaryMasterSolution_poissonWeight` (Anderson,
Craciun & Kurtz 2010, Theorem 4.1); positive recurrence and the limit come from
`IsRegenerative.ergodic` (renewal–reward and the strong law of large numbers). -/
theorem ergodic_of_isComplexBalanced {N : ComplexBalanced.ReactionNetwork S ρ} {κ : ρ → ℝ}
    {c : S → ℝ} (hcb : N.IsComplexBalanced κ c) (hc : ∀ s, 0 < c s)
    {X : ℝ → Ω → (S → ℕ)} (hX : Measurable (uncurry X)) (hnonexp : NoExplosion P X)
    (htransfer : NoExplosion P X → ∀ p : (S → ℕ) → ℝ, (∀ x, 0 ≤ p x) → HasSum p 1 →
      IsStationaryMasterSolution N κ p → P.map (X 0) = countLaw p →
      ∀ t, 0 ≤ t → P.map (X t) = countLaw p)
    (hinit : P.map (X 0) = countLaw (poissonWeight c))
    {R : ℕ → Ω → ℝ} {x₀ : S → ℕ} (hreg : IsRegenerative P X R x₀) :
    IsPositiveRecurrent P R ∧ ∀ f : (S → ℕ) → ℝ, ∀ B, (∀ x, |f x| ≤ B) →
      ∀ᵐ ω ∂P, Tendsto (fun t => occupation X f t ω / t) atTop
        (𝓝 (∑' x, poissonWeight c x * f x)) := by
  have hnn := poissonWeight_nonneg fun s => (hc s).le
  have h1 := hasSum_poissonWeight fun s => (hc s).le
  have hstat := htransfer hnonexp _ hnn h1
    (isStationaryMasterSolution_poissonWeight N hcb) hinit
  have hx₀ : countLaw (poissonWeight c) {x₀} ≠ 0 := by
    rw [countLaw_singleton, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact poissonWeight_pos hc x₀
  obtain ⟨hpr, hlim⟩ := hreg.ergodic hX hstat hx₀
  refine ⟨hpr, fun f B hB => ?_⟩
  rw [← integral_countLaw hnn h1 hB]
  exact hlim f (measurable_of_countable f) B hB

/-- **The same limit from any initial state.** If a second chain `X'` (for instance started
from a fixed state) regenerates with cycle lengths and cycle rewards distributed as those of the
stationary chain of `ergodic_of_isComplexBalanced` (the strong Markov property makes all
cycles after the first entrance into `x₀` copies of one another), its time averages converge
almost surely to the same product-form means. -/
theorem ergodic_of_isComplexBalanced_of_identDistrib
    {N : ComplexBalanced.ReactionNetwork S ρ} {κ : ρ → ℝ}
    {c : S → ℝ} (hcb : N.IsComplexBalanced κ c) (hc : ∀ s, 0 < c s)
    {X : ℝ → Ω → (S → ℕ)} (hX : Measurable (uncurry X)) (hnonexp : NoExplosion P X)
    (htransfer : NoExplosion P X → ∀ p : (S → ℕ) → ℝ, (∀ x, 0 ≤ p x) → HasSum p 1 →
      IsStationaryMasterSolution N κ p → P.map (X 0) = countLaw p →
      ∀ t, 0 ≤ t → P.map (X t) = countLaw p)
    (hinit : P.map (X 0) = countLaw (poissonWeight c))
    {R : ℕ → Ω → ℝ} {x₀ : S → ℕ} (hreg : IsRegenerative P X R x₀)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X' : ℝ → Ω' → (S → ℕ)} {R' : ℕ → Ω' → ℝ} {x₀' : S → ℕ}
    (hreg' : IsRegenerative P' X' R' x₀') (hX' : Measurable (uncurry X'))
    (hlen : IdentDistrib (cycleLength R' 0) (cycleLength R 0) P' P)
    (hrew : ∀ f : (S → ℕ) → ℝ, Measurable f → (∃ B, ∀ x, |f x| ≤ B) →
      IdentDistrib (cycleReward X' R' f 0) (cycleReward X R f 0) P' P)
    (f : (S → ℕ) → ℝ) (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    ∀ᵐ ω ∂P', Tendsto (fun t => occupation X' f t ω / t) atTop
      (𝓝 (∑' x, poissonWeight c x * f x)) := by
  have hnn := poissonWeight_nonneg fun s => (hc s).le
  have h1 := hasSum_poissonWeight fun s => (hc s).le
  have hstat := htransfer hnonexp _ hnn h1
    (isStationaryMasterSolution_poissonWeight N hcb) hinit
  have hx₀ : countLaw (poissonWeight c) {x₀} ≠ 0 := by
    rw [countLaw_singleton, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact poissonWeight_pos hc x₀
  rw [← integral_countLaw hnn h1 hB]
  exact hreg.ergodic_of_identDistrib hX hstat hx₀ hreg' hX' hlen hrew f
    (measurable_of_countable f) B hB

end CRN

end MathlibExt.Biology.Dynamics.StochasticCRNErgodicity
