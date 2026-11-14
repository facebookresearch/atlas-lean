/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.StochasticCRNErgodicity
public import MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Normed.Group.Tannery
import MathlibExt.Probability.Distributions.ExponentialMoments
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Regeneration of complex-balanced stochastic reaction networks

`MathlibExt.Biology.Dynamics.StochasticCRNErgodicity` (`ergodic_of_isComplexBalanced`) proves
positive recurrence and the ergodic theorem for a path process that is *assumed* to be
non-explosive (`hnonexp`), to carry the stationary master equation to a stationary law
(`htransfer`), and to regenerate at a state `x₀` (`hreg`). This file works with the chain itself,
the jump–hold chain of `MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion` with stochastic
mass-action propensities, and proves the same conclusion with those hypotheses replaced by

* complex balance of `c > 0` for the rate constants `κ ≥ 0` (as in the ergodicity file);
* a Foster–Lyapunov drift bound `L V ≤ a V + b` with `∑_s x_s ≤ V(x)`, from which
  `StochasticCRNNonExplosion` proves non-explosion;
* reachability of every state from `x₀` along reactions with positive propensity.

Reachability cannot be dropped: complex balance does not give regeneration. For a network with a
conservation law (for example `A ⇌ B`, which is complex balanced) the state space splits into
infinitely many closed classes, so with positive probability the chain started from `π_c` never
visits `x₀`.

## Main results

The strong Markov property of the i.i.d. steps driving the chain:

* `measure_inter_shiftAt_preimage`, `map_prod_shiftAt`: after a stopping time `τ` of the step
  sequence, the remaining steps are independent of everything determined before `τ` and have the
  law of the whole sequence.

The stationary master equation transferred to the chain (`htransfer`, in Laplace form):

* `tsum_mul_lintegral_abelSum`: the **resolvent identity**. If `w` balances the rate-weighted
  jump kernel, `∑_x w(x) q(x) K(x, y) = w(y) q(y)`, with `∑ w q < ∞`, then
  `∑_x w(x) E_x[a ∫_0^∞ e^{-a t} g(X_t) dt] = ∑_x w(x) g(x)` for `a > 0`, `0 ≤ g ≤ 1`.
* `tsum_poissonWeight_mul_holdRate_mul_jumpPMF`, `tsum_ofReal_poissonWeight_mul_holdRate_ne_top`:
  complex balance gives this balance for the Poisson weights `π_c`, and `∑ π_c q < ∞`.
* `tsum_poissonWeight_mul_lintegral_laplace_path`: the resulting Laplace-form stationarity of
  `π_c` for the stochastic mass-action chain.

Regeneration (`hreg`):

* `measure_return_eq_one`: **recurrence** of `x₀` from the balanced law (otherwise the chain visits
  `x₀` finitely often, and the identification below would force `w(x₀) = 0`).
* `hitProb_eq_one`, `ae_forall_visit_ne_top`: with reachability, every visit to `x₀` happens almost
  surely from every initial state.
* `identDistrib_cycleSum`, `indepFun_cycleSum_of_lt`: the regeneration cycles between successive
  visits are identically distributed and independent.

Positive recurrence and the limit:

* `tendsto_abel_of_tendsto_cesaro`: an **Abelian theorem** (Cesàro means converge to `L` ⇒ Abel
  means converge to `L`).
* `eq_tsum_of_ae_tendsto`: a time-average limit that is the same from every initial state equals
  the `w`-mean (Abel means, bounded convergence, the resolvent identity).
* `integrable_returnReward`: **positive recurrence** (finite mean return time to `x₀`).
* `ergodic_of_balanced`: the ergodic theorem for a jump–hold chain with a balanced law.

For stochastic reaction networks:

* `ergodic_of_isComplexBalanced_of_reachable`: for a complex-balanced network with a drift bound and
  reachability, the chain returns to `x₀` almost surely with finite mean return time, and from every
  initial state the time averages of every bounded observable converge almost surely to
  `∑_y π_c(y) f(y)`.
* `ergodic_of_isComplexBalanced_of_reachable_countLaw`: the same limit for the chain started from
  `π_c`, the setting of `StochasticCRNErgodicity.ergodic_of_isComplexBalanced`.
* `noExplosion_path`: the non-explosion of `StochasticCRNNonExplosion` (jump times tend to `∞`)
  gives `StochasticCRNErgodicity.NoExplosion` of the path.

## What is not proved

* `htransfer` is discharged in Laplace form only: `∫_0^∞ a e^{-a t} P_{π_c}(X_t = y) dt = π_c(y)`
  for every `a > 0`. The fixed-time identity `P_{π_c}(X_t = y) = π_c(y)` would follow by uniqueness
  of Laplace transforms, which is not proved; the ergodic theorem does not need it, because the
  limit is identified through Abel means.
* `StochasticCRNErgodicity.IsRegenerative` asks for its properties at every sample point; the chain
  has them almost surely. Its theorems are therefore not applied: the renewal–reward argument is
  redone along the regeneration cycles, reusing the deterministic renewal lemmas and the
  infinite-mean strong law of that file.
* Non-explosion of every complex-balanced network (Anderson, Cappelletti, Koyama and Kurtz 2018) is
  not proved; a drift bound is assumed, as in `StochasticCRNNonExplosion`.
* Convergence of transition probabilities and unbounded observables are not treated.

## Implementation notes

Two lemmas are verbatim copies of private lemmas: `tendsto_div_of_eq_add_sum'` of
`StochasticCRNErgodicity.tendsto_div_of_eq_add_sum`, and `propensity_eq_zero_of_not_le` of
`SystemsBiology.propensity_eq_zero`. A recorded follow-up of T223 makes those two originals public
and deletes the copies. The step-sequence lemmas (`ProbabilityTheory.measurable_ctmcShift`,
`ProbabilityTheory.ctmc_indep_infinitePi`, `ProbabilityTheory.ctmc_map_shift_infinitePi`) are
used from `ContinuousTimeMarkovChain/Path.lean`.

## References

* D. F. Anderson, G. Craciun, T. G. Kurtz, *Product-form stationary distributions for deficiency
  zero chemical reaction networks*, Bull. Math. Biol. 72 (2010) 1947–1970.
* D. F. Anderson, D. Cappelletti, M. Koyama, T. G. Kurtz, *Non-explosivity of stochastically
  modeled reaction networks that are complex balanced*, Bull. Math. Biol. 80 (2018) 2561–2579.
* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §2.6–2.8, §3.4–3.8.
* S. Asmussen, *Applied Probability and Queues*, 2nd ed., Springer (2003), §V–VI.
-/

@[expose] public section

open Finset MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace MathlibExt.Biology.Dynamics.StochasticCRNRegeneration

open MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion

/-! ### The strong Markov property of an i.i.d. step sequence -/

section StrongMarkov

variable {σ : Type*}

/-- `τ` is a **stopping time of the step sequence**: whether `τ ω = n` depends only on the first
`n` steps `ω 0, …, ω (n - 1)`. The value `⊤` means that the event never happens. -/
def IsStepStoppingTime (τ : (ℕ → (σ → σ) × ℝ) → ℕ∞) : Prop :=
  ∀ (n : ℕ) (ω ω' : ℕ → (σ → σ) × ℝ), τ ω = n → (∀ i < n, ω i = ω' i) → τ ω' = n

/-- The set `C` is **determined before** `τ`: on `{τ = n}`, membership in `C` depends only on the
first `n` steps. -/
def IsDeterminedBefore (τ : (ℕ → (σ → σ) × ℝ) → ℕ∞) (C : Set (ℕ → (σ → σ) × ℝ)) : Prop :=
  ∀ (n : ℕ) (ω ω' : ℕ → (σ → σ) × ℝ), τ ω = n → (∀ i < n, ω i = ω' i) → ω ∈ C → ω' ∈ C

/-- The steps after the random time `τ` (after `0` steps if `τ = ⊤`). -/
def shiftAt (τ : (ℕ → (σ → σ) × ℝ) → ℕ∞) (ω : ℕ → (σ → σ) × ℝ) : ℕ → (σ → σ) × ℝ :=
  ctmcShift (τ ω).toNat ω

variable [MeasurableSpace σ]

/-- The σ-algebra of the first `n` steps. -/
abbrev pastSigma (n : ℕ) : MeasurableSpace (ℕ → (σ → σ) × ℝ) :=
  ⨆ k ∈ Set.Iio n, MeasurableSpace.comap (fun ω : ℕ → (σ → σ) × ℝ => ω k) inferInstance

/-- The σ-algebra of the steps from index `n` on. -/
abbrev futureSigma (n : ℕ) : MeasurableSpace (ℕ → (σ → σ) × ℝ) :=
  ⨆ k ∈ Set.Ici n, MeasurableSpace.comap (fun ω : ℕ → (σ → σ) × ℝ => ω k) inferInstance

/-- A measurable set whose membership depends only on the first `n` steps is measurable for the
σ-algebra of the first `n` steps. -/
theorem measurableSet_pastSigma {n : ℕ} {A : Set (ℕ → (σ → σ) × ℝ)} (hA : MeasurableSet A)
    (hdet : ∀ ω ω', (∀ i < n, ω i = ω' i) → ω ∈ A → ω' ∈ A) :
    MeasurableSet[pastSigma n] A := by
  classical
  let φ : (ℕ → (σ → σ) × ℝ) → (ℕ → (σ → σ) × ℝ) := fun ω k => if k < n then ω k else (id, 0)
  have hφ : Measurable[pastSigma n] φ := by
    refine @measurable_pi_iff _ _ _ (pastSigma n) _ _ |>.2 fun k => ?_
    by_cases hk : k < n
    · simp only [φ, hk, ite_true]
      exact (comap_measurable (fun ω : ℕ → (σ → σ) × ℝ => ω k)).mono
        (le_iSup₂ (f := fun k (_ : k ∈ Set.Iio n) =>
          MeasurableSpace.comap (fun ω : ℕ → (σ → σ) × ℝ => ω k) inferInstance) k hk) le_rfl
    · simp only [φ, hk, ite_false]
      exact @measurable_const _ _ _ (pastSigma n) _
  have hA' : A = φ ⁻¹' A := by
    ext ω
    constructor
    · exact hdet ω (φ ω) fun i hi => by simp [φ, hi]
    · exact hdet (φ ω) ω fun i hi => by simp [φ, hi]
  rw [hA']
  exact hφ hA

/-- The shift by `n` steps is measurable (for the product σ-algebra). -/
theorem measurable_ctmcShift_pi (n : ℕ) : Measurable (ctmcShift (ι := σ) n) :=
  Measurable.of_eval fun j => measurable_pi_apply (n + j)

variable (ν : Measure ((σ → σ) × ℝ)) [IsProbabilityMeasure ν]

/-- The level sets of a measurable stopping time are measurable. -/
theorem measurable_shiftAt {τ : (ℕ → (σ → σ) × ℝ) → ℕ∞} (hτ : Measurable τ) :
    Measurable (shiftAt τ) := by
  have h : Measurable fun p : ℕ × (ℕ → (σ → σ) × ℝ) => ctmcShift p.1 p.2 :=
    measurable_from_prod_countable_right fun n => measurable_ctmcShift_pi n
  exact h.comp (((measurable_of_countable ENat.toNat).comp hτ).prodMk measurable_id)

/-- **Strong Markov property of an i.i.d. step sequence.** For a stopping time `τ` and a
set `C` determined before `τ`, on `{τ < ⊤}` the steps after `τ` are independent of `C` and have
the law of the whole sequence:
`P(τ < ⊤, C, shift_τ ∈ B) = P(τ < ⊤, C) P(B)`. -/
theorem measure_inter_shiftAt_preimage {τ : (ℕ → (σ → σ) × ℝ) → ℕ∞}
    (hτ : IsStepStoppingTime τ) (hτm : Measurable τ) {C : Set (ℕ → (σ → σ) × ℝ)}
    (hC : MeasurableSet C) (hCd : IsDeterminedBefore τ C) {B : Set (ℕ → (σ → σ) × ℝ)}
    (hB : MeasurableSet B) :
    (Measure.infinitePi fun _ : ℕ => ν) ({ω | τ ω ≠ ⊤} ∩ C ∩ shiftAt τ ⁻¹' B) =
      (Measure.infinitePi fun _ : ℕ => ν) ({ω | τ ω ≠ ⊤} ∩ C) *
        (Measure.infinitePi fun _ : ℕ => ν) B := by
  set μ := Measure.infinitePi fun _ : ℕ => ν
  have hlev : ∀ n : ℕ, MeasurableSet {ω | τ ω = n} := fun n =>
    hτm (measurableSet_singleton (n : ℕ∞))
  have hsplit : ∀ D : Set (ℕ → (σ → σ) × ℝ),
      {ω | τ ω ≠ ⊤} ∩ D = ⋃ n : ℕ, {ω | τ ω = n} ∩ D := by
    intro D
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨h, hD⟩
      exact ⟨(τ ω).toNat, (ENat.natCast_toNat h).symm, hD⟩
    · rintro ⟨n, hn, hD⟩
      exact ⟨by simp [hn], hD⟩
  have hdisj : ∀ D : Set (ℕ → (σ → σ) × ℝ),
      Pairwise (Function.onFun Disjoint fun n : ℕ => {ω | τ ω = n} ∩ D) := by
    intro D i j hij
    refine Set.disjoint_left.mpr fun ω hi hj => hij ?_
    exact_mod_cast hi.1.symm.trans hj.1
  have hpiece : ∀ n : ℕ, {ω | τ ω = n} ∩ (C ∩ shiftAt τ ⁻¹' B) =
      ({ω | τ ω = n} ∩ C) ∩ ctmcShift n ⁻¹' B := by
    intro n
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, shiftAt]
    constructor
    · rintro ⟨hn, hC, hB⟩
      refine ⟨⟨hn, hC⟩, ?_⟩
      rwa [hn, ENat.toNat_natCast] at hB
    · rintro ⟨⟨hn, hC⟩, hB⟩
      refine ⟨hn, hC, ?_⟩
      rwa [hn, ENat.toNat_natCast]
  have hmul : ∀ n : ℕ, μ (({ω | τ ω = n} ∩ C) ∩ ctmcShift n ⁻¹' B) =
      μ ({ω | τ ω = n} ∩ C) * μ B := by
    intro n
    have hpast : MeasurableSet[pastSigma n] ({ω | τ ω = n} ∩ C) := by
      refine measurableSet_pastSigma ((hlev n).inter hC) fun ω ω' hagree hω => ?_
      exact ⟨hτ n ω ω' hω.1 hagree, hCd n ω ω' hω.1 hagree hω.2⟩
    have hfut : MeasurableSet[futureSigma n] (ctmcShift n ⁻¹' B) :=
      ProbabilityTheory.measurable_ctmcShift n hB
    rw [((ProbabilityTheory.ctmc_indep_infinitePi ν n).indepSet_of_measurableSet hpast
      hfut).measure_inter_eq_mul, ← Measure.map_apply (measurable_ctmcShift_pi n) hB,
      ProbabilityTheory.ctmc_map_shift_infinitePi]
  rw [Set.inter_assoc, hsplit, hsplit, measure_iUnion (hdisj _) fun n =>
    (hlev n).inter (hC.inter (measurable_shiftAt hτm hB)), measure_iUnion (hdisj _) fun n =>
    (hlev n).inter hC, ← ENNReal.tsum_mul_right]
  exact tsum_congr fun n => by rw [hpiece, hmul]

/-- **Strong Markov property, almost surely finite stopping time**: the steps after `τ` have the
law of the whole sequence and are independent of every measurable map determined before `τ`. -/
theorem map_prod_shiftAt {τ : (ℕ → (σ → σ) × ℝ) → ℕ∞} (hτ : IsStepStoppingTime τ)
    (hτm : Measurable τ) (hfin : (Measure.infinitePi fun _ : ℕ => ν) {ω | τ ω = ⊤} = 0)
    {β : Type*} [MeasurableSpace β] {G : (ℕ → (σ → σ) × ℝ) → β} (hG : Measurable G)
    (hGd : ∀ (n : ℕ) (ω ω' : ℕ → (σ → σ) × ℝ), τ ω = n → (∀ i < n, ω i = ω' i) → G ω = G ω') :
    (Measure.infinitePi fun _ : ℕ => ν).map (fun ω => (G ω, shiftAt τ ω)) =
      ((Measure.infinitePi fun _ : ℕ => ν).map G).prod (Measure.infinitePi fun _ : ℕ => ν) := by
  set μ := Measure.infinitePi fun _ : ℕ => ν
  have hfin' : ∀ D : Set (ℕ → (σ → σ) × ℝ), μ ({ω | τ ω ≠ ⊤} ∩ D) = μ D := by
    intro D
    refine measure_congr ?_
    have : ∀ᵐ ω ∂μ, τ ω ≠ ⊤ := by
      rw [ae_iff]; simpa using hfin
    filter_upwards [this] with ω hω
    change (ω ∈ {ω | τ ω ≠ ⊤} ∩ D) = (ω ∈ D)
    simp [hω]
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply (hG.prodMk (measurable_shiftAt hτm)) (hs.prod ht),
    Measure.map_apply hG hs, Set.mk_preimage_prod, ← hfin', ← hfin' (G ⁻¹' s), ← Set.inter_assoc]
  exact measure_inter_shiftAt_preimage ν hτ hτm (hG hs)
    (fun n ω ω' hn hag hω => by simpa [Set.mem_preimage, hGd n ω ω' hn hag] using hω) ht

end StrongMarkov


/-! ### Visits to a state and rewards along the jump chain -/

section Chain

variable {σ : Type*}

/-- The jump chain at steps `≤ n` depends only on the first `n` steps. -/
theorem ctmcJumpChain_congr {n : ℕ} {ω ω' : ℕ → (σ → σ) × ℝ} (h : ∀ i < n, ω i = ω' i)
    (x : σ) : ∀ j ≤ n, ctmcJumpChain x ω j = ctmcJumpChain x ω' j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    simp only [ctmcJumpChain, ih (by omega), h j (by omega)]

variable [DecidableEq σ]

/-- The number of visits to `x₀` of the jump chain started at `x` strictly before step `n`. -/
def nVisits (x₀ x : σ) (ω : ℕ → (σ → σ) × ℝ) (n : ℕ) : ℕ :=
  ∑ j ∈ range n, if ctmcJumpChain x ω j = x₀ then 1 else 0

theorem nVisits_zero (x₀ x : σ) (ω : ℕ → (σ → σ) × ℝ) : nVisits x₀ x ω 0 = 0 := by
  simp [nVisits]

theorem nVisits_succ (x₀ x : σ) (ω : ℕ → (σ → σ) × ℝ) (n : ℕ) :
    nVisits x₀ x ω (n + 1) = nVisits x₀ x ω n + if ctmcJumpChain x ω n = x₀ then 1 else 0 := by
  simp only [nVisits, sum_range_succ]

theorem nVisits_mono (x₀ x : σ) (ω : ℕ → (σ → σ) × ℝ) : Monotone (nVisits x₀ x ω) :=
  monotone_nat_of_le_succ fun n => by rw [nVisits_succ]; exact Nat.le_add_right _ _

/-- A visit at step `m < n` is counted by `nVisits _ _ _ n`. -/
theorem nVisits_lt_of_lt {x₀ x : σ} {ω : ℕ → (σ → σ) × ℝ} {m n : ℕ}
    (hm : ctmcJumpChain x ω m = x₀) (hmn : m < n) : nVisits x₀ x ω m < nVisits x₀ x ω n := by
  have h1 : nVisits x₀ x ω (m + 1) = nVisits x₀ x ω m + 1 := by simp [nVisits_succ, hm]
  have h2 := nVisits_mono x₀ x ω (show m + 1 ≤ n by omega)
  omega

theorem nVisits_congr {n : ℕ} {ω ω' : ℕ → (σ → σ) × ℝ} (x₀ x : σ)
    (h : ∀ j ≤ n, ctmcJumpChain x ω j = ctmcJumpChain x ω' j) :
    ∀ j ≤ n, nVisits x₀ x ω j = nVisits x₀ x ω' j := by
  intro j hj
  exact sum_congr rfl fun i hi => by rw [h i (by simp at hi; omega)]

/-- At most one step `n` is a visit with exactly `k` earlier visits. -/
theorem eq_of_visit {x₀ x : σ} {ω : ℕ → (σ → σ) × ℝ} {k m n : ℕ}
    (hm : ctmcJumpChain x ω m = x₀ ∧ nVisits x₀ x ω m = k)
    (hn : ctmcJumpChain x ω n = x₀ ∧ nVisits x₀ x ω n = k) : m = n := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := nVisits_lt_of_lt hm.1 h; omega
  · have := nVisits_lt_of_lt hn.1 h; omega

open scoped Classical in
/-- The **`k`-th visit** (counting from `0`) to `x₀` of the jump chain started at `x`: the step
`n` with `Y n = x₀` and exactly `k` visits before it; `⊤` if there are at most `k` visits. -/
noncomputable def visit (x₀ x : σ) (k : ℕ) (ω : ℕ → (σ → σ) × ℝ) : ℕ∞ :=
  if h : ∃ n, ctmcJumpChain x ω n = x₀ ∧ nVisits x₀ x ω n = k then (Nat.find h : ℕ∞) else ⊤

theorem visit_eq_iff {x₀ x : σ} {k : ℕ} {ω : ℕ → (σ → σ) × ℝ} {n : ℕ} :
    visit x₀ x k ω = n ↔ ctmcJumpChain x ω n = x₀ ∧ nVisits x₀ x ω n = k := by
  unfold visit
  split_ifs with h
  · rw [Nat.cast_inj]
    constructor
    · rintro rfl; exact Nat.find_spec h
    · intro hn; exact eq_of_visit (Nat.find_spec h) hn
  · simp only [ENat.top_ne_natCast, false_iff]
    exact fun hn => h ⟨n, hn⟩

theorem visit_ne_top_iff {x₀ x : σ} {k : ℕ} {ω : ℕ → (σ → σ) × ℝ} :
    visit x₀ x k ω ≠ ⊤ ↔ ∃ n, ctmcJumpChain x ω n = x₀ ∧ nVisits x₀ x ω n = k := by
  constructor
  · intro h
    exact ⟨(visit x₀ x k ω).toNat, visit_eq_iff.1 (ENat.natCast_toNat h).symm⟩
  · rintro ⟨n, hn⟩
    rw [visit_eq_iff.2 hn]
    exact ENat.natCast_ne_top n

theorem visit_self_zero (x₀ : σ) (ω : ℕ → (σ → σ) × ℝ) : visit x₀ x₀ 0 ω = 0 := by
  rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, visit_eq_iff]
  exact ⟨rfl, nVisits_zero _ _ _⟩

/-- Each visit time is a stopping time of the step sequence. -/
theorem isStepStoppingTime_visit (x₀ x : σ) (k : ℕ) : IsStepStoppingTime (visit x₀ x k) := by
  intro n ω ω' h hag
  rw [visit_eq_iff] at h ⊢
  have hY := ctmcJumpChain_congr hag x
  rw [← hY n le_rfl, ← nVisits_congr x₀ x hY n le_rfl]
  exact h

/-- If more than `k` visits happen before step `n`, the `k`-th visit happens before `n`. -/
theorem exists_visit_lt_of_lt_nVisits {x₀ x : σ} {ω : ℕ → (σ → σ) × ℝ} {k n : ℕ}
    (h : k < nVisits x₀ x ω n) : ∃ m < n, visit x₀ x k ω = m := by
  classical
  have hex : ∃ p, k + 1 ≤ nVisits x₀ x ω p := ⟨n, h⟩
  have hpn : Nat.find hex ≤ n := Nat.find_min' hex h
  have hp1 : k + 1 ≤ nVisits x₀ x ω (Nat.find hex) := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h0; rw [h0, nVisits_zero] at hp1; omega
  obtain ⟨p', hp'⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hlt : nVisits x₀ x ω p' < k + 1 := by
    by_contra hc
    exact (Nat.find_min hex (show p' < Nat.find hex by omega)) (by omega)
  rw [hp', nVisits_succ] at hp1
  have hY : ctmcJumpChain x ω p' = x₀ := by
    by_contra hY
    simp [hY] at hp1
    omega
  simp only [hY, ite_true] at hp1
  exact ⟨p', by omega, visit_eq_iff.2 ⟨hY, by omega⟩⟩

/-- If the `k`-th visit happens at step `n`, then all earlier visits happen by step `n`. -/
theorem visit_le_of_visit_eq {x₀ x : σ} {k : ℕ} {ω : ℕ → (σ → σ) × ℝ} {n : ℕ}
    (h : visit x₀ x k ω = n) {j : ℕ} (hj : j ≤ k) :
    ∃ m ≤ n, visit x₀ x j ω = m := by
  rw [visit_eq_iff] at h
  rcases hj.lt_or_eq with hj | rfl
  · obtain ⟨m, hm, hv⟩ := exists_visit_lt_of_lt_nVisits (x₀ := x₀) (x := x) (ω := ω)
      (show j < nVisits x₀ x ω n by omega)
    exact ⟨m, hm.le, hv⟩
  · exact ⟨n, le_rfl, visit_eq_iff.2 h⟩

/-- The first visit exists iff the chain ever visits `x₀`. -/
theorem visit_zero_ne_top_iff {x₀ x : σ} {ω : ℕ → (σ → σ) × ℝ} :
    visit x₀ x 0 ω ≠ ⊤ ↔ ∃ n, ctmcJumpChain x ω n = x₀ := by
  constructor
  · intro h
    obtain ⟨n, hn, -⟩ := visit_ne_top_iff.1 h
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    obtain ⟨m, -, hm⟩ := exists_visit_lt_of_lt_nVisits (x₀ := x₀) (x := x) (ω := ω) (k := 0)
      (n := n + 1) (by rw [nVisits_succ]; simp [hn])
    rw [hm]
    exact ENat.natCast_ne_top m

/-- From `x₀`, the first return exists iff the chain revisits `x₀` after step `0`. -/
theorem visit_self_one_ne_top_iff {x₀ : σ} {ω : ℕ → (σ → σ) × ℝ} :
    visit x₀ x₀ 1 ω ≠ ⊤ ↔ ∃ n, ctmcJumpChain x₀ ω (n + 1) = x₀ := by
  constructor
  · intro h
    obtain ⟨m, hm, hc⟩ := visit_ne_top_iff.1 h
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := by
      rcases m with _ | n
      · rw [nVisits_zero] at hc; omega
      · exact ⟨n, rfl⟩
    exact ⟨n, hm⟩
  · rintro ⟨n, hn⟩
    have h1 : 1 ≤ nVisits x₀ x₀ ω (n + 1) := by
      have := nVisits_mono x₀ x₀ ω (show 1 ≤ n + 1 by omega)
      rw [nVisits_succ, nVisits_zero] at this
      simpa [ctmcJumpChain] using this
    obtain ⟨m, -, hm⟩ := exists_visit_lt_of_lt_nVisits (x₀ := x₀) (x := x₀) (ω := ω) (k := 1)
      (n := n + 2) (by rw [nVisits_succ]; simp [hn]; omega)
    rw [hm]
    exact ENat.natCast_ne_top m

/-- Within the first excursion from `x₀`, only step `0` is at `x₀`. -/
theorem ctmcJumpChain_ne_of_lt_visit_one {x₀ : σ} {ω : ℕ → (σ → σ) × ℝ} {m : ℕ}
    (h : visit x₀ x₀ 1 ω = m) {i : ℕ} (hi0 : 0 < i) (him : i < m) :
    ctmcJumpChain x₀ ω i ≠ x₀ := by
  intro hY
  rw [visit_eq_iff] at h
  have h1 := nVisits_lt_of_lt hY him
  have h2 := nVisits_mono x₀ x₀ ω (show 1 ≤ i by omega)
  rw [nVisits_succ, nVisits_zero] at h2
  simp [ctmcJumpChain] at h2
  omega

/-- After a visit at step `n`, the visit counts split into those before `n` and those of the
chain restarted at `x₀` with the shifted steps. -/
theorem nVisits_add {x₀ x : σ} {ω : ℕ → (σ → σ) × ℝ} {n : ℕ}
    (h : ctmcJumpChain x ω n = x₀) (i : ℕ) :
    nVisits x₀ x ω (n + i) = nVisits x₀ x ω n + nVisits x₀ x₀ (ctmcShift n ω) i := by
  induction i with
  | zero => simp [nVisits_zero]
  | succ i ih =>
    rw [← add_assoc, nVisits_succ, ih, nVisits_succ, add_assoc, ← h, ctmcJumpChain_shift]

omit [DecidableEq σ] in
theorem ctmcJumpChain_add {x₀ x : σ} {ω : ℕ → (σ → σ) × ℝ} {n : ℕ}
    (h : ctmcJumpChain x ω n = x₀) (i : ℕ) :
    ctmcJumpChain x ω (n + i) = ctmcJumpChain x₀ (ctmcShift n ω) i := by
  rw [← h, ctmcJumpChain_shift]

/-- **Visits after a visit.** If the `k`-th visit is at step `n`, the `(k + j)`-th visit is `n`
plus the `j`-th visit of the chain restarted at `x₀` with the shifted steps. -/
theorem visit_add {x₀ x : σ} {k : ℕ} {ω : ℕ → (σ → σ) × ℝ} {n : ℕ}
    (h : visit x₀ x k ω = n) (j : ℕ) :
    visit x₀ x (k + j) ω = n + visit x₀ x₀ j (ctmcShift n ω) := by
  rw [visit_eq_iff] at h
  by_cases hv : visit x₀ x₀ j (ctmcShift n ω) = ⊤
  · rw [hv, add_top]
    by_contra hne
    obtain ⟨p, hp⟩ := visit_ne_top_iff.1 hne
    rcases lt_or_ge p n with hpn | hpn
    · have := nVisits_lt_of_lt hp.1 hpn
      omega
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hpn
      refine (visit_ne_top_iff.2 ⟨m, ?_, ?_⟩) hv
      · rw [← ctmcJumpChain_add h.1]; exact hp.1
      · have := nVisits_add h.1 m
        omega
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, visit x₀ x₀ j (ctmcShift n ω) = m :=
      ⟨_, (ENat.natCast_toNat hv).symm⟩
    rw [hm, ← Nat.cast_add, visit_eq_iff]
    rw [visit_eq_iff] at hm
    refine ⟨by rw [ctmcJumpChain_add h.1]; exact hm.1, ?_⟩
    rw [nVisits_add h.1, h.2, hm.2]

/-- The reward `∑_{i < m} g(Y_i) H_i` collected by the observable `g` during the first `m`
holding intervals of the chain started at `x`, with holding times `H_i = E_i / q(Y_i)`. For
`g = 1` it is the jump time `T_m`. -/
noncomputable def reward (q g : σ → ℝ) (x : σ) (ω : ℕ → (σ → σ) × ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ range m, g (ctmcJumpChain x ω i) * JumpHold.holdingTime q x ω i

omit [DecidableEq σ] in
theorem reward_one (q : σ → ℝ) (x : σ) (ω : ℕ → (σ → σ) × ℝ) (m : ℕ) :
    reward q (fun _ => 1) x ω m = JumpHold.jumpTime q x ω m := by
  simp [reward, JumpHold.jumpTime]

omit [DecidableEq σ] in
/-- After a visit to `x₀` at step `n`, rewards split into those before `n` and those of the chain
restarted at `x₀` with the shifted steps. -/
theorem reward_add (q g : σ → ℝ) {x₀ x : σ} {ω : ℕ → (σ → σ) × ℝ} {n : ℕ}
    (h : ctmcJumpChain x ω n = x₀) (i : ℕ) :
    reward q g x ω (n + i) = reward q g x ω n + reward q g x₀ (ctmcShift n ω) i := by
  simp only [reward, sum_range_add, JumpHold.holdingTime, ctmcJumpChain_add h]
  rfl

omit [DecidableEq σ] in
/-- The reward up to step `m ≤ n` depends only on the first `n` steps. -/
theorem reward_congr (q g : σ → ℝ) (x : σ) {n : ℕ} {ω ω' : ℕ → (σ → σ) × ℝ}
    (h : ∀ i < n, ω i = ω' i) {m : ℕ} (hm : m ≤ n) :
    reward q g x ω m = reward q g x ω' m := by
  have hY := ctmcJumpChain_congr h x
  refine sum_congr rfl fun i hi => ?_
  have hi' : i < n := by simp at hi; omega
  simp only [JumpHold.holdingTime, hY i hi'.le, h i hi']

/-- The reward collected by `g` during the first excursion of the chain started at `x₀`, up to
its first return to `x₀` (all steps if it never returns). -/
noncomputable def returnReward (q g : σ → ℝ) (x₀ : σ) (ω : ℕ → (σ → σ) × ℝ) : ℝ :=
  reward q g x₀ ω (visit x₀ x₀ 1 ω).toNat

/-- The reward collected by `g` during the `k`-th **regeneration cycle** of the chain started at
`x`, from its `k`-th to its `(k + 1)`-st visit to `x₀`. For `g = 1` it is the cycle length. -/
noncomputable def cycleSum (q g : σ → ℝ) (x₀ x : σ) (k : ℕ) (ω : ℕ → (σ → σ) × ℝ) : ℝ :=
  reward q g x ω (visit x₀ x (k + 1) ω).toNat - reward q g x ω (visit x₀ x k ω).toNat

/-- Each regeneration cycle is the first excursion from `x₀` of the shifted steps. -/
theorem cycleSum_eq (q g : σ → ℝ) {x₀ x : σ} {k : ℕ} {ω : ℕ → (σ → σ) × ℝ} {n : ℕ}
    (h : visit x₀ x k ω = n) (h1 : visit x₀ x (k + 1) ω ≠ ⊤) :
    cycleSum q g x₀ x k ω = returnReward q g x₀ (shiftAt (visit x₀ x k) ω) := by
  have hadd := visit_add h 1
  have hY := (visit_eq_iff.1 h).1
  have hshift : shiftAt (visit x₀ x k) ω = ctmcShift n ω := by
    simp [shiftAt, h, ENat.toNat_natCast]
  rw [hshift, returnReward]
  rw [hadd] at h1
  have h1' : visit x₀ x₀ 1 (ctmcShift n ω) ≠ ⊤ := fun ht => h1 (by rw [ht, add_top])
  obtain ⟨m, hm⟩ : ∃ m : ℕ, visit x₀ x₀ 1 (ctmcShift n ω) = m :=
    ⟨_, (ENat.natCast_toNat h1').symm⟩
  rw [cycleSum, hadd, hm, h, ← Nat.cast_add, ENat.toNat_natCast, ENat.toNat_natCast,
    ENat.toNat_natCast, reward_add q g hY]
  ring

/-- An earlier regeneration cycle is determined before a later visit. -/
theorem cycleSum_congr (q g : σ → ℝ) {x₀ x : σ} {j k : ℕ} (hjk : j < k) {n : ℕ}
    {ω ω' : ℕ → (σ → σ) × ℝ} (h : visit x₀ x k ω = n) (hag : ∀ i < n, ω i = ω' i) :
    cycleSum q g x₀ x j ω = cycleSum q g x₀ x j ω' := by
  obtain ⟨a, ha, hva⟩ := visit_le_of_visit_eq h (show j ≤ k by omega)
  obtain ⟨b, hb, hvb⟩ := visit_le_of_visit_eq h (show j + 1 ≤ k by omega)
  have hva' := isStepStoppingTime_visit x₀ x j a ω ω' hva fun i hi => hag i (by omega)
  have hvb' := isStepStoppingTime_visit x₀ x (j + 1) b ω ω' hvb fun i hi => hag i (by omega)
  simp only [cycleSum, hva, hvb, hva', hvb', ENat.toNat_natCast]
  rw [reward_congr q g x hag ha, reward_congr q g x hag hb]

section Measurability

variable [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ]

omit [DecidableEq σ] in
theorem measurable_jumpChain (x : σ) (n : ℕ) :
    Measurable fun ω : ℕ → (σ → σ) × ℝ => ctmcJumpChain x ω n := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have h : Measurable fun p : σ × (ℕ → (σ → σ) × ℝ) => (p.2 n).1 p.1 :=
      measurable_from_prod_countable_right fun y =>
        (measurable_pi_apply y).comp (measurable_pi_apply n).fst
    exact h.comp (ih.prodMk measurable_id)

omit [DecidableEq σ] in
/-- A set determined by the first `n + 1` states of the jump chain is measurable. -/
theorem measurableSet_of_jumpChain (x : σ) (n : ℕ) {A : Set (ℕ → (σ → σ) × ℝ)}
    (hA : ∀ ω ω', (∀ j ≤ n, ctmcJumpChain x ω j = ctmcJumpChain x ω' j) → ω ∈ A → ω' ∈ A) :
    MeasurableSet A := by
  let Φ : (ℕ → (σ → σ) × ℝ) → (Fin (n + 1) → σ) := fun ω j => ctmcJumpChain x ω j
  have hΦ : Measurable Φ := Measurable.of_eval fun j => measurable_jumpChain x j
  have hA' : A = Φ ⁻¹' (Φ '' A) := by
    ext ω
    constructor
    · intro h; exact ⟨ω, h, rfl⟩
    · rintro ⟨ω', hω', hΦω⟩
      refine hA ω' ω (fun j hj => ?_) hω'
      have := congrFun hΦω ⟨j, by omega⟩
      simpa [Φ] using this
  rw [hA']
  exact hΦ (Set.to_countable _).measurableSet

theorem measurable_visit (x₀ x : σ) (k : ℕ) : Measurable (visit x₀ x k) := by
  refine ENat.measurable_iff.2 fun n => measurableSet_of_jumpChain x n fun ω ω' h hω => ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω ⊢
  rw [visit_eq_iff] at hω ⊢
  rw [← h n le_rfl, ← nVisits_congr x₀ x h n le_rfl]
  exact hω

omit [DecidableEq σ] in
theorem measurable_reward (q g : σ → ℝ) (x : σ) (m : ℕ) :
    Measurable fun ω => reward q g x ω m :=
  Finset.measurable_sum _ fun i _ =>
    ((measurable_of_countable g).comp (measurable_jumpChain x i)).mul
      (((measurable_pi_apply i).snd).div ((measurable_of_countable q).comp
        (measurable_jumpChain x i)))

omit [DecidableEq σ] in
theorem measurable_reward_comp (q g : σ → ℝ) (x : σ) {N : (ℕ → (σ → σ) × ℝ) → ℕ}
    (hN : Measurable N) : Measurable fun ω => reward q g x ω (N ω) := by
  have h : Measurable fun p : ℕ × (ℕ → (σ → σ) × ℝ) => reward q g x p.2 p.1 :=
    measurable_from_prod_countable_right fun m => measurable_reward q g x m
  exact h.comp (hN.prodMk measurable_id)

theorem measurable_returnReward (q g : σ → ℝ) (x₀ : σ) : Measurable (returnReward q g x₀) :=
  measurable_reward_comp q g x₀ ((measurable_of_countable _).comp (measurable_visit x₀ x₀ 1))

theorem measurable_cycleSum (q g : σ → ℝ) (x₀ x : σ) (k : ℕ) :
    Measurable (cycleSum q g x₀ x k) :=
  (measurable_reward_comp q g x ((measurable_of_countable _).comp
    (measurable_visit x₀ x (k + 1)))).sub
    (measurable_reward_comp q g x ((measurable_of_countable _).comp (measurable_visit x₀ x k)))

end Measurability

end Chain

/-! ### The resolvent identity: the stationary law in Laplace form -/

section Resolvent

variable {σ : Type*}

theorem holdingTime_succ_eq (q : σ → ℝ) (x : σ) (ω : ℕ → (σ → σ) × ℝ) (k : ℕ) :
    JumpHold.holdingTime q x ω (k + 1) =
      JumpHold.holdingTime q ((ω 0).1 x) (ctmcShift 1 ω) k := by
  simp only [JumpHold.holdingTime, JumpHold.ctmcJumpChain_succ_eq]
  rw [show ctmcShift 1 ω k = ω (k + 1) by simp [ctmcShift, Nat.add_comm]]

/-- The **Abel functional** of the jump–hold chain started at `x`:
`∑_k g(Y_k) e^{-a T_k} (1 - e^{-a H_k})`. For nonnegative clocks and jump times tending to `∞`
it is the Laplace transform `a ∫_0^∞ e^{-a t} g(X_t) dt` of the path
(`lintegral_exp_path_eq_abelSum`). -/
noncomputable def abelSum (q g : σ → ℝ) (a : ℝ) (x : σ) (ω : ℕ → (σ → σ) × ℝ) : ℝ≥0∞ :=
  ∑' k, ENNReal.ofReal (g (ctmcJumpChain x ω k)) *
    ENNReal.ofReal (Real.exp (-(a * JumpHold.jumpTime q x ω k)) *
      (1 - Real.exp (-(a * JumpHold.holdingTime q x ω k))))

/-- First-step decomposition of the Abel functional. -/
theorem abelSum_eq (q g : σ → ℝ) (a : ℝ) (x : σ) (ω : ℕ → (σ → σ) × ℝ) :
    abelSum q g a x ω =
      ENNReal.ofReal (g x) * ENNReal.ofReal (1 - Real.exp (-(a * ((ω 0).2 / q x)))) +
        ENNReal.ofReal (Real.exp (-(a * ((ω 0).2 / q x)))) *
          abelSum q g a ((ω 0).1 x) (ctmcShift 1 ω) := by
  conv_lhs => rw [abelSum, tsum_eq_zero_add' ENNReal.summable]
  congr 1
  · simp [ctmcJumpChain, JumpHold.jumpTime, JumpHold.holdingTime]
  · rw [abelSum, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [JumpHold.ctmcJumpChain_succ_eq, JumpHold.jumpTime_succ_eq, holdingTime_succ_eq, mul_add,
      neg_add, Real.exp_add, mul_assoc, ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring

/-- With nonnegative clocks and `0 ≤ g ≤ 1`, the Abel functional is at most `1` (the weights
`e^{-a T_k} - e^{-a T_{k+1}}` telescope). -/
theorem abelSum_le_one (q g : σ → ℝ) {a : ℝ} (ha : 0 ≤ a) (hq : ∀ x, 0 < q x)
    (hg1 : ∀ x, g x ≤ 1) (x : σ) {ω : ℕ → (σ → σ) × ℝ} (hE : ∀ k, 0 ≤ (ω k).2) :
    abelSum q g a x ω ≤ 1 := by
  set t : ℕ → ℝ := fun k => Real.exp (-(a * JumpHold.jumpTime q x ω k))
  have hH : ∀ k, 0 ≤ JumpHold.holdingTime q x ω k := fun k => div_nonneg (hE k) (hq _).le
  have hT : ∀ k, JumpHold.jumpTime q x ω (k + 1) =
      JumpHold.jumpTime q x ω k + JumpHold.holdingTime q x ω k := fun k => by
    simp [JumpHold.jumpTime, sum_range_succ]
  have hdec : ∀ k, t (k + 1) ≤ t k := fun k => by
    simp only [t, hT]
    exact Real.exp_le_exp.2 (by nlinarith [hH k])
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  have hterm : ∀ k, ENNReal.ofReal (g (ctmcJumpChain x ω k)) *
      ENNReal.ofReal (Real.exp (-(a * JumpHold.jumpTime q x ω k)) *
        (1 - Real.exp (-(a * JumpHold.holdingTime q x ω k)))) ≤
      ENNReal.ofReal (t k - t (k + 1)) := by
    intro k
    calc _ ≤ 1 * ENNReal.ofReal (Real.exp (-(a * JumpHold.jumpTime q x ω k)) *
          (1 - Real.exp (-(a * JumpHold.holdingTime q x ω k)))) :=
          mul_le_mul_left (ENNReal.ofReal_le_one.2 (hg1 _)) _
      _ = ENNReal.ofReal (t k - t (k + 1)) := by
          rw [one_mul]
          congr 1
          simp only [t, hT, mul_add, neg_add, Real.exp_add]
          ring
  calc ∑ k ∈ range n, _ ≤ ∑ k ∈ range n, ENNReal.ofReal (t k - t (k + 1)) :=
        sum_le_sum fun k _ => hterm k
    _ = ENNReal.ofReal (∑ k ∈ range n, (t k - t (k + 1))) :=
        (ENNReal.ofReal_sum_of_nonneg fun k _ => sub_nonneg.2 (hdec k)).symm
    _ = ENNReal.ofReal (t 0 - t n) := by rw [sum_range_sub']
    _ ≤ 1 := by
        refine ENNReal.ofReal_le_one.2 ?_
        have h0 : t 0 = 1 := by simp [t, JumpHold.jumpTime]
        have hn : 0 < t n := Real.exp_pos _
        linarith

variable [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ]

theorem measurable_holdingTime (q : σ → ℝ) (x : σ) (k : ℕ) :
    Measurable fun ω => JumpHold.holdingTime q x ω k :=
  ((measurable_pi_apply k).snd).div ((measurable_of_countable q).comp (measurable_jumpChain x k))

theorem measurable_jumpTime (q : σ → ℝ) (x : σ) (k : ℕ) :
    Measurable fun ω => JumpHold.jumpTime q x ω k :=
  Finset.measurable_sum _ fun i _ => measurable_holdingTime q x i

theorem measurable_abelSum (q g : σ → ℝ) (a : ℝ) (x : σ) : Measurable (abelSum q g a x) :=
  Measurable.tsum fun k =>
    (ENNReal.measurable_ofReal.comp ((measurable_of_countable g).comp
      (measurable_jumpChain x k))).mul (ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp ((measurable_jumpTime q x k).const_mul a).neg).mul
        (measurable_const.sub (Real.measurable_exp.comp
          ((measurable_holdingTime q x k).const_mul a).neg))))

/-- The clock `Exp(1)` is almost surely nonnegative. -/
theorem ae_nonneg_expMeasure_one : ∀ᵐ e ∂expMeasure 1, 0 ≤ e := by
  have h0 : expMeasure 1 (Set.Iio 0) = 0 := by
    rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
    refine (setLIntegral_congr_fun measurableSet_Iio fun x hx => gammaPDF_of_neg hx).trans ?_
    simp
  rw [ae_iff]
  simpa [Set.Iio, not_le] using h0

variable (K : σ → PMF σ)

/-- **First-step equation for the Abel functional** (the resolvent equation of the chain):
`E_x[A] = g(x) a / (q(x) + a) + q(x) / (q(x) + a) ∑_y K(x, y) E_y[A]`. -/
theorem lintegral_abelSum (q g : σ → ℝ) (hq : ∀ x, 0 < q x) {a : ℝ} (ha : 0 ≤ a) (x : σ) :
    ∫⁻ ω, abelSum q g a x ω ∂JumpHold.inputMeasure K =
      ENNReal.ofReal (g x) * ENNReal.ofReal (a / (q x + a)) +
        ENNReal.ofReal (q x / (q x + a)) *
          ∑' y, K x y * ∫⁻ ω, abelSum q g a y ω ∂JumpHold.inputMeasure K := by
  set μ := JumpHold.inputMeasure K
  set A : σ → ℝ≥0∞ := fun y => ∫⁻ ω, abelSum q g a y ω ∂μ with hAdef
  set e : ℝ → ℝ := fun E => Real.exp (-(a * (E / q x))) with hedef
  have hqx := hq x
  have he : Measurable e := Real.measurable_exp.comp ((measurable_id.div_const _).const_mul a).neg
  have habm : Measurable fun p : σ × (ℕ → (σ → σ) × ℝ) => abelSum q g a p.1 p.2 :=
    measurable_from_prod_countable_right fun y => measurable_abelSum q g a y
  set F : ((σ → σ) × ℝ) × (ℕ → (σ → σ) × ℝ) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (g x) * ENNReal.ofReal (1 - e p.1.2) +
      ENNReal.ofReal (e p.1.2) * abelSum q g a (p.1.1 x) p.2 with hFdef
  have hF : Measurable F := by
    refine (measurable_const.mul (ENNReal.measurable_ofReal.comp
      (measurable_const.sub (he.comp measurable_fst.snd)))).add
      ((ENNReal.measurable_ofReal.comp (he.comp measurable_fst.snd)).mul ?_)
    have hpx : Measurable fun p : ((σ → σ) × ℝ) × (ℕ → (σ → σ) × ℝ) => (p.1.1 x, p.2) :=
      ((measurable_pi_apply x).comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd
    exact habm.comp hpx
  have hmf : Measurable fun ω : ℕ → (σ → σ) × ℝ => (ω 0, ctmcShift 1 ω) :=
    (measurable_pi_apply 0).prodMk (measurable_ctmcShift_pi 1)
  have h1 : ∫⁻ ω, abelSum q g a x ω ∂μ = ∫⁻ p, F p ∂((JumpHold.stepMeasure K).prod μ) := by
    rw [← JumpHold.inputMeasure_map_first, lintegral_map hF hmf]
    exact lintegral_congr fun ω => abelSum_eq q g a x ω
  have h2 : ∀ s : (σ → σ) × ℝ, ∫⁻ ω', F (s, ω') ∂μ =
      ENNReal.ofReal (g x) * ENNReal.ofReal (1 - e s.2) + ENNReal.ofReal (e s.2) * A (s.1 x) := by
    intro s
    simp only [hFdef]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul _ (measurable_abelSum q g a _)]
  rw [h1, lintegral_prod _ hF.aemeasurable]
  have h3 : ∫⁻ s, ∫⁻ ω', F (s, ω') ∂μ ∂(JumpHold.stepMeasure K) = ∫⁻ s,
      (ENNReal.ofReal (g x) * ENNReal.ofReal (1 - e s.2) + ENNReal.ofReal (e s.2) * A (s.1 x))
        ∂(JumpHold.stepMeasure K) := lintegral_congr h2
  rw [h3]
  have hb : 0 ≤ a / q x := div_nonneg ha hqx.le
  have hexp : ∫⁻ E, ENNReal.ofReal (e E) ∂expMeasure 1 = ENNReal.ofReal (q x / (q x + a)) := by
    have := JumpHold.lintegral_exp_neg_mul_expMeasure_one hb
    have hfun : (fun E => ENNReal.ofReal (e E)) =
        fun E => ENNReal.ofReal (Real.exp (-(a / q x * E))) := by
      funext E; simp only [hedef]; congr 3; ring
    rw [hfun, this]
    congr 1
    field_simp
  have hone : ∫⁻ E, ENNReal.ofReal (1 - e E) ∂expMeasure 1 = ENNReal.ofReal (a / (q x + a)) := by
    have hle : (fun E => ENNReal.ofReal (e E)) ≤ᵐ[expMeasure 1] fun _ => 1 := by
      filter_upwards [ae_nonneg_expMeasure_one] with E hE
      refine ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 ?_)
      have : 0 ≤ a * (E / q x) := mul_nonneg ha (div_nonneg hE hqx.le)
      linarith
    have hprob : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
    have hsub : (fun E => ENNReal.ofReal (1 - e E)) = fun E => 1 - ENNReal.ofReal (e E) :=
      funext fun E => by
        rw [ENNReal.ofReal_sub 1 (by simp only [hedef]; positivity), ENNReal.ofReal_one]
    have hme : Measurable fun E => ENNReal.ofReal (e E) := ENNReal.measurable_ofReal.comp he
    rw [hsub, lintegral_sub hme (by rw [hexp]; exact ENNReal.ofReal_ne_top) hle, lintegral_const,
      measure_univ, mul_one, hexp, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (by positivity)]
    congr 1
    field_simp
    ring
  have hevalx : ∫⁻ ξ, A (ξ x) ∂(Measure.infinitePi fun y => (K y).toMeasure) =
      ∑' y, K x y * A y := by
    rw [← lintegral_map (measurable_of_countable A) (measurable_pi_apply x),
      Measure.infinitePi_map_eval, lintegral_countable']
    refine tsum_congr fun y => ?_
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y), mul_comm]
  have hprob : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  rw [JumpHold.stepMeasure, lintegral_add_left
    (f := fun s : (σ → σ) × ℝ => ENNReal.ofReal (g x) * ENNReal.ofReal (1 - e s.2))
    (measurable_const.mul (ENNReal.measurable_ofReal.comp
      (measurable_const.sub (he.comp measurable_snd))))]
  have hp1 : ∫⁻ s : (σ → σ) × ℝ, ENNReal.ofReal (g x) * ENNReal.ofReal (1 - e s.2)
      ∂(Measure.infinitePi fun y => (K y).toMeasure).prod (expMeasure 1) =
      ENNReal.ofReal (g x) * ENNReal.ofReal (a / (q x + a)) := by
    have hm1 : Measurable fun s : (σ → σ) × ℝ => ENNReal.ofReal (1 - e s.2) :=
      ENNReal.measurable_ofReal.comp (measurable_const.sub (he.comp measurable_snd))
    have hm1' : Measurable fun E : ℝ => ENNReal.ofReal (1 - e E) :=
      ENNReal.measurable_ofReal.comp (measurable_const.sub he)
    rw [lintegral_const_mul _ hm1, ← hone]
    have := lintegral_prod_mul (μ := Measure.infinitePi fun y => (K y).toMeasure)
      (ν := expMeasure 1) (f := fun _ => 1) (g := fun E => ENNReal.ofReal (1 - e E))
      aemeasurable_const hm1'.aemeasurable
    simp only [one_mul, lintegral_const, measure_univ, mul_one] at this
    rw [this]
  have hp2 : ∫⁻ s : (σ → σ) × ℝ, ENNReal.ofReal (e s.2) * A (s.1 x)
      ∂(Measure.infinitePi fun y => (K y).toMeasure).prod (expMeasure 1) =
      ENNReal.ofReal (q x / (q x + a)) * ∑' y, K x y * A y := by
    have := lintegral_prod_mul (μ := Measure.infinitePi fun y => (K y).toMeasure)
      (ν := expMeasure 1) (f := fun ξ => A (ξ x)) (g := fun E => ENNReal.ofReal (e E))
      ((measurable_of_countable A).comp (measurable_pi_apply x)).aemeasurable
      (ENNReal.measurable_ofReal.comp he).aemeasurable
    rw [show (fun s : (σ → σ) × ℝ => ENNReal.ofReal (e s.2) * A (s.1 x)) =
      fun s => A (s.1 x) * ENNReal.ofReal (e s.2) from funext fun s => mul_comm _ _, this,
      hevalx, hexp, mul_comm]
  rw [hp1, hp2]

/-- **Resolvent identity** (stationarity of a balanced law in Laplace form). Let the weights `w`
balance the rate-weighted jump kernel, `∑_x w(x) q(x) K(x, y) = w(y) q(y)` (the stationary
master equation `w Q = 0`), with `∑_x w(x) q(x) < ∞`. Then for every `a > 0` and `0 ≤ g ≤ 1`,
`∑_x w(x) E_x[A_a g] = ∑_x w(x) g(x)`, where `A_a g` is the Abel functional
`a ∫_0^∞ e^{-a t} g(X_t) dt`. -/
theorem tsum_mul_lintegral_abelSum (q g : σ → ℝ) (hq : ∀ x, 0 < q x) (hg1 : ∀ x, g x ≤ 1)
    {a : ℝ} (ha : 0 < a) (w : σ → ℝ≥0∞)
    (hbal : ∀ y, ∑' x, w x * ENNReal.ofReal (q x) * K x y = w y * ENNReal.ofReal (q y))
    (hfin : ∑' x, w x * ENNReal.ofReal (q x) ≠ ⊤) :
    ∑' x, w x * ∫⁻ ω, abelSum q g a x ω ∂JumpHold.inputMeasure K =
      ∑' x, w x * ENNReal.ofReal (g x) := by
  set μ := JumpHold.inputMeasure K
  set A : σ → ℝ≥0∞ := fun y => ∫⁻ ω, abelSum q g a y ω ∂μ with hAdef
  have hA1 : ∀ x, A x ≤ 1 := by
    intro x
    calc A x ≤ ∫⁻ _, 1 ∂μ := lintegral_mono_ae (by
          filter_upwards [JumpHold.ae_clock_nonneg K] with ω hω
          exact abelSum_le_one q g ha.le hq hg1 x hω)
      _ = 1 := by simp
  have hcoef : ∀ x, ENNReal.ofReal (q x + a) * ENNReal.ofReal (a / (q x + a)) = ENNReal.ofReal a ∧
      ENNReal.ofReal (q x + a) * ENNReal.ofReal (q x / (q x + a)) = ENNReal.ofReal (q x) := by
    intro x
    have hqa : 0 < q x + a := by linarith [hq x]
    rw [← ENNReal.ofReal_mul hqa.le, ← ENNReal.ofReal_mul hqa.le]
    constructor <;> congr 1 <;> field_simp
  have key : ∀ x, (ENNReal.ofReal (q x) + ENNReal.ofReal a) * A x =
      ENNReal.ofReal a * ENNReal.ofReal (g x) + ENNReal.ofReal (q x) * ∑' y, K x y * A y := by
    intro x
    simp only [hAdef]
    rw [lintegral_abelSum K q g hq ha.le x, ← ENNReal.ofReal_add (hq x).le ha.le, mul_add,
      mul_left_comm, (hcoef x).1, ← mul_assoc, (hcoef x).2, mul_comm (ENNReal.ofReal a)]
  have hsum : ∑' x, w x * ((ENNReal.ofReal (q x) + ENNReal.ofReal a) * A x) =
      ∑' x, w x * (ENNReal.ofReal a * ENNReal.ofReal (g x) +
        ENNReal.ofReal (q x) * ∑' y, K x y * A y) := tsum_congr fun x => by rw [key x]
  have hL : ∑' x, w x * ((ENNReal.ofReal (q x) + ENNReal.ofReal a) * A x) =
      (∑' x, w x * ENNReal.ofReal (q x) * A x) + ENNReal.ofReal a * ∑' x, w x * A x := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    exact tsum_congr fun x => by ring
  have h2 : ∑' x, w x * (ENNReal.ofReal (q x) * ∑' y, K x y * A y) =
      ∑' y, w y * ENNReal.ofReal (q y) * A y := by
    calc ∑' x, w x * (ENNReal.ofReal (q x) * ∑' y, K x y * A y)
        = ∑' x, ∑' y, w x * ENNReal.ofReal (q x) * K x y * A y := by
          refine tsum_congr fun x => ?_
          rw [← mul_assoc, ← ENNReal.tsum_mul_left]
          exact tsum_congr fun y => by ring
      _ = ∑' y, ∑' x, w x * ENNReal.ofReal (q x) * K x y * A y := ENNReal.tsum_comm
      _ = ∑' y, w y * ENNReal.ofReal (q y) * A y := by
          refine tsum_congr fun y => ?_
          rw [ENNReal.tsum_mul_right, hbal]
  have hR : ∑' x, w x * (ENNReal.ofReal a * ENNReal.ofReal (g x) +
      ENNReal.ofReal (q x) * ∑' y, K x y * A y) =
      ENNReal.ofReal a * (∑' x, w x * ENNReal.ofReal (g x)) +
        ∑' x, w x * ENNReal.ofReal (q x) * A x := by
    calc _ = ∑' x, (ENNReal.ofReal a * (w x * ENNReal.ofReal (g x)) +
          w x * (ENNReal.ofReal (q x) * ∑' y, K x y * A y)) := tsum_congr fun x => by ring
      _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, h2]
  have hX : ∑' x, w x * ENNReal.ofReal (q x) * A x ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum fun x => ?_)
    calc w x * ENNReal.ofReal (q x) * A x ≤ w x * ENNReal.ofReal (q x) * 1 :=
          mul_le_mul_right (hA1 x) _
      _ = w x * ENNReal.ofReal (q x) := mul_one _
  rw [hL, hR, add_comm] at hsum
  have := (ENNReal.add_left_inj hX).1 hsum
  exact (ENNReal.mul_right_inj (by simpa using ha) ENNReal.ofReal_ne_top).1 this

end Resolvent

/-! ### The path: occupation integrals and Laplace transforms -/

section Pathwise

variable {σ : Type*} {q : σ → ℝ} {x : σ} {ω : ℕ → (σ → σ) × ℝ}

theorem jumpTime_zero : JumpHold.jumpTime q x ω 0 = 0 := by simp [JumpHold.jumpTime]

theorem jumpTime_succ (k : ℕ) :
    JumpHold.jumpTime q x ω (k + 1) =
      JumpHold.jumpTime q x ω k + JumpHold.holdingTime q x ω k := by
  simp [JumpHold.jumpTime, sum_range_succ]

theorem jumpTime_mono (hq : ∀ y, 0 < q y) (hE : ∀ k, 0 ≤ (ω k).2) :
    Monotone (JumpHold.jumpTime q x ω) :=
  monotone_nat_of_le_succ fun k => by
    rw [jumpTime_succ]
    have : 0 ≤ JumpHold.holdingTime q x ω k := div_nonneg (hE k) (hq _).le
    linarith

theorem exists_jumpTime_le_lt (hT : Tendsto (JumpHold.jumpTime q x ω) atTop atTop) {s : ℝ}
    (hs : 0 ≤ s) :
    ∃ k, JumpHold.jumpTime q x ω k ≤ s ∧ s < JumpHold.jumpTime q x ω (k + 1) := by
  classical
  have hex : ∃ n, s < JumpHold.jumpTime q x ω n := (hT.eventually_gt_atTop s).exists
  have hne : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, jumpTime_zero] at this
    linarith
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
  refine ⟨k, not_lt.1 (Nat.find_min hex (show k < Nat.find hex by omega)), ?_⟩
  rw [show k + 1 = Nat.find hex by omega]
  exact Nat.find_spec hex

/-- Before time `0` the path is at its initial state. -/
theorem path_of_neg {s : ℝ} (hs : s < 0) : JumpHold.path q x ω s = x := by
  classical
  have h : ∃ n, s < JumpHold.jumpTime q x ω n := ⟨0, by rw [jumpTime_zero]; exact hs⟩
  rw [JumpHold.path, dite_eq_left h,
    show Nat.find h = 0 from (Nat.find_eq_zero h).2 (by rw [jumpTime_zero]; exact hs)]
  rfl

theorem measurable_path [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ]
    (hq : ∀ y, 0 < q y) (hE : ∀ k, 0 ≤ (ω k).2)
    (hT : Tendsto (JumpHold.jumpTime q x ω) atTop atTop) :
    Measurable fun s => JumpHold.path q x ω s := by
  refine measurable_to_countable' fun y => ?_
  have hset : (fun s => JumpHold.path q x ω s) ⁻¹' {y} =
      ({s : ℝ | s < 0} ∩ {_s | x = y}) ∪ ⋃ k, ({s | JumpHold.jumpTime q x ω k ≤ s} ∩
        ({s | s < JumpHold.jumpTime q x ω (k + 1)} ∩ {_s | ctmcJumpChain x ω k = y})) := by
    ext s
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hs
      rcases lt_or_ge s 0 with h | h
      · exact Or.inl ⟨h, (path_of_neg (q := q) (ω := ω) h).symm.trans hs⟩
      · obtain ⟨k, hk1, hk2⟩ := exists_jumpTime_le_lt hT h
        exact Or.inr ⟨k, hk1, hk2, by rw [← JumpHold.path_eq_ctmcJumpChain hq hE hk1 hk2]; exact hs⟩
    · rintro (⟨h, rfl⟩ | ⟨k, hk1, hk2, rfl⟩)
      · exact path_of_neg h
      · exact JumpHold.path_eq_ctmcJumpChain hq hE hk1 hk2
  rw [hset]
  refine ((measurableSet_lt measurable_id measurable_const).inter (MeasurableSet.const _)).union
    (MeasurableSet.iUnion fun k => ?_)
  exact (measurableSet_le measurable_const measurable_id).inter
    ((measurableSet_lt measurable_id measurable_const).inter (MeasurableSet.const _))

theorem intervalIntegrable_path [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ]
    (hmeas : Measurable fun s => JumpHold.path q x ω s) {g : σ → ℝ} {B : ℝ}
    (hB : ∀ y, |g y| ≤ B) (u v : ℝ) :
    IntervalIntegrable (fun s => g (JumpHold.path q x ω s)) volume u v :=
  (intervalIntegrable_const (c := B)).mono_fun'
    ((measurable_of_countable g).comp hmeas).aestronglyMeasurable
    (ae_of_all _ fun s => by simpa [Real.norm_eq_abs] using hB _)

/-- The occupation integral of the path up to the `m`-th jump time is the reward
`∑_{k < m} g(Y_k) H_k`. -/
theorem integral_path_jumpTime [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ]
    (hq : ∀ y, 0 < q y) (hE : ∀ k, 0 ≤ (ω k).2)
    (hmeas : Measurable fun s => JumpHold.path q x ω s) {g : σ → ℝ} {B : ℝ}
    (hB : ∀ y, |g y| ≤ B) (m : ℕ) :
    ∫ s in (0 : ℝ)..JumpHold.jumpTime q x ω m, g (JumpHold.path q x ω s) = reward q g x ω m := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := JumpHold.jumpTime q x ω)
    (f := fun s => g (JumpHold.path q x ω s)) (μ := volume) (n := m)
    fun k _ => intervalIntegrable_path hmeas hB _ _
  rw [jumpTime_zero] at hsum
  rw [← hsum, reward]
  refine sum_congr rfl fun k _ => ?_
  have hle : JumpHold.jumpTime q x ω k ≤ JumpHold.jumpTime q x ω (k + 1) :=
    jumpTime_mono hq hE (Nat.le_succ k)
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ JumpHold.jumpTime q x ω (k + 1) := by
    rw [ae_iff]; simp
  rw [intervalIntegral.integral_congr_ae (g := fun _ => g (ctmcJumpChain x ω k)) ?_]
  · rw [intervalIntegral.integral_const, jumpTime_succ, smul_eq_mul]
    ring
  · filter_upwards [hne] with s hs hmem
    rw [Set.uIoc_of_le hle] at hmem
    exact congrArg g (JumpHold.path_eq_ctmcJumpChain hq hE hmem.1.le (lt_of_le_of_ne hmem.2 hs))

/-- The occupation integral of a bounded observable is Lipschitz in time. -/
theorem abs_integral_path_sub_le [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ]
    (hmeas : Measurable fun s => JumpHold.path q x ω s) {g : σ → ℝ} {B : ℝ}
    (hB : ∀ y, |g y| ≤ B) {s t : ℝ} (hst : s ≤ t) :
    |(∫ u in (0 : ℝ)..t, g (JumpHold.path q x ω u)) -
      ∫ u in (0 : ℝ)..s, g (JumpHold.path q x ω u)| ≤ B * (t - s) := by
  rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_path hmeas hB _ _)
    (intervalIntegrable_path hmeas hB _ _), ← Real.norm_eq_abs]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t) (C := B)
    (f := fun u => g (JumpHold.path q x ω u)) fun u _ => by
      simpa [Real.norm_eq_abs] using hB (JumpHold.path q x ω u)
  rwa [abs_of_nonneg (sub_nonneg.2 hst)] at this

theorem integral_mul_exp_neg_mul {a : ℝ} (ha : a ≠ 0) (u v : ℝ) :
    ∫ t in u..v, a * Real.exp (-(a * t)) = Real.exp (-(a * u)) - Real.exp (-(a * v)) := by
  have hfun : (fun t => Real.exp (-(a * t))) = fun t => Real.exp ((-a) * t) := by
    funext t; ring_nf
  rw [intervalIntegral.integral_const_mul, hfun,
    intervalIntegral.integral_comp_mul_left (f := Real.exp) (neg_ne_zero.2 ha), integral_exp,
    smul_eq_mul]
  field_simp
  ring_nf

/-- **The Abel functional is the Laplace transform of the path**: with nonnegative clocks and
jump times tending to `∞`, `∫_0^∞ a e^{-a t} g(X_t) dt = ∑_k g(Y_k) e^{-a T_k} (1 - e^{-a H_k})`. -/
theorem lintegral_exp_path_eq_abelSum (hq : ∀ y, 0 < q y) (hE : ∀ k, 0 ≤ (ω k).2)
    (hT : Tendsto (JumpHold.jumpTime q x ω) atTop atTop) {g : σ → ℝ} (hg0 : ∀ y, 0 ≤ g y)
    {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (a * Real.exp (-(a * t)) * g (JumpHold.path q x ω t)) =
      abelSum q g a x ω := by
  set T := JumpHold.jumpTime q x ω with hTdef
  have hmono := jumpTime_mono (x := x) hq hE
  have hcover : Set.Ici (0 : ℝ) = ⋃ k, Set.Ico (T k) (T (k + 1)) := by
    ext s
    simp only [Set.mem_Ici, Set.mem_iUnion, Set.mem_Ico]
    constructor
    · intro hs; exact exists_jumpTime_le_lt hT hs
    · rintro ⟨k, hk, -⟩
      have : 0 ≤ T k :=
        (jumpTime_zero (q := q) (x := x) (ω := ω)).symm.le.trans (hmono (Nat.zero_le k))
      linarith
  have hdisj : Pairwise (Function.onFun Disjoint fun k => Set.Ico (T k) (T (k + 1))) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun s hi hj => ?_
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · have := hmono (show i + 1 ≤ j by omega)
      linarith [hi.2, hj.1]
    · have := hmono (show j + 1 ≤ i by omega)
      linarith [hi.1, hj.2]
  rw [setLIntegral_congr Ioi_ae_eq_Ici, hcover, lintegral_iUnion (fun k => measurableSet_Ico) hdisj,
    abelSum]
  refine tsum_congr fun k => ?_
  have hpath : Set.EqOn (fun t => ENNReal.ofReal (a * Real.exp (-(a * t)) *
      g (JumpHold.path q x ω t)))
      (fun t => ENNReal.ofReal (g (ctmcJumpChain x ω k)) * ENNReal.ofReal (a * Real.exp (-(a * t))))
      (Set.Ico (T k) (T (k + 1))) := by
    intro t ht
    simp only
    rw [JumpHold.path_eq_ctmcJumpChain hq hE ht.1 ht.2, ← ENNReal.ofReal_mul (hg0 _), mul_comm]
  have hcont : Continuous fun t => a * Real.exp (-(a * t)) := by fun_prop
  have hme : Measurable fun t => ENNReal.ofReal (a * Real.exp (-(a * t))) :=
    ENNReal.measurable_ofReal.comp hcont.measurable
  rw [setLIntegral_congr_fun measurableSet_Ico hpath, lintegral_const_mul _ hme,
    ← ofReal_integral_eq_lintegral_ofReal
      ((hcont.integrableOn_Icc).mono_set Set.Ico_subset_Icc_self)
      (ae_of_all _ fun t => by positivity),
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hmono (Nat.le_succ k)),
    integral_mul_exp_neg_mul ha.ne', jumpTime_succ]
  congr 2
  rw [mul_add, neg_add, Real.exp_add]
  ring

/-- Real form of `lintegral_exp_path_eq_abelSum`. -/
theorem abelSum_toReal_eq [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ]
    (hq : ∀ y, 0 < q y) (hE : ∀ k, 0 ≤ (ω k).2)
    (hT : Tendsto (JumpHold.jumpTime q x ω) atTop atTop) {g : σ → ℝ} (hg0 : ∀ y, 0 ≤ g y)
    {a : ℝ} (ha : 0 < a) :
    (abelSum q g a x ω).toReal =
      a * ∫ t in Set.Ioi 0, Real.exp (-(a * t)) * g (JumpHold.path q x ω t) := by
  have hmeas := measurable_path hq hE hT
  rw [← lintegral_exp_path_eq_abelSum hq hE hT hg0 ha, ← integral_const_mul,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun t => by
      have := hg0 (JumpHold.path q x ω t); positivity)]
  · congr 1
    exact lintegral_congr fun t => by ring_nf
  · have hg : Measurable g := measurable_of_countable g
    exact Measurable.aestronglyMeasurable (by fun_prop)

end Pathwise

/-! ### An Abelian theorem: Cesàro limits are Abel limits -/

section Abelian


/-- `∫_t^∞ a² e^{-a r} dr = a e^{-a t}`. -/
theorem lintegral_Ici_sq_mul_exp {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ∫⁻ r in Set.Ici t, ENNReal.ofReal (a ^ 2 * Real.exp (-(a * r))) =
      ENNReal.ofReal (a * Real.exp (-(a * t))) := by
  have hfun : (fun r => a ^ 2 * Real.exp (-(a * r))) = fun r => a ^ 2 * Real.exp ((-a) * r) := by
    funext r; ring_nf
  have hint : IntegrableOn (fun r => a ^ 2 * Real.exp (-(a * r))) (Set.Ioi t) := by
    rw [hfun]; exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) t).const_mul _
  rw [← setLIntegral_congr Ioi_ae_eq_Ici, ← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun r => by positivity), hfun, integral_const_mul,
    integral_exp_mul_Ioi (neg_neg_of_pos ha)]
  congr 1
  field_simp

/-- **Abelian theorem.** If `0 ≤ h ≤ 1` is measurable and its Cesàro means
`t⁻¹ ∫_0^t h` converge to `L`, then its Abel means `a ∫_0^∞ e^{-a t} h(t) dt` converge to `L`
as `a → 0⁺`. -/
theorem tendsto_abel_of_tendsto_cesaro {h : ℝ → ℝ} (hm : Measurable h) (h0 : ∀ t, 0 ≤ h t)
    (h1 : ∀ t, h t ≤ 1) {L : ℝ}
    (hL : Tendsto (fun t => (∫ s in (0 : ℝ)..t, h s) / t) atTop (𝓝 L)) :
    Tendsto (fun a : ℝ => a * ∫ t in Set.Ioi 0, Real.exp (-(a * t)) * h t) (𝓝[>] 0) (𝓝 L) := by
  set F : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, h s with hFdef
  have hint : ∀ u v : ℝ, IntervalIntegrable h volume u v := fun u v =>
    (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' hm.aestronglyMeasurable
      (ae_of_all _ fun s => by simpa [Real.norm_eq_abs, abs_of_nonneg (h0 s)] using h1 s)
  have hFc : Continuous F := intervalIntegral.continuous_primitive hint 0
  have hF0 : ∀ t, 0 ≤ t → 0 ≤ F t := fun t ht =>
    intervalIntegral.integral_nonneg ht fun s _ => h0 s
  have hFt : ∀ t, 0 ≤ t → F t ≤ t := fun t ht => by
    have := intervalIntegral.integral_mono_on ht (hint 0 t) intervalIntegrable_const
      (fun s _ => h1 s)
    simpa using this
  set φ : ℝ → ℝ := fun t => F t / t with hφdef
  have hφm : Measurable φ := hFc.measurable.div measurable_id
  have hφ01 : ∀ t, 0 < t → 0 ≤ φ t ∧ φ t ≤ 1 := fun t ht =>
    ⟨div_nonneg (hF0 t ht.le) ht.le, (div_le_one ht).2 (hFt t ht.le)⟩
  -- Fubini: `a ∫ e^{-a t} h(t) dt = a² ∫ e^{-a r} F(r) dr`
  have hfub : ∀ a, 0 < a → ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (a * Real.exp (-(a * t)) * h t) =
      ∫⁻ r in Set.Ioi 0, ENNReal.ofReal (a ^ 2 * Real.exp (-(a * r)) * F r) := by
    intro a ha
    set H : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (h t)
    set E : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (a ^ 2 * Real.exp (-(a * r)))
    have hHm : Measurable H := ENNReal.measurable_ofReal.comp hm
    have hEm : Measurable E := ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.measurable_exp.comp (measurable_id.const_mul a).neg))
    set D : Set (ℝ × ℝ) := {p | 0 < p.1} ∩ {p | p.1 ≤ p.2}
    have hD : MeasurableSet D := (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_snd)
    set Φ : ℝ × ℝ → ℝ≥0∞ := D.indicator fun p => H p.1 * E p.2
    have hΦ : Measurable Φ := ((hHm.comp measurable_fst).mul (hEm.comp measurable_snd)).indicator hD
    have hleft : ∀ t,
        (Set.Ioi 0).indicator (fun t => H t * ENNReal.ofReal (a * Real.exp (-(a * t)))) t
        = ∫⁻ r, Φ (t, r) := by
      intro t
      by_cases ht : 0 < t
      · rw [Set.indicator_of_mem (Set.mem_Ioi.2 ht), ← lintegral_Ici_sq_mul_exp ha t,
          ← lintegral_const_mul _ hEm, ← lintegral_indicator measurableSet_Ici]
        refine lintegral_congr fun r => ?_
        by_cases hr : t ≤ r
        · simp [Φ, D, Set.indicator, ht, hr, H, E]
        · simp [Φ, D, Set.indicator, ht, hr]
      · rw [Set.indicator_of_notMem (by simpa using ht)]
        have hz : ∀ r, Φ (t, r) = 0 := fun r => by simp [Φ, D, ht]
        simp [hz]
    have hright : ∀ r, ∫⁻ t, Φ (t, r) =
        (Set.Ioi 0).indicator (fun r => E r * ENNReal.ofReal (F r)) r := by
      intro r
      have hΦr : (fun t => Φ (t, r)) = (Set.Ioc 0 r).indicator fun t => H t * E r := by
        funext t
        by_cases ht : t ∈ Set.Ioc 0 r
        · rw [Set.indicator_of_mem ht]
          simp [Φ, D, ht.1, ht.2]
        · rw [Set.indicator_of_notMem ht]
          simp only [Set.mem_Ioc, not_and, not_le] at ht
          by_cases h0' : 0 < t
          · simp [Φ, D, h0', (ht h0').not_ge]
          · simp [Φ, D, h0']
      rw [hΦr, lintegral_indicator measurableSet_Ioc, lintegral_mul_const _ hHm]
      by_cases hr : 0 < r
      · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hr), mul_comm]
        congr 1
        rw [show F r = ∫ s in Set.Ioc 0 r, h s from intervalIntegral.integral_of_le hr.le]
        exact (ofReal_integral_eq_lintegral_ofReal (hint 0 r).1
          (ae_of_all _ fun t => h0 t)).symm
      · rw [Set.indicator_of_notMem (by simpa using hr), Set.Ioc_eq_empty (by simpa using hr)]
        simp
    calc ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (a * Real.exp (-(a * t)) * h t)
        = ∫⁻ t, (Set.Ioi 0).indicator
            (fun t => H t * ENNReal.ofReal (a * Real.exp (-(a * t)))) t := by
          rw [lintegral_indicator measurableSet_Ioi]
          refine lintegral_congr fun t => ?_
          rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ a * Real.exp (-(a * t))), mul_comm]
      _ = ∫⁻ t, ∫⁻ r, Φ (t, r) := lintegral_congr hleft
      _ = ∫⁻ r, ∫⁻ t, Φ (t, r) := lintegral_lintegral_swap hΦ.aemeasurable
      _ = ∫⁻ r, (Set.Ioi 0).indicator (fun r => E r * ENNReal.ofReal (F r)) r :=
          lintegral_congr hright
      _ = ∫⁻ r in Set.Ioi 0, ENNReal.ofReal (a ^ 2 * Real.exp (-(a * r)) * F r) := by
          rw [lintegral_indicator measurableSet_Ioi]
          refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
          exact (ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ a ^ 2 * Real.exp (-(a * r)))).symm
  -- substitution
  have hkey : ∀ a, 0 < a → a * ∫ t in Set.Ioi 0, Real.exp (-(a * t)) * h t =
      ∫ u in Set.Ioi 0, Real.exp (-u) * u * φ (u / a) := by
    intro a ha
    have hl : a * ∫ t in Set.Ioi 0, Real.exp (-(a * t)) * h t =
        ∫ r in Set.Ioi 0, a ^ 2 * Real.exp (-(a * r)) * F r := by
      rw [← integral_const_mul, integral_eq_lintegral_of_nonneg_ae,
        integral_eq_lintegral_of_nonneg_ae,
        ← hfub a ha]
      · congr 1
        exact lintegral_congr fun t => by ring_nf
      · exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun r hr => by
          exact mul_nonneg (by positivity) (hF0 r (le_of_lt hr)))
      · exact ((measurable_const.mul (Real.measurable_exp.comp
          (measurable_id.const_mul a).neg)).mul hFc.measurable).aestronglyMeasurable
      · exact ae_of_all _ fun t => mul_nonneg ha.le (mul_nonneg (Real.exp_pos _).le (h0 t))
      · exact (measurable_const.mul ((Real.measurable_exp.comp
          (measurable_id.const_mul a).neg).mul hm)).aestronglyMeasurable
    have hsub := integral_comp_mul_left_Ioi (fun u => Real.exp (-u) * u * φ (u / a)) 0 ha
    rw [mul_zero] at hsub
    rw [hl]
    have hcongr : ∫ r in Set.Ioi 0, a ^ 2 * Real.exp (-(a * r)) * F r =
        ∫ r in Set.Ioi 0, a * (Real.exp (-(a * r)) * (a * r) * φ (a * r / a)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
      have hr' : r ≠ 0 := (Set.mem_Ioi.1 hr).ne'
      simp only [hφdef]
      field_simp
    rw [hcongr, integral_const_mul, hsub, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha.ne',
      one_mul]
  -- dominated convergence
  have hG : IntegrableOn (fun u : ℝ => Real.exp (-u) * u) (Set.Ioi 0) := by
    have := Real.GammaIntegral_convergent (s := 2) two_pos
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
    norm_num
  have hGint : ∫ u in Set.Ioi 0, Real.exp (-u) * u = 1 := by
    have := Real.Gamma_eq_integral (s := 2) two_pos
    rw [Real.Gamma_two] at this
    rw [this]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    norm_num
  have hlim : Tendsto (fun a => ∫ u in Set.Ioi 0, Real.exp (-u) * u * φ (u / a)) (𝓝[>] 0)
      (𝓝 (∫ u in Set.Ioi 0, Real.exp (-u) * u * L)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun u => Real.exp (-u) * u) ?_ ?_ hG ?_
    · exact Eventually.of_forall fun a =>
        ((Real.measurable_exp.comp measurable_neg).mul measurable_id |>.mul
          (hφm.comp (measurable_id.div_const a))).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
      refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u (hu : 0 < u) => ?_)
      have := hφ01 (u / a) (div_pos hu ha)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le hu.le)
        this.1)]
      calc Real.exp (-u) * u * φ (u / a) ≤ Real.exp (-u) * u * 1 :=
            mul_le_mul_of_nonneg_left this.2 (by have := Real.exp_pos (-u); positivity)
        _ = Real.exp (-u) * u := mul_one _
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u (hu : 0 < u) => ?_)
      have hdiv : Tendsto (fun a => u / a) (𝓝[>] 0) atTop := by
        simpa [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hu
      exact (hL.comp hdiv).const_mul _
  rw [integral_mul_const, hGint, one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
  exact (hkey a ha).symm

end Abelian

/-! ### Identification of almost sure time-average limits -/

section Identification

variable {σ : Type*} [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ]
  (K : σ → PMF σ)

omit [Countable σ] [MeasurableSingletonClass σ] in
theorem lintegral_abelSum_le_one (q g : σ → ℝ) (hq : ∀ x, 0 < q x) (hg1 : ∀ x, g x ≤ 1)
    {a : ℝ} (ha : 0 ≤ a) (x : σ) : ∫⁻ ω, abelSum q g a x ω ∂JumpHold.inputMeasure K ≤ 1 :=
  calc _ ≤ ∫⁻ _, 1 ∂JumpHold.inputMeasure K := lintegral_mono_ae (by
        filter_upwards [JumpHold.ae_clock_nonneg K] with ω hω
        exact abelSum_le_one q g ha hq hg1 x hω)
    _ = 1 := by simp

/-- **Identification of the limit.** Let `w` be a probability law balancing the rate-weighted
jump kernel (`w Q = 0`) with `∑ w q < ∞`, and let the chain be non-explosive from every state.
If from every initial state the time averages of `0 ≤ g ≤ 1` converge almost surely to the same
constant `L`, then `L = ∑_x w(x) g(x)`. The proof passes to Abel means (Abelian theorem), takes
expectations (bounded convergence), averages over `w` (dominated convergence), and uses the
resolvent identity `tsum_mul_lintegral_abelSum`. -/
theorem eq_tsum_of_ae_tendsto (q g : σ → ℝ) (hq : ∀ x, 0 < q x) (hg0 : ∀ x, 0 ≤ g x)
    (hg1 : ∀ x, g x ≤ 1) (w : σ → ℝ≥0∞) (hw : ∑' x, w x = 1)
    (hbal : ∀ y, ∑' x, w x * ENNReal.ofReal (q x) * K x y = w y * ENNReal.ofReal (q y))
    (hfin : ∑' x, w x * ENNReal.ofReal (q x) ≠ ⊤)
    (hT : ∀ x, ∀ᵐ ω ∂JumpHold.inputMeasure K, Tendsto (JumpHold.jumpTime q x ω) atTop atTop)
    {L : ℝ} (hlim : ∀ x, ∀ᵐ ω ∂JumpHold.inputMeasure K,
      Tendsto (fun t => (∫ s in (0 : ℝ)..t, g (JumpHold.path q x ω s)) / t) atTop (𝓝 L)) :
    L = ∑' x, (w x).toReal * g x := by
  set μ := JumpHold.inputMeasure K
  have hA : ∀ x, Tendsto (fun a => ∫ ω, (abelSum q g a x ω).toReal ∂μ) (𝓝[>] 0) (𝓝 L) := by
    intro x
    have hL : ∫ _ω, L ∂μ = L := by simp
    rw [← hL]
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_
      (integrable_const (μ := μ) (1 : ℝ)) ?_
    · exact Eventually.of_forall fun a =>
        (measurable_abelSum q g a x).ennreal_toReal.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
      filter_upwards [JumpHold.ae_clock_nonneg K] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by rw [ENNReal.ofReal_one]; exact abelSum_le_one q g ha.le hq hg1 x hω)
    · filter_upwards [JumpHold.ae_clock_nonneg K, hT x, hlim x] with ω hE hTω hω
      have hmeas := measurable_path hq hE hTω
      refine (tendsto_abel_of_tendsto_cesaro ((measurable_of_countable g).comp hmeas)
        (fun t => hg0 _) (fun t => hg1 _) hω).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
      exact (abelSum_toReal_eq hq hE hTω hg0 ha).symm
  have hw' : ∀ x, w x ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top (by rw [hw]; exact ENNReal.one_ne_top) (ENNReal.le_tsum x)
  have hwsum : Summable fun x => (w x).toReal :=
    ENNReal.summable_toReal (by rw [hw]; exact ENNReal.one_ne_top)
  have hwone : ∑' x, (w x).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq hw', hw, ENNReal.toReal_one]
  have hint : ∀ a, 0 < a → ∀ x, ∫ ω, (abelSum q g a x ω).toReal ∂μ =
      (∫⁻ ω, abelSum q g a x ω ∂μ).toReal := fun a ha x =>
    integral_toReal (measurable_abelSum q g a x).aemeasurable (by
      filter_upwards [JumpHold.ae_clock_nonneg K] with ω hω
      exact (abelSum_le_one q g ha.le hq hg1 x hω).trans_lt ENNReal.one_lt_top)
  have hsum : Tendsto (fun a => ∑' x, (w x).toReal * ∫ ω, (abelSum q g a x ω).toReal ∂μ)
      (𝓝[>] 0) (𝓝 (∑' x, (w x).toReal * L)) := by
    refine tendsto_tsum_of_dominated_convergence hwsum (fun x => (hA x).const_mul _) ?_
    filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
    intro x
    rw [hint a ha x, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
    calc (w x).toReal * (∫⁻ ω, abelSum q g a x ω ∂μ).toReal ≤ (w x).toReal * 1 :=
          mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal zero_le_one (by
            rw [ENNReal.ofReal_one]; exact lintegral_abelSum_le_one K q g hq hg1 ha.le x))
            ENNReal.toReal_nonneg
      _ = (w x).toReal := mul_one _
  have hconst : ∀ a, 0 < a → ∑' x, (w x).toReal * ∫ ω, (abelSum q g a x ω).toReal ∂μ =
      ∑' x, (w x).toReal * g x := by
    intro a ha
    have h := tsum_mul_lintegral_abelSum K q g hq hg1 ha w hbal hfin
    have hne1 : ∀ x, w x * ∫⁻ ω, abelSum q g a x ω ∂μ ≠ ⊤ := fun x =>
      ENNReal.mul_ne_top (hw' x) (ne_top_of_le_ne_top ENNReal.one_ne_top
        (lintegral_abelSum_le_one K q g hq hg1 ha.le x))
    have hne2 : ∀ x, w x * ENNReal.ofReal (g x) ≠ ⊤ := fun x =>
      ENNReal.mul_ne_top (hw' x) ENNReal.ofReal_ne_top
    have h' := congrArg ENNReal.toReal h
    rw [ENNReal.tsum_toReal_eq hne1, ENNReal.tsum_toReal_eq hne2] at h'
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hg0 _)] at h'
    rw [← h']
    exact tsum_congr fun x => by rw [hint a ha x]
  rw [tsum_mul_right, hwone, one_mul] at hsum
  refine tendsto_nhds_unique hsum (tendsto_const_nhds.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
  exact (hconst a ha).symm

end Identification

/-! ### Recurrence -/

section Recurrence

variable {σ : Type*} [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ]
  [DecidableEq σ] (K : σ → PMF σ)

omit [DecidableEq σ] in
/-- **First-step analysis**: a functional of the chain after its first jump, from `x`, averages
to `∑_y K(x, y) E_y[F y]`. -/
theorem lintegral_comp_first (x : σ) {F : σ → (ℕ → (σ → σ) × ℝ) → ℝ≥0∞}
    (hF : ∀ y, Measurable (F y)) :
    ∫⁻ ω, F ((ω 0).1 x) (ctmcShift 1 ω) ∂JumpHold.inputMeasure K =
      ∑' y, K x y * ∫⁻ ω, F y ω ∂JumpHold.inputMeasure K := by
  set μ := JumpHold.inputMeasure K
  have hFm : Measurable fun p : σ × (ℕ → (σ → σ) × ℝ) => F p.1 p.2 :=
    measurable_from_prod_countable_right hF
  have hpx : Measurable fun p : ((σ → σ) × ℝ) × (ℕ → (σ → σ) × ℝ) => (p.1.1 x, p.2) :=
    ((measurable_pi_apply x).comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd
  have hG : Measurable fun p : ((σ → σ) × ℝ) × (ℕ → (σ → σ) × ℝ) => F (p.1.1 x) p.2 :=
    hFm.comp hpx
  have hmf : Measurable fun ω : ℕ → (σ → σ) × ℝ => (ω 0, ctmcShift 1 ω) :=
    (measurable_pi_apply 0).prodMk (measurable_ctmcShift_pi 1)
  set A : σ → ℝ≥0∞ := fun y => ∫⁻ ω, F y ω ∂μ with hAdef
  have hA : Measurable A := measurable_of_countable A
  have hprob : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  calc ∫⁻ ω, F ((ω 0).1 x) (ctmcShift 1 ω) ∂μ
      = ∫⁻ p, F (p.1.1 x) p.2 ∂((JumpHold.stepMeasure K).prod μ) := by
        rw [← JumpHold.inputMeasure_map_first, lintegral_map hG hmf]
    _ = ∫⁻ s, A (s.1 x) ∂(JumpHold.stepMeasure K) := lintegral_prod _ hG.aemeasurable
    _ = ∫⁻ ξ, A (ξ x) ∂(Measure.infinitePi fun y => (K y).toMeasure) := by
        have := lintegral_map
          (μ := (Measure.infinitePi fun y => (K y).toMeasure).prod (expMeasure 1))
          (hA.comp (measurable_pi_apply x)) measurable_fst
        rw [Measure.map_fst_prod, measure_univ, one_smul] at this
        exact this.symm
    _ = ∑' y, K x y * A y := by
        rw [← lintegral_map hA (measurable_pi_apply x), Measure.infinitePi_map_eval,
          lintegral_countable']
        exact tsum_congr fun y => by
          rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y), mul_comm]

omit [DecidableEq σ] in
theorem measurableSet_hit (x₀ x : σ) :
    MeasurableSet {ω : ℕ → (σ → σ) × ℝ | ∃ n, ctmcJumpChain x ω n = x₀} := by
  have : {ω : ℕ → (σ → σ) × ℝ | ∃ n, ctmcJumpChain x ω n = x₀} =
      ⋃ n, (fun ω => ctmcJumpChain x ω n) ⁻¹' {x₀} := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.iUnion fun n => measurable_jumpChain x n (measurableSet_singleton x₀)

/-- The hitting probabilities `h(x) = P_x(∃ n, Y_n = x₀)`. -/
noncomputable def hitProb (x₀ x : σ) : ℝ≥0∞ :=
  JumpHold.inputMeasure K {ω | ∃ n, ctmcJumpChain x ω n = x₀}

omit [DecidableEq σ] in
/-- First-step equation of the hitting probabilities off `x₀`. -/
theorem hitProb_eq {x₀ x : σ} (hx : x ≠ x₀) :
    hitProb K x₀ x = ∑' y, K x y * hitProb K x₀ y := by
  have h := lintegral_comp_first K x (F := fun y => {ω | ∃ n, ctmcJumpChain y ω n = x₀}.indicator 1)
    fun y => measurable_one.indicator (measurableSet_hit x₀ y)
  simp only [lintegral_indicator_one (measurableSet_hit x₀ _)] at h
  simp only [hitProb]
  rw [← h, ← lintegral_indicator_one (measurableSet_hit x₀ x)]
  refine lintegral_congr fun ω => ?_
  simp only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
  congr 1
  apply propext
  constructor
  · rintro ⟨n, hn⟩
    rcases n with _ | n
    · exact absurd hn hx
    · exact ⟨n, by rw [← JumpHold.ctmcJumpChain_succ_eq]; exact hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by rw [JumpHold.ctmcJumpChain_succ_eq]; exact hn⟩

/-- The return probability to `x₀` is the `K(x₀, ·)`-average of the hitting probabilities. -/
theorem measure_return_eq (x₀ : σ) :
    JumpHold.inputMeasure K {ω | visit x₀ x₀ 1 ω ≠ ⊤} = ∑' y, K x₀ y * hitProb K x₀ y := by
  have h := lintegral_comp_first K x₀
    (F := fun y => {ω | ∃ n, ctmcJumpChain y ω n = x₀}.indicator 1)
    fun y => measurable_one.indicator (measurableSet_hit x₀ y)
  simp only [lintegral_indicator_one (measurableSet_hit x₀ _)] at h
  simp only [hitProb]
  have hm : MeasurableSet {ω : ℕ → (σ → σ) × ℝ | visit x₀ x₀ 1 ω ≠ ⊤} :=
    (measurable_visit x₀ x₀ 1) (measurableSet_singleton ⊤).compl
  rw [← h, ← lintegral_indicator_one hm]
  refine lintegral_congr fun ω => ?_
  simp only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
  congr 1
  apply propext
  rw [visit_self_one_ne_top_iff]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, by rw [← JumpHold.ctmcJumpChain_succ_eq]; exact hn⟩
  · rintro ⟨n, hn⟩; exact ⟨n, by rw [JumpHold.ctmcJumpChain_succ_eq]; exact hn⟩

/-- The `(k + 1)`-st visit happens iff the `k`-th does and the chain restarted there returns. -/
theorem measure_visit_succ (x₀ x : σ) (k : ℕ) :
    JumpHold.inputMeasure K {ω | visit x₀ x (k + 1) ω ≠ ⊤} =
      JumpHold.inputMeasure K {ω | visit x₀ x k ω ≠ ⊤} *
        JumpHold.inputMeasure K {ω | visit x₀ x₀ 1 ω ≠ ⊤} := by
  have hset : {ω | visit x₀ x (k + 1) ω ≠ ⊤} = {ω | visit x₀ x k ω ≠ ⊤} ∩ Set.univ ∩
      shiftAt (visit x₀ x k) ⁻¹' {ω | visit x₀ x₀ 1 ω ≠ ⊤} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.inter_univ, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · intro h
      obtain ⟨m, hm⟩ : ∃ m : ℕ, visit x₀ x (k + 1) ω = m := ⟨_, (ENat.natCast_toNat h).symm⟩
      obtain ⟨n, -, hn⟩ := visit_le_of_visit_eq hm (Nat.le_succ k)
      have hadd := visit_add hn 1
      refine ⟨by rw [hn]; exact ENat.natCast_ne_top n, ?_⟩
      rw [shiftAt, hn, ENat.toNat_natCast]
      intro ht
      rw [hm, ht, add_top] at hadd
      exact ENat.natCast_ne_top m hadd
    · rintro ⟨h, h1⟩
      obtain ⟨n, hn⟩ : ∃ n : ℕ, visit x₀ x k ω = n := ⟨_, (ENat.natCast_toNat h).symm⟩
      rw [shiftAt, hn, ENat.toNat_natCast] at h1
      rw [visit_add hn 1]
      exact WithTop.add_ne_top.2 ⟨ENat.natCast_ne_top n, h1⟩
  have hdet : IsDeterminedBefore (visit x₀ x k) Set.univ := fun _ _ _ _ _ _ => trivial
  have := measure_inter_shiftAt_preimage (JumpHold.stepMeasure K)
    (isStepStoppingTime_visit x₀ x k) (measurable_visit x₀ x k) MeasurableSet.univ hdet
    ((measurable_visit x₀ x₀ 1) (measurableSet_singleton ⊤).compl)
  rw [Set.inter_univ] at this
  rw [hset, Set.inter_univ]
  exact this

theorem measure_visit_le (x₀ x : σ) (k : ℕ) :
    JumpHold.inputMeasure K {ω | visit x₀ x k ω ≠ ⊤} ≤
      JumpHold.inputMeasure K {ω | visit x₀ x₀ 1 ω ≠ ⊤} ^ k := by
  induction k with
  | zero => simpa using prob_le_one
  | succ k ih =>
    rw [measure_visit_succ, pow_succ]
    exact mul_le_mul_left ih _

/-- If the chain returns to `x₀` with probability `< 1`, it visits `x₀` only finitely often,
almost surely, from every initial state. -/
theorem ae_exists_visit_eq_top {x₀ : σ}
    (hp : JumpHold.inputMeasure K {ω | visit x₀ x₀ 1 ω ≠ ⊤} < 1) (x : σ) :
    ∀ᵐ ω ∂JumpHold.inputMeasure K, ∃ k, visit x₀ x k ω = ⊤ := by
  rw [ae_iff]
  push Not
  refine le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hp)
    fun k => ?_) bot_le
  exact (measure_mono (s := {ω | ∀ k, visit x₀ x k ω ≠ ⊤}) (t := {ω | visit x₀ x k ω ≠ ⊤})
    fun ω hω => hω k).trans (measure_visit_le K x₀ x k)

omit [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ] in
/-- With finitely many visits to `x₀`, the time spent at `x₀` is bounded, so its long-run
fraction vanishes. -/
theorem tendsto_integral_indicator_div_zero {q : σ → ℝ} (hq : ∀ y, 0 < q y) {x₀ x : σ}
    {ω : ℕ → (σ → σ) × ℝ} (hE : ∀ k, 0 ≤ (ω k).2)
    (hT : Tendsto (JumpHold.jumpTime q x ω) atTop atTop) {k₀ : ℕ}
    (hk₀ : visit x₀ x k₀ ω = ⊤) [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ] :
    Tendsto (fun t => (∫ s in (0 : ℝ)..t,
      (if JumpHold.path q x ω s = x₀ then (1 : ℝ) else 0)) / t) atTop (𝓝 0) := by
  set g : σ → ℝ := fun y => if y = x₀ then 1 else 0 with hgdef
  have hg0 : ∀ y, 0 ≤ g y := fun y => by simp only [hgdef]; split_ifs <;> norm_num
  have hgB : ∀ y, |g y| ≤ 1 := fun y => by simp only [hgdef]; split_ifs <;> norm_num
  have hmeas := measurable_path hq hE hT
  -- the number of visits is bounded, hence eventually constant
  have hbdd : ∀ n, nVisits x₀ x ω n ≤ k₀ := by
    intro n
    by_contra h
    obtain ⟨m, -, hm⟩ := exists_visit_lt_of_lt_nVisits (x₀ := x₀) (x := x) (ω := ω)
      (show k₀ < nVisits x₀ x ω n by omega)
    rw [hm] at hk₀
    exact ENat.natCast_ne_top m hk₀
  have hS : sSup (Set.range (nVisits x₀ x ω)) ∈ Set.range (nVisits x₀ x ω) :=
    Nat.sSup_mem (Set.range_nonempty _) ⟨k₀, by rintro _ ⟨n, rfl⟩; exact hbdd n⟩
  obtain ⟨N, hN⟩ := hS
  have hmax : ∀ n, nVisits x₀ x ω n ≤ nVisits x₀ x ω N := fun n => by
    rw [hN]; exact le_csSup ⟨k₀, by rintro _ ⟨m, rfl⟩; exact hbdd m⟩ ⟨n, rfl⟩
  have hnot : ∀ n, N ≤ n → ctmcJumpChain x ω n ≠ x₀ := by
    intro n hn hY
    have h1 := nVisits_lt_of_lt hY (show n < n + 1 by omega)
    have h2 := nVisits_mono x₀ x ω hn
    have h3 := hmax (n + 1)
    omega
  have hconst : ∀ m, N ≤ m → reward q g x ω m = reward q g x ω N := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      rw [reward, sum_range_succ, ← reward, ih]
      simp [hgdef, hnot m hm]
  set C := reward q g x ω N
  have hle : ∀ t, 0 ≤ t → ∫ s in (0 : ℝ)..t, g (JumpHold.path q x ω s) ≤ C := by
    intro t ht
    obtain ⟨m, hm⟩ := (hT.eventually (eventually_ge_atTop t)).and
      (eventually_ge_atTop N) |>.exists
    calc ∫ s in (0 : ℝ)..t, g (JumpHold.path q x ω s)
        ≤ ∫ s in (0 : ℝ)..JumpHold.jumpTime q x ω m, g (JumpHold.path q x ω s) :=
          intervalIntegral.integral_mono_interval le_rfl ht hm.1
            (ae_of_all _ fun s => hg0 _) (intervalIntegrable_path hmeas hgB _ _)
      _ = C := by rw [integral_path_jumpTime hq hE hmeas hgB, hconst m hm.2]
  have hge : ∀ t, 0 ≤ t → 0 ≤ ∫ s in (0 : ℝ)..t, g (JumpHold.path q x ω s) := fun t ht =>
    intervalIntegral.integral_nonneg ht fun s _ => hg0 _
  have hlim : Tendsto (fun t : ℝ => C / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop 0] with t ht
    exact div_nonneg (hge t ht) ht
  · filter_upwards [eventually_gt_atTop 0] with t ht
    exact div_le_div_of_nonneg_right (hle t ht.le) ht.le

/-- **Recurrence from a balanced law.** If `w` is a probability law balancing the
rate-weighted jump kernel, `∑ w q < ∞`, the chain is non-explosive and `w(x₀) > 0`, then the
chain started at `x₀` returns to `x₀` almost surely. -/
theorem measure_return_eq_one (q : σ → ℝ) (hq : ∀ x, 0 < q x) (w : σ → ℝ≥0∞)
    (hw : ∑' x, w x = 1)
    (hbal : ∀ y, ∑' x, w x * ENNReal.ofReal (q x) * K x y = w y * ENNReal.ofReal (q y))
    (hfin : ∑' x, w x * ENNReal.ofReal (q x) ≠ ⊤)
    (hT : ∀ x, ∀ᵐ ω ∂JumpHold.inputMeasure K, Tendsto (JumpHold.jumpTime q x ω) atTop atTop)
    {x₀ : σ} (hx₀ : w x₀ ≠ 0) :
    JumpHold.inputMeasure K {ω | visit x₀ x₀ 1 ω ≠ ⊤} = 1 := by
  by_contra hp
  have hp' : JumpHold.inputMeasure K {ω | visit x₀ x₀ 1 ω ≠ ⊤} < 1 :=
    lt_of_le_of_ne prob_le_one hp
  set g : σ → ℝ := fun y => if y = x₀ then 1 else 0 with hgdef
  have hlim : ∀ x, ∀ᵐ ω ∂JumpHold.inputMeasure K,
      Tendsto (fun t => (∫ s in (0 : ℝ)..t, g (JumpHold.path q x ω s)) / t) atTop (𝓝 0) := by
    intro x
    filter_upwards [ae_exists_visit_eq_top K hp' x, JumpHold.ae_clock_nonneg K, hT x]
      with ω ⟨k₀, hk₀⟩ hE hTω
    exact tendsto_integral_indicator_div_zero hq hE hTω hk₀
  have h0 := eq_tsum_of_ae_tendsto K q g hq (fun y => by simp only [hgdef]; split_ifs <;> norm_num)
    (fun y => by simp only [hgdef]; split_ifs <;> norm_num) w hw hbal hfin hT hlim
  have hw' : w x₀ ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hw]; exact ENNReal.one_ne_top) (ENNReal.le_tsum x₀)
  simp only [hgdef, mul_ite, mul_one, mul_zero, tsum_ite_eq] at h0
  exact (ENNReal.toReal_pos hx₀ hw').ne h0

/-- **Hitting from every state.** If the chain returns to `x₀` almost surely and every state is
reachable from `x₀` through jumps of positive probability, then from every initial state the
chain hits `x₀` almost surely. -/
theorem hitProb_eq_one {x₀ : σ} (hp : JumpHold.inputMeasure K {ω | visit x₀ x₀ 1 ω ≠ ⊤} = 1)
    {y : σ} (hy : Relation.ReflTransGen (fun u v => K u v ≠ 0) x₀ y) : hitProb K x₀ y = 1 := by
  have hle : ∀ z, hitProb K x₀ z ≤ 1 := fun z => prob_le_one
  have hprop : ∀ u, ∑' z, K u z * hitProb K x₀ z = 1 → ∀ v, K u v ≠ 0 → hitProb K x₀ v = 1 := by
    intro u hu v hv
    by_contra hne
    have hlt : hitProb K x₀ v < 1 := lt_of_le_of_ne (hle v) hne
    have : ∑' z, K u z * hitProb K x₀ z < ∑' z, K u z := by
      refine ENNReal.tsum_lt_tsum (i := v) (by rw [hu]; exact ENNReal.one_ne_top)
        (fun z => mul_le_of_le_one_right bot_le (hle z)) ?_
      simpa [mul_comm] using ENNReal.mul_lt_mul_left hv (PMF.apply_ne_top _ _) hlt
    rw [hu, PMF.tsum_coe] at this
    exact lt_irrefl _ this
  induction hy with
  | refl =>
    have : {ω : ℕ → (σ → σ) × ℝ | ∃ n, ctmcJumpChain x₀ ω n = x₀} = Set.univ :=
      Set.eq_univ_of_forall fun ω => ⟨0, rfl⟩
    rw [hitProb, this, measure_univ]
  | @tail b c _ hbc ih =>
    by_cases hb : b = x₀
    · subst hb
      exact hprop _ (by rw [← measure_return_eq]; exact hp) c hbc
    · exact hprop b (by rw [← hitProb_eq K hb]; exact ih) c hbc

/-- Under recurrence of `x₀` and reachability of every state, all visits to `x₀` happen almost
surely, from every initial state. -/
theorem ae_forall_visit_ne_top {x₀ : σ}
    (hp : JumpHold.inputMeasure K {ω | visit x₀ x₀ 1 ω ≠ ⊤} = 1)
    (hirr : ∀ y, Relation.ReflTransGen (fun u v => K u v ≠ 0) x₀ y) (x : σ) :
    ∀ᵐ ω ∂JumpHold.inputMeasure K, ∀ k, visit x₀ x k ω ≠ ⊤ := by
  rw [ae_all_iff]
  intro k
  have hk : JumpHold.inputMeasure K {ω | visit x₀ x k ω ≠ ⊤} = 1 := by
    induction k with
    | zero =>
      rw [← hitProb_eq_one K hp (hirr x), hitProb]
      congr 1
      ext ω
      simp only [Set.mem_ofPred_eq]
      exact visit_zero_ne_top_iff
    | succ k ih => rw [measure_visit_succ, ih, hp, one_mul]
  have hm : MeasurableSet {ω | visit x₀ x k ω ≠ ⊤} :=
    (measurable_visit x₀ x k) (measurableSet_singleton ⊤).compl
  rw [ae_iff]
  have := prob_compl_eq_zero_iff hm |>.2 hk
  simpa [Set.compl_def] using this

end Recurrence

/-! ### Regeneration cycles, positive recurrence and the ergodic theorem -/

section Ergodic

open StochasticCRNErgodicity

variable {σ : Type*} [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ]
  [DecidableEq σ] (K : σ → PMF σ)

theorem expMeasure_one_Iic_zero : expMeasure 1 (Set.Iic 0) = 0 := by
  rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iic,
    ← setLIntegral_congr Iio_ae_eq_Iic]
  refine (setLIntegral_congr_fun measurableSet_Iio fun x hx => gammaPDF_of_neg hx).trans ?_
  simp

omit [Countable σ] [MeasurableSingletonClass σ] [DecidableEq σ] in
/-- The clocks are almost surely positive. -/
theorem ae_clock_pos : ∀ᵐ ω ∂JumpHold.inputMeasure K, ∀ k, 0 < (ω k).2 := by
  rw [ae_all_iff]
  intro k
  have hm : Measurable fun ω : ℕ → (σ → σ) × ℝ => (ω k).2 := (measurable_pi_apply k).snd
  rw [ae_iff]
  have : {ω : ℕ → (σ → σ) × ℝ | ¬ 0 < (ω k).2} = (fun ω => (ω k).2) ⁻¹' Set.Iic 0 := by
    ext; simp
  rw [this, ← Measure.map_apply hm measurableSet_Iic, JumpHold.inputMeasure_map_clock,
    expMeasure_one_Iic_zero]

omit [Countable σ] [MeasurableSingletonClass σ] [DecidableEq σ] in
theorem inputMeasure_eq : JumpHold.inputMeasure K =
    Measure.infinitePi fun _ : ℕ => JumpHold.stepMeasure K := rfl

/-- After an almost surely finite visit, the steps again have the input law. -/
theorem map_shiftAt_visit {x₀ x : σ} {k : ℕ}
    (hk : ∀ᵐ ω ∂JumpHold.inputMeasure K, visit x₀ x k ω ≠ ⊤) :
    (JumpHold.inputMeasure K).map (shiftAt (visit x₀ x k)) = JumpHold.inputMeasure K := by
  have hfin : JumpHold.inputMeasure K {ω | visit x₀ x k ω = ⊤} = 0 := by
    rw [ae_iff] at hk; simpa using hk
  have h := map_prod_shiftAt (JumpHold.stepMeasure K) (isStepStoppingTime_visit x₀ x k)
    (measurable_visit x₀ x k) hfin (G := fun _ => (0 : ℕ)) measurable_const
    (fun _ _ _ _ _ => rfl)
  rw [← inputMeasure_eq] at h
  have h2 := congrArg (Measure.map Prod.snd) h
  rw [Measure.map_map measurable_snd (measurable_const.prodMk
    (measurable_shiftAt (measurable_visit x₀ x k))), Measure.map_snd_prod,
    Measure.map_apply measurable_const MeasurableSet.univ, Set.preimage_univ, measure_univ,
    one_smul] at h2
  exact h2

omit [Countable σ] [MeasurableSingletonClass σ] in
theorem cycleSum_ae_eq {q g : σ → ℝ} {x₀ x : σ}
    (hall : ∀ᵐ ω ∂JumpHold.inputMeasure K, ∀ k, visit x₀ x k ω ≠ ⊤) (k : ℕ) :
    cycleSum q g x₀ x k =ᵐ[JumpHold.inputMeasure K]
      returnReward q g x₀ ∘ shiftAt (visit x₀ x k) := by
  filter_upwards [hall] with ω hω
  obtain ⟨n, hn⟩ : ∃ n : ℕ, visit x₀ x k ω = n := ⟨_, (ENat.natCast_toNat (hω k)).symm⟩
  exact cycleSum_eq q g hn (hω (k + 1))

/-- Each regeneration cycle has the law of the first excursion from `x₀`. -/
theorem identDistrib_cycleSum (q g : σ → ℝ) {x₀ x : σ}
    (hall : ∀ᵐ ω ∂JumpHold.inputMeasure K, ∀ k, visit x₀ x k ω ≠ ⊤) (k : ℕ) :
    IdentDistrib (cycleSum q g x₀ x k) (returnReward q g x₀)
      (JumpHold.inputMeasure K) (JumpHold.inputMeasure K) := by
  have hk : ∀ᵐ ω ∂JumpHold.inputMeasure K, visit x₀ x k ω ≠ ⊤ := hall.mono fun ω h => h k
  have hsh := measurable_shiftAt (σ := σ) (measurable_visit x₀ x k)
  refine (IdentDistrib.of_ae_eq (measurable_cycleSum q g x₀ x k).aemeasurable
    (cycleSum_ae_eq K hall k)).trans ⟨((measurable_returnReward q g x₀).comp hsh).aemeasurable,
    (measurable_returnReward q g x₀).aemeasurable, ?_⟩
  rw [← Measure.map_map (measurable_returnReward q g x₀) hsh, map_shiftAt_visit K hk]

/-- Distinct regeneration cycles are independent (strong Markov property at the later visit). -/
theorem indepFun_cycleSum_of_lt (q g g' : σ → ℝ) {x₀ x : σ}
    (hall : ∀ᵐ ω ∂JumpHold.inputMeasure K, ∀ k, visit x₀ x k ω ≠ ⊤) {j k : ℕ} (hjk : j < k) :
    IndepFun (cycleSum q g x₀ x j) (cycleSum q g' x₀ x k) (JumpHold.inputMeasure K) := by
  have hk : ∀ᵐ ω ∂JumpHold.inputMeasure K, visit x₀ x k ω ≠ ⊤ := hall.mono fun ω h => h k
  have hfin : JumpHold.inputMeasure K {ω | visit x₀ x k ω = ⊤} = 0 := by
    rw [ae_iff] at hk; simpa using hk
  have hsh := measurable_shiftAt (σ := σ) (measurable_visit x₀ x k)
  have hprod := map_prod_shiftAt (JumpHold.stepMeasure K) (isStepStoppingTime_visit x₀ x k)
    (measurable_visit x₀ x k) hfin (measurable_cycleSum q g x₀ x j)
    (fun n ω ω' hn hag => cycleSum_congr q g hjk hn hag)
  rw [← inputMeasure_eq] at hprod
  have hind : IndepFun (cycleSum q g x₀ x j) (shiftAt (visit x₀ x k))
      (JumpHold.inputMeasure K) := by
    rw [indepFun_iff_map_prod_eq_prod_map_map (measurable_cycleSum q g x₀ x j).aemeasurable
      hsh.aemeasurable, map_shiftAt_visit K hk]
    exact hprod
  exact (hind.comp measurable_id (measurable_returnReward q g' x₀)).congr
    (ae_of_all _ fun _ => rfl) (cycleSum_ae_eq K hall k).symm

open Function in
theorem pairwise_indepFun_cycleSum (q g : σ → ℝ) {x₀ x : σ}
    (hall : ∀ᵐ ω ∂JumpHold.inputMeasure K, ∀ k, visit x₀ x k ω ≠ ⊤) :
    Pairwise ((· ⟂ᵢ[JumpHold.inputMeasure K] ·) on cycleSum q g x₀ x) := by
  intro j k hjk
  rcases Nat.lt_or_gt_of_ne hjk with h | h
  · exact indepFun_cycleSum_of_lt K q g g hall h
  · exact (indepFun_cycleSum_of_lt K q g g hall h).symm

omit [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ] [DecidableEq σ] in
theorem abs_reward_le {q g : σ → ℝ} (hq : ∀ y, 0 < q y) (hg : ∀ y, |g y| ≤ 1) {x : σ}
    {ω : ℕ → (σ → σ) × ℝ} (hE : ∀ k, 0 ≤ (ω k).2) (m : ℕ) :
    |reward q g x ω m| ≤ reward q (fun _ => 1) x ω m := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  have hH : 0 ≤ JumpHold.holdingTime q x ω i := div_nonneg (hE i) (hq _).le
  rw [abs_mul, abs_of_nonneg hH, one_mul]
  exact mul_le_of_le_one_left hH (hg _)

omit [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ] in
/-- The time spent at `x₀` during the first excursion from `x₀` is the first holding time. -/
theorem returnReward_indicator_eq {q : σ → ℝ} {x₀ : σ} {ω : ℕ → (σ → σ) × ℝ}
    (h : visit x₀ x₀ 1 ω ≠ ⊤) :
    returnReward q (fun y => if y = x₀ then 1 else 0) x₀ ω = (ω 0).2 / q x₀ := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, visit x₀ x₀ 1 ω = m := ⟨_, (ENat.natCast_toNat h).symm⟩
  have hm1 : 1 ≤ m := by
    rw [visit_eq_iff] at hm
    rcases m with _ | m
    · rw [nVisits_zero] at hm; omega
    · omega
  rw [returnReward, hm, ENat.toNat_natCast, reward, sum_eq_single 0]
  · simp [ctmcJumpChain, JumpHold.holdingTime]
  · intro i hi hi0
    simp only [ctmcJumpChain_ne_of_lt_visit_one hm (Nat.pos_of_ne_zero hi0) (by simpa using hi),
      ite_false, zero_mul]
  · intro h0; simp at h0; omega

omit [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ] in
/-- With positive clocks the times of the successive visits are strictly increasing. -/
theorem strictMono_jumpTime_visit {q : σ → ℝ} (hq : ∀ y, 0 < q y) {x₀ x : σ}
    {ω : ℕ → (σ → σ) × ℝ} (hE : ∀ k, 0 < (ω k).2) (hall : ∀ k, visit x₀ x k ω ≠ ⊤) :
    StrictMono fun n => JumpHold.jumpTime q x ω (visit x₀ x n ω).toNat := by
  have hT : StrictMono (JumpHold.jumpTime q x ω) := strictMono_nat_of_lt_succ fun i => by
    rw [jumpTime_succ]
    have := div_pos (hE i) (hq (ctmcJumpChain x ω i))
    simp only [JumpHold.holdingTime] at this ⊢
    linarith
  refine strictMono_nat_of_lt_succ fun n => hT ?_
  obtain ⟨a, ha⟩ : ∃ a : ℕ, visit x₀ x n ω = a := ⟨_, (ENat.natCast_toNat (hall n)).symm⟩
  have hadd := visit_add ha 1
  have h1 : visit x₀ x₀ 1 (ctmcShift a ω) ≠ ⊤ := fun ht => hall (n + 1) (by rw [hadd, ht, add_top])
  obtain ⟨m, hm⟩ : ∃ m : ℕ, visit x₀ x₀ 1 (ctmcShift a ω) = m := ⟨_, (ENat.natCast_toNat h1).symm⟩
  have hm1 : 1 ≤ m := by
    rw [visit_eq_iff] at hm
    rcases m with _ | m
    · rw [nVisits_zero] at hm; omega
    · omega
  rw [hadd, hm, ha, ← Nat.cast_add, ENat.toNat_natCast, ENat.toNat_natCast]
  omega

omit [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ] in
/-- Rewards at the successive visits telescope into the cycle rewards. -/
theorem reward_visit_eq (q g : σ → ℝ) (x₀ x : σ) (ω : ℕ → (σ → σ) × ℝ) (n : ℕ) :
    reward q g x ω (visit x₀ x n ω).toNat =
      reward q g x ω (visit x₀ x 0 ω).toNat + ∑ k ∈ range n, cycleSum q g x₀ x k ω := by
  simp only [cycleSum]
  rw [sum_range_sub (fun k => reward q g x ω (visit x₀ x k ω).toNat)]
  ring

theorem tendsto_div_of_eq_add_sum' {a d : ℕ → ℝ} {c μ : ℝ}
    (h : ∀ n, a n = c + ∑ k ∈ range n, d k)
    (hd : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ k ∈ range n, d k) atTop (𝓝 μ)) :
    Tendsto (fun n : ℕ => a n / n) atTop (𝓝 μ) := by
  have := (tendsto_const_div_atTop_nhds_zero_nat c).add hd
  rw [zero_add] at this
  refine this.congr fun n => ?_
  rw [h, smul_eq_mul, add_div, div_eq_inv_mul (∑ k ∈ range n, d k)]

/-- **Renewal–reward along the regeneration cycles.** If all visits to `x₀` happen and the mean
return time to `x₀` is finite, the time averages of `|g| ≤ 1` from `x` converge almost surely
to `E[cycle reward] / E[cycle length]` of the first excursion from `x₀`. -/
theorem ae_tendsto_of_integrable (q g : σ → ℝ) (hq : ∀ y, 0 < q y) (hg : ∀ y, |g y| ≤ 1)
    {x₀ x : σ}
    (hT : ∀ᵐ ω ∂JumpHold.inputMeasure K, Tendsto (JumpHold.jumpTime q x ω) atTop atTop)
    (hall : ∀ᵐ ω ∂JumpHold.inputMeasure K, ∀ k, visit x₀ x k ω ≠ ⊤)
    (hret : ∀ᵐ ω ∂JumpHold.inputMeasure K, visit x₀ x₀ 1 ω ≠ ⊤)
    (hint : Integrable (returnReward q (fun _ => 1) x₀) (JumpHold.inputMeasure K)) :
    ∀ᵐ ω ∂JumpHold.inputMeasure K,
      Tendsto (fun t => (∫ s in (0 : ℝ)..t, g (JumpHold.path q x ω s)) / t) atTop
        (𝓝 ((JumpHold.inputMeasure K)[returnReward q g x₀] /
          (JumpHold.inputMeasure K)[returnReward q (fun _ => 1) x₀])) := by
  set μ := JumpHold.inputMeasure K
  set L := cycleSum q (fun _ => 1) x₀ x
  set W := cycleSum q g x₀ x
  have hLid : ∀ k, IdentDistrib (L k) (L 0) μ μ := fun k =>
    (identDistrib_cycleSum K _ _ hall k).trans (identDistrib_cycleSum K _ _ hall 0).symm
  have hWid : ∀ k, IdentDistrib (W k) (W 0) μ μ := fun k =>
    (identDistrib_cycleSum K _ _ hall k).trans (identDistrib_cycleSum K _ _ hall 0).symm
  have hLint : Integrable (L 0) μ := (identDistrib_cycleSum K _ _ hall 0).integrable_iff.2 hint
  have hRint : Integrable (returnReward q g x₀) μ := by
    refine hint.mono' (measurable_returnReward q g x₀).aestronglyMeasurable ?_
    filter_upwards [JumpHold.ae_clock_nonneg K] with ω hω
    rw [Real.norm_eq_abs]
    exact abs_reward_le hq hg hω _
  have hWint : Integrable (W 0) μ := (identDistrib_cycleSum K _ _ hall 0).integrable_iff.2 hRint
  have hm : 0 < μ[returnReward q (fun _ => 1) x₀] := by
    have hpos : ∀ᵐ ω ∂μ, 0 < returnReward q (fun _ => 1) x₀ ω := by
      filter_upwards [ae_clock_pos K, hret] with ω hE h1
      obtain ⟨m, hm⟩ : ∃ m : ℕ, visit x₀ x₀ 1 ω = m := ⟨_, (ENat.natCast_toNat h1).symm⟩
      have hm1 : 1 ≤ m := by
        rw [visit_eq_iff] at hm
        rcases m with _ | m
        · rw [nVisits_zero] at hm; omega
        · omega
      rw [returnReward, hm, ENat.toNat_natCast, reward_one]
      calc (0 : ℝ) < JumpHold.jumpTime q x₀ ω 1 := by
            simp only [JumpHold.jumpTime, sum_range_one, JumpHold.holdingTime]
            exact div_pos (hE 0) (hq _)
        _ ≤ JumpHold.jumpTime q x₀ ω m := jumpTime_mono hq (fun k => (hE k).le) hm1
    rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun ω h => h.le) hint]
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have hc : μ (Function.support (returnReward q (fun _ => 1) x₀))ᶜ = 0 := by
      rw [Function.compl_support]
      exact measure_mono_null (fun ω (h : returnReward q (fun _ => 1) x₀ ω = 0) =>
        (show ¬ 0 < returnReward q (fun _ => 1) x₀ ω by rw [h]; exact lt_irrefl 0))
        (ae_iff.1 hpos)
    have := measure_univ_le_add_compl (μ := μ) (Function.support (returnReward q (fun _ => 1) x₀))
    rw [h0, hc, add_zero, measure_univ] at this
    exact absurd this (by simp)
  have hLmean : μ[L 0] = μ[returnReward q (fun _ => 1) x₀] :=
    (identDistrib_cycleSum K _ _ hall 0).integral_eq
  have hWmean : μ[W 0] = μ[returnReward q g x₀] := (identDistrib_cycleSum K _ _ hall 0).integral_eq
  filter_upwards [strong_law_ae L hLint (pairwise_indepFun_cycleSum K q (fun _ => 1) hall) hLid,
    strong_law_ae W hWint (pairwise_indepFun_cycleSum K q g hall) hWid, ae_clock_pos K, hT, hall]
    with ω hLω hWω hE hTω hallω
  rw [hLmean] at hLω
  rw [hWmean] at hWω
  have hE' : ∀ k, 0 ≤ (ω k).2 := fun k => (hE k).le
  have hmeas := measurable_path hq hE' hTω
  set R : ℕ → ℝ := fun n => JumpHold.jumpTime q x ω (visit x₀ x n ω).toNat
  have hF : ∀ n, ∫ s in (0 : ℝ)..R n, g (JumpHold.path q x ω s) =
      reward q g x ω (visit x₀ x 0 ω).toNat + ∑ k ∈ range n, W k ω := fun n => by
    rw [integral_path_jumpTime hq hE' hmeas hg, reward_visit_eq]
  have hR : ∀ n, R n = R 0 + ∑ k ∈ range n, L k ω := fun n => by
    simp only [R]
    rw [← reward_one, ← reward_one, reward_visit_eq q (fun _ => 1) x₀ x ω n]
  exact tendsto_div_of_renewal (F := fun t => ∫ s in (0 : ℝ)..t, g (JumpHold.path q x ω s))
    (R := R) (by simp)
    (fun s t _ hst => abs_integral_path_sub_le hmeas hg hst)
    ((jumpTime_zero (q := q) (x := x) (ω := ω)).symm.le.trans
      (jumpTime_mono hq hE' (Nat.zero_le _)))
    (strictMono_jumpTime_visit hq hE hallω) hm (tendsto_div_of_eq_add_sum' hR hLω)
    ((tendsto_div_of_eq_add_sum' hF hWω).congr fun n => rfl)

omit [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ] in
theorem cycleSum_one_eq (q : σ → ℝ) (x₀ x : σ) (ω : ℕ → (σ → σ) × ℝ) (k : ℕ) :
    cycleSum q (fun _ => 1) x₀ x k ω =
      JumpHold.jumpTime q x ω (visit x₀ x (k + 1) ω).toNat -
        JumpHold.jumpTime q x ω (visit x₀ x k ω).toNat := by
  simp only [cycleSum, reward_one]

/-- **Positive recurrence from a balanced law.** Under the hypotheses of
`measure_return_eq_one`, if all visits to `x₀` happen from every initial state, the mean return
time to `x₀` is finite. Otherwise the long-run fraction of time at `x₀` would vanish from every
initial state (renewal theorem with infinite mean), contradicting `eq_tsum_of_ae_tendsto`,
which identifies it with `w(x₀) > 0`. -/
theorem integrable_returnReward (q : σ → ℝ) (hq : ∀ y, 0 < q y) (w : σ → ℝ≥0∞)
    (hw : ∑' x, w x = 1)
    (hbal : ∀ y, ∑' x, w x * ENNReal.ofReal (q x) * K x y = w y * ENNReal.ofReal (q y))
    (hfin : ∑' x, w x * ENNReal.ofReal (q x) ≠ ⊤)
    (hT : ∀ x, ∀ᵐ ω ∂JumpHold.inputMeasure K, Tendsto (JumpHold.jumpTime q x ω) atTop atTop)
    {x₀ : σ} (hx₀ : w x₀ ≠ 0)
    (hall : ∀ x, ∀ᵐ ω ∂JumpHold.inputMeasure K, ∀ k, visit x₀ x k ω ≠ ⊤) :
    Integrable (returnReward q (fun _ => 1) x₀) (JumpHold.inputMeasure K) := by
  set μ := JumpHold.inputMeasure K
  by_contra hni
  set g : σ → ℝ := fun y => if y = x₀ then 1 else 0 with hgdef
  have hg0 : ∀ y, 0 ≤ g y := fun y => by simp only [hgdef]; split_ifs <;> norm_num
  have hg1 : ∀ y, g y ≤ 1 := fun y => by simp only [hgdef]; split_ifs <;> norm_num
  have hgB : ∀ y, |g y| ≤ 1 := fun y => by simp only [hgdef]; split_ifs <;> norm_num
  have hret : ∀ᵐ ω ∂μ, visit x₀ x₀ 1 ω ≠ ⊤ := (hall x₀).mono fun ω h => h 1
  have hHint : Integrable (returnReward q g x₀) μ := by
    have hclock : Integrable (fun ω : ℕ → (σ → σ) × ℝ => (ω 0).2 / q x₀) μ := by
      have := integrable_id_expMeasure (r := 1) one_pos
      rw [← JumpHold.inputMeasure_map_clock K 0] at this
      exact ((integrable_map_measure (by fun_prop)
        ((measurable_pi_apply 0).snd).aemeasurable).1 this).div_const _
    refine hclock.congr ?_
    filter_upwards [hret] with ω h
    exact (returnReward_indicator_eq h).symm
  have hlim : ∀ x, ∀ᵐ ω ∂μ, Tendsto (fun t => (∫ s in (0 : ℝ)..t,
      g (JumpHold.path q x ω s)) / t) atTop (𝓝 0) := by
    intro x
    set L' : ℕ → (ℕ → (σ → σ) × ℝ) → ℝ := fun k ω => max (cycleSum q (fun _ => 1) x₀ x k ω) 0
    set W := cycleSum q g x₀ x
    have hmax : Measurable fun r : ℝ => max r 0 := measurable_id.max measurable_const
    have hLid : ∀ k, IdentDistrib (L' k) (L' 0) μ μ := fun k =>
      ((identDistrib_cycleSum K q _ (hall x) k).trans
        (identDistrib_cycleSum K q _ (hall x) 0).symm).comp hmax
    have hLind : Pairwise (Function.onFun (fun f h => f ⟂ᵢ[μ] h) L') := fun i j hij =>
      (pairwise_indepFun_cycleSum K q (fun _ => 1) (hall x) hij).comp hmax hmax
    have hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < cycleSum q (fun _ => 1) x₀ x k ω := by
      filter_upwards [ae_clock_pos K, hall x] with ω hE hallω k
      rw [cycleSum_one_eq]
      exact sub_pos.2 ((strictMono_jumpTime_visit hq hE hallω) (Nat.lt_succ_self k))
    have hLni : ¬ Integrable (L' 0) μ := by
      intro hi
      apply hni
      refine (identDistrib_cycleSum K q _ (hall x) 0).integrable_iff.1 (hi.congr ?_)
      filter_upwards [hpos] with ω hω
      exact max_eq_left (hω 0).le
    have hWid : ∀ k, IdentDistrib (W k) (W 0) μ μ := fun k =>
      (identDistrib_cycleSum K q g (hall x) k).trans (identDistrib_cycleSum K q g (hall x) 0).symm
    have hWint : Integrable (W 0) μ :=
      (identDistrib_cycleSum K q g (hall x) 0).integrable_iff.2 hHint
    filter_upwards [ae_tendsto_avg_atTop_of_not_integrable (fun k ω => le_max_right _ _) hLni
      hLind hLid, strong_law_ae W hWint (pairwise_indepFun_cycleSum K q g (hall x)) hWid,
      ae_clock_pos K, hT x, hall x, hpos] with ω hLω hWω hE hTω hallω hposω
    have hE' : ∀ k, 0 ≤ (ω k).2 := fun k => (hE k).le
    have hmeas := measurable_path hq hE' hTω
    set R : ℕ → ℝ := fun n => JumpHold.jumpTime q x ω (visit x₀ x n ω).toNat
    have hF : ∀ n, ∫ s in (0 : ℝ)..R n, g (JumpHold.path q x ω s) =
        reward q g x ω (visit x₀ x 0 ω).toNat + ∑ k ∈ range n, W k ω := fun n => by
      rw [integral_path_jumpTime hq hE' hmeas hgB, reward_visit_eq]
    have hR : ∀ n, R n = R 0 + ∑ k ∈ range n, cycleSum q (fun _ => 1) x₀ x k ω := fun n => by
      simp only [R]
      rw [← reward_one, ← reward_one, reward_visit_eq q (fun _ => 1) x₀ x ω n]
    have hR0 : 0 ≤ R 0 := (jumpTime_zero (q := q) (x := x) (ω := ω)).symm.le.trans
      (jumpTime_mono hq hE' (Nat.zero_le _))
    have hRlim : Tendsto (fun n : ℕ => R n / n) atTop atTop := by
      refine tendsto_atTop_mono' atTop ?_ hLω
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hsum : ∑ k ∈ range n, L' k ω = ∑ k ∈ range n, cycleSum q (fun _ => 1) x₀ x k ω :=
        sum_congr rfl fun k _ => max_eq_left (hposω k).le
      rw [hR n, hsum, add_div, inv_mul_eq_div]
      exact le_add_of_nonneg_left (div_nonneg hR0 hn'.le)
    refine tendsto_div_zero_of_renewal
      (F := fun t => ∫ s in (0 : ℝ)..t, g (JumpHold.path q x ω s)) (R := R) (by simp) ?_ hR0
      (strictMono_jumpTime_visit hq hE hallω) hRlim (tendsto_div_of_eq_add_sum' hF hWω)
    intro a ha b hb hab
    exact intervalIntegral.integral_mono_interval le_rfl ha hab
      (ae_of_all _ fun s => hg0 _) (intervalIntegrable_path hmeas hgB _ _)
  have h0 := eq_tsum_of_ae_tendsto K q g hq hg0 hg1 w hw hbal hfin hT hlim
  have hw' : w x₀ ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hw]; exact ENNReal.one_ne_top) (ENNReal.le_tsum x₀)
  simp only [hgdef, mul_ite, mul_one, mul_zero, tsum_ite_eq] at h0
  exact (ENNReal.toReal_pos hx₀ hw').ne h0

/-- **Ergodic theorem for a jump–hold chain with a balanced law.** Let `w` be a probability law
balancing the rate-weighted jump kernel (`∑_x w(x) q(x) K(x, y) = w(y) q(y)`) with
`∑ w q < ∞`, let the chain be non-explosive from every initial state, let `w(x₀) > 0`, and let
every state be reachable from `x₀` through jumps of positive probability. Then the chain started
at `x₀` returns to `x₀` almost surely, the mean return time is finite (positive recurrence), and
from every initial state the time averages of every bounded observable `f` converge almost
surely to `∑_y w(y) f(y)`. -/
theorem ergodic_of_balanced (q : σ → ℝ) (hq : ∀ y, 0 < q y) (w : σ → ℝ≥0∞)
    (hw : ∑' x, w x = 1)
    (hbal : ∀ y, ∑' x, w x * ENNReal.ofReal (q x) * K x y = w y * ENNReal.ofReal (q y))
    (hfin : ∑' x, w x * ENNReal.ofReal (q x) ≠ ⊤)
    (hT : ∀ x, ∀ᵐ ω ∂JumpHold.inputMeasure K, Tendsto (JumpHold.jumpTime q x ω) atTop atTop)
    {x₀ : σ} (hx₀ : w x₀ ≠ 0) (hirr : ∀ y, Relation.ReflTransGen (fun u v => K u v ≠ 0) x₀ y) :
    JumpHold.inputMeasure K {ω | visit x₀ x₀ 1 ω ≠ ⊤} = 1 ∧
      Integrable (returnReward q (fun _ => 1) x₀) (JumpHold.inputMeasure K) ∧
      ∀ (x : σ) (f : σ → ℝ) (B : ℝ), (∀ y, |f y| ≤ B) → ∀ᵐ ω ∂JumpHold.inputMeasure K,
        Tendsto (fun t => (∫ s in (0 : ℝ)..t, f (JumpHold.path q x ω s)) / t) atTop
          (𝓝 (∑' y, (w y).toReal * f y)) := by
  set μ := JumpHold.inputMeasure K
  have hp := measure_return_eq_one K q hq w hw hbal hfin hT hx₀
  have hall := fun x => ae_forall_visit_ne_top K hp hirr x
  have hret : ∀ᵐ ω ∂μ, visit x₀ x₀ 1 ω ≠ ⊤ := (hall x₀).mono fun ω h => h 1
  have hint := integrable_returnReward K q hq w hw hbal hfin hT hx₀ hall
  refine ⟨hp, hint, fun x f B hB => ?_⟩
  set B' : ℝ := |B| + 1 with hB'def
  have hB' : 0 < B' := by positivity
  set g : σ → ℝ := fun y => (f y + B') / (2 * B') with hgdef
  have hfB : ∀ y, |f y| < B' := fun y => (hB y).trans_lt (by linarith [le_abs_self B])
  have hg0 : ∀ y, 0 ≤ g y := fun y => by
    have := neg_lt_of_abs_lt (hfB y)
    simp only [hgdef]
    exact div_nonneg (by linarith) (by positivity)
  have hg1 : ∀ y, g y ≤ 1 := fun y => by
    have := lt_of_abs_lt (hfB y)
    simp only [hgdef]; rw [div_le_one (by positivity)]; linarith
  have hgB : ∀ y, |g y| ≤ 1 := fun y => by rw [abs_of_nonneg (hg0 y)]; exact hg1 y
  have hlimg := fun x' => ae_tendsto_of_integrable K q g hq hgB (hT x') (hall x') hret hint
  have hid := eq_tsum_of_ae_tendsto K q g hq hg0 hg1 w hw hbal hfin hT hlimg
  have hw' : ∀ y, w y ≠ ⊤ := fun y =>
    ne_top_of_le_ne_top (by rw [hw]; exact ENNReal.one_ne_top) (ENNReal.le_tsum y)
  have hwsum : Summable fun y => (w y).toReal :=
    ENNReal.summable_toReal (by rw [hw]; exact ENNReal.one_ne_top)
  have hwone : ∑' y, (w y).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq hw', hw, ENNReal.toReal_one]
  have hsg : Summable fun y => (w y).toReal * g y :=
    hwsum.of_nonneg_of_le (fun y => mul_nonneg ENNReal.toReal_nonneg (hg0 y))
      fun y => mul_le_of_le_one_right ENNReal.toReal_nonneg (hg1 y)
  have hfg : ∀ y, f y = 2 * B' * g y - B' := fun y => by simp only [hgdef]; field_simp; ring
  have htarget : ∑' y, (w y).toReal * f y = 2 * B' * ∑' y, (w y).toReal * g y - B' := by
    have h1 : ∑' y, (w y).toReal * f y =
        ∑' y, (2 * B' * ((w y).toReal * g y) - B' * (w y).toReal) :=
      tsum_congr fun y => by rw [hfg]; ring
    rw [h1, (hsg.mul_left _).tsum_sub (hwsum.mul_left _), tsum_mul_left, tsum_mul_left, hwone,
      mul_one]
  filter_upwards [hlimg x, JumpHold.ae_clock_nonneg K, hT x] with ω hω hE hTω
  rw [hid] at hω
  rw [htarget]
  have hmeas := measurable_path hq hE hTω
  have hlim2 := (hω.const_mul (2 * B')).sub_const B'
  refine hlim2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hint1 := intervalIntegrable_path hmeas hgB 0 t
  have hfeq : (fun s => f (JumpHold.path q x ω s)) =
      fun s => 2 * B' * g (JumpHold.path q x ω s) - B' := funext fun s => hfg _
  rw [hfeq, intervalIntegral.integral_sub (hint1.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  field_simp

end Ergodic

/-! ### Complex-balanced stochastic reaction networks -/

section CRN

open ComplexBalanced SystemsBiology StochasticCRNErgodicity

variable {S ρ : Type*} [Fintype S] [Fintype ρ]

omit [Fintype ρ] in
theorem propensity_eq_zero_of_not_le (N : ReactionNetwork S ρ) {κ : ρ → ℝ} {r : ρ}
    {x : S → ℕ} (h : ¬ N.src r ≤ x) : propensity N κ r x = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, x s < N.src r s := by
    by_contra h'
    push Not at h'
    exact h h'
  simp only [propensity]
  rw [Finset.prod_eq_zero (Finset.mem_univ s) (by simp [Nat.descFactorial_eq_zero_iff_lt.2 hs]),
    mul_zero]

omit [Fintype ρ] in
theorem propensity_nonneg_of_nonneg (N : ReactionNetwork S ρ) {κ : ρ → ℝ} (hκ : ∀ r, 0 ≤ κ r)
    (r : ρ) (x : S → ℕ) : 0 ≤ propensity N κ r x :=
  mul_nonneg (hκ r) (prod_nonneg fun _ _ => Nat.cast_nonneg _)

/-- The **stochastic mass-action chain** of the reaction network `N` with rate constants
`κ ≥ 0`: the `StochasticCRN` of `MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion` with the
mass-action propensities `SystemsBiology.propensity N κ`. -/
noncomputable def massAction (N : ReactionNetwork S ρ) (κ : ρ → ℝ) (hκ : ∀ r, 0 ≤ κ r) :
    StochasticCRN S ρ where
  network := N
  propensity := propensity N κ
  propensity_nonneg := propensity_nonneg_of_nonneg N hκ
  propensity_eq_zero _ _ h := propensity_eq_zero_of_not_le N h

omit [Fintype ρ] in
theorem jump_massAction (N : ReactionNetwork S ρ) (κ : ρ → ℝ) (hκ : ∀ r, 0 ≤ κ r) (r : ρ)
    (x : S → ℕ) : (massAction N κ hκ).jump r x = fire N r x := by
  funext s
  simp [StochasticCRN.jump, fire, massAction]

/-- The rate-weighted jump kernel of a stochastic CRN: `q(x) K(x, y)` is the total propensity of
the reactions leading from `x` to `y`, plus the fictitious self-loop at an absorbing state. -/
theorem ofReal_holdRate_mul_jumpPMF (M : StochasticCRN S ρ) (x y : S → ℕ) :
    ENNReal.ofReal (M.holdRate x) * M.jumpPMF x y =
      (∑ r, if M.jump r x = y then ENNReal.ofReal (M.propensity r x) else 0) +
        if M.totalRate x = 0 ∧ x = y then 1 else 0 := by
  by_cases h0 : M.totalRate x = 0
  · have hzero : ∀ r, M.propensity r x = 0 := fun r =>
      (Finset.sum_eq_zero_iff_of_nonneg fun r _ => M.propensity_nonneg r x).1 h0 r (mem_univ r)
    rw [StochasticCRN.jumpPMF, dite_eq_left h0, StochasticCRN.holdRate, ite_eq_left h0,
      PMF.pure_apply]
    simp only [hzero, ENNReal.ofReal_zero, ite_self, sum_const_zero, zero_add, ENNReal.ofReal_one,
      one_mul, h0, true_and]
    by_cases hxy : x = y
    · simp [hxy]
    · simp [hxy, Ne.symm hxy]
  · have hT : 0 < M.totalRate x := lt_of_le_of_ne (M.totalRate_nonneg x) (Ne.symm h0)
    rw [StochasticCRN.jumpPMF, dite_eq_right h0, PMF.map_apply, tsum_fintype, mul_sum]
    simp only [h0, false_and, ite_false, add_zero]
    refine sum_congr rfl fun r _ => ?_
    by_cases hr : M.jump r x = y
    · rw [ite_eq_left hr.symm, ite_eq_left hr, StochasticCRN.holdRate, ite_eq_right h0,
        StochasticCRN.reactionPMF,
        PMF.ofFintype_apply, ← ENNReal.ofReal_mul hT.le]
      congr 1
      field_simp
    · rw [ite_eq_right (Ne.symm hr), ite_eq_right hr, mul_zero]

omit [Fintype ρ] in
/-- The inflow along one reaction: `∑_x π(x) λ_r(x) [fire r x = y]` is the single term from the
predecessor `unfire r y`. -/
theorem tsum_ite_fire_eq (N : ReactionNetwork S ρ) {κ : ρ → ℝ} (c : S → ℝ) (r : ρ)
    (y : S → ℕ) :
    ∑' x, (if fire N r x = y then
        ENNReal.ofReal (poissonWeight c x * propensity N κ r x) else 0) =
      if N.prod r ≤ y then
        ENNReal.ofReal (poissonWeight c (unfire N r y) * propensity N κ r (unfire N r y))
      else 0 := by
  split_ifs with hy
  · rw [tsum_eq_single (unfire N r y)]
    · rw [ite_eq_left ((fire_eq_iff N (fun s => by simp [unfire])).2 ⟨hy, rfl⟩)]
    · intro x hx
      split_ifs with hj
      · by_cases hs : N.src r ≤ x
        · exact absurd ((fire_eq_iff N hs).1 hj).2 hx
        · rw [propensity_eq_zero_of_not_le N hs, mul_zero, ENNReal.ofReal_zero]
      · rfl
  · refine ENNReal.tsum_eq_zero.2 fun x => ?_
    split_ifs with hj
    · exfalso
      apply hy
      rw [← hj]
      intro s
      simp [fire]
    · rfl

/-- **Balance of the product-form law for the jump–hold chain**: complex balance makes the
Poisson weights balance the rate-weighted jump kernel of the stochastic mass-action chain,
`∑_x π_c(x) q(x) K(x, y) = π_c(y) q(y)` (the stationary master equation
`isStationaryMasterSolution_poissonWeight`, with the self-loops of absorbing states). -/
theorem tsum_poissonWeight_mul_holdRate_mul_jumpPMF (N : ReactionNetwork S ρ) {κ : ρ → ℝ}
    (hκ : ∀ r, 0 ≤ κ r) {c : S → ℝ} (hcb : N.IsComplexBalanced κ c) (hc : ∀ s, 0 ≤ c s)
    (y : S → ℕ) :
    ∑' x, ENNReal.ofReal (poissonWeight c x) *
        ENNReal.ofReal ((massAction N κ hκ).holdRate x) * (massAction N κ hκ).jumpPMF x y =
      ENNReal.ofReal (poissonWeight c y) * ENNReal.ofReal ((massAction N κ hκ).holdRate y) := by
  set M := massAction N κ hκ
  have hπ := poissonWeight_nonneg hc
  have h1 : ∀ x, ENNReal.ofReal (poissonWeight c x) * ENNReal.ofReal (M.holdRate x) *
      M.jumpPMF x y = (∑ r, if fire N r x = y then
        ENNReal.ofReal (poissonWeight c x * propensity N κ r x) else 0) +
      ENNReal.ofReal (poissonWeight c x) * (if M.totalRate x = 0 ∧ x = y then 1 else 0) := by
    intro x
    rw [mul_assoc, ofReal_holdRate_mul_jumpPMF, mul_add, mul_sum]
    refine congrArg₂ (· + ·) (sum_congr rfl fun r _ => ?_) rfl
    rw [jump_massAction]
    split_ifs
    · rw [← ENNReal.ofReal_mul (hπ x)]; rfl
    · rw [mul_zero]
  simp only [h1]
  rw [ENNReal.tsum_add, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp only [tsum_ite_fire_eq]
  rw [tsum_eq_single y (fun x hx => by simp [hx])]
  have hmaster := isStationaryMasterSolution_poissonWeight N hcb y
  have hsum : (∑ r, if N.prod r ≤ y then ENNReal.ofReal (poissonWeight c (unfire N r y) *
      propensity N κ r (unfire N r y)) else 0) =
      ENNReal.ofReal (poissonWeight c y * M.totalRate y) := by
    rw [← sum_filter, ← ENNReal.ofReal_sum_of_nonneg fun r _ =>
      mul_nonneg (hπ _) (propensity_nonneg_of_nonneg N hκ r _)]
    congr 1
    rw [← hmaster]
    rfl
  rw [hsum]
  by_cases h0 : M.totalRate y = 0
  · simp [StochasticCRN.holdRate, h0]
  · simp only [h0, false_and, ite_false, mul_zero, add_zero, StochasticCRN.holdRate]
    exact ENNReal.ofReal_mul (hπ y)

theorem hasSum_poisson_mul_descFactorial (a : ℝ) (k : ℕ) :
    HasSum (fun n : ℕ => a ^ n * Real.exp (-a) / n.factorial * (n.descFactorial k : ℝ))
      (a ^ k) := by
  have hp : HasSum (fun n : ℕ => a ^ n * Real.exp (-a) / n.factorial) 1 := by
    have h1 : HasSum (fun n : ℕ => a ^ n / n.factorial) (Real.exp a) := by
      rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp a
    have h2 := h1.mul_right (Real.exp (-a))
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2
    exact h2.congr_fun fun n => by ring
  set F : ℕ → ℝ := fun n => a ^ n * Real.exp (-a) / n.factorial * (n.descFactorial k : ℝ)
    with hFdef
  have hp' : HasSum (fun n : ℕ => a ^ k * (a ^ n * Real.exp (-a) / n.factorial)) (a ^ k) := by
    simpa using hp.mul_left (a ^ k)
  have hshift : HasSum (fun n : ℕ => F (n + k)) (a ^ k) := by
    refine hp'.congr_fun fun n => ?_
    simp only [hFdef]
    have hf : ((n + k).factorial : ℝ) = (n.factorial : ℝ) * ((n + k).descFactorial k : ℝ) := by
      have := Nat.factorial_mul_descFactorial (show k ≤ n + k by omega)
      rw [Nat.add_sub_cancel] at this
      exact_mod_cast this.symm
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    have hd : ((n + k).descFactorial k : ℝ) ≠ 0 := by
      have := Nat.factorial_mul_descFactorial (show k ≤ n + k by omega)
      intro h0
      rw [h0, mul_zero] at hf
      exact (Nat.factorial_ne_zero (n + k)) (by exact_mod_cast hf)
    rw [hf, pow_add]
    field_simp
  have hzero : ∑ i ∈ range k, F i = 0 :=
    sum_eq_zero fun i hi => by
      simp [hFdef, Nat.descFactorial_eq_zero_iff_lt.2 (mem_range.1 hi)]
  have := (hasSum_nat_add_iff k).1 hshift
  rwa [hzero, add_zero] at this

omit [Fintype ρ] in
theorem hasSum_poissonWeight_mul_propensity (N : ReactionNetwork S ρ) (κ : ρ → ℝ) {c : S → ℝ}
    (hc : ∀ s, 0 ≤ c s) (r : ρ) :
    HasSum (fun x => poissonWeight c x * propensity N κ r x) (κ r * ∏ s, c s ^ N.src r s) := by
  have h := MetaMathlibExt.hasSum_prod_pi
    (f := fun s (n : ℕ) => c s ^ n * Real.exp (-c s) / (n.factorial : ℝ) *
      (n.descFactorial (N.src r s) : ℝ))
    (a := fun s => c s ^ N.src r s) (fun s n => by have := hc s; positivity)
    fun s => hasSum_poisson_mul_descFactorial (c s) _
  have h' : HasSum (fun x : S → ℕ => κ r * ∏ s, (c s ^ x s * Real.exp (-c s) / (x s).factorial *
      ((x s).descFactorial (N.src r s) : ℝ))) (κ r * ∏ s, c s ^ N.src r s) := h.mul_left (κ r)
  refine h'.congr_fun fun x => ?_
  simp only [poissonWeight, propensity]
  rw [mul_left_comm, ← prod_mul_distrib]

theorem tsum_ofReal_poissonWeight_mul_holdRate_ne_top (N : ReactionNetwork S ρ) {κ : ρ → ℝ}
    (hκ : ∀ r, 0 ≤ κ r) {c : S → ℝ} (hc : ∀ s, 0 ≤ c s) :
    ∑' x, ENNReal.ofReal (poissonWeight c x) * ENNReal.ofReal ((massAction N κ hκ).holdRate x) ≠
      ⊤ := by
  set M := massAction N κ hκ
  have hπ := poissonWeight_nonneg hc
  set G : (S → ℕ) → ℝ := fun x => ∑ r, poissonWeight c x * propensity N κ r x + poissonWeight c x
  have hG : Summable G :=
    (summable_sum fun r _ => (hasSum_poissonWeight_mul_propensity N κ hc r).summable).add
      (hasSum_poissonWeight hc).summable
  have hG0 : ∀ x, 0 ≤ G x := fun x =>
    add_nonneg (sum_nonneg fun r _ => mul_nonneg (hπ x) (propensity_nonneg_of_nonneg N hκ r x))
      (hπ x)
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' x, G x)) ?_
  rw [ENNReal.ofReal_tsum_of_nonneg hG0 hG]
  refine ENNReal.tsum_le_tsum fun x => ?_
  rw [← ENNReal.ofReal_mul (hπ x)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hq : M.holdRate x ≤ M.totalRate x + 1 := by
    unfold StochasticCRN.holdRate
    split_ifs with h
    · rw [h]; norm_num
    · linarith
  calc poissonWeight c x * M.holdRate x ≤ poissonWeight c x * (M.totalRate x + 1) :=
        mul_le_mul_of_nonneg_left hq (hπ x)
    _ = G x := by simp only [G, StochasticCRN.totalRate, mul_add, mul_sum, mul_one]; rfl

/-- Reachability along reactions with positive propensity is reachability in the jump kernel. -/
theorem reflTransGen_jumpPMF (N : ReactionNetwork S ρ) {κ : ρ → ℝ} (hκ : ∀ r, 0 ≤ κ r)
    {u v : S → ℕ}
    (h : Relation.ReflTransGen (fun u v => ∃ r, 0 < propensity N κ r u ∧ fire N r u = v) u v) :
    Relation.ReflTransGen (fun u v => (massAction N κ hκ).jumpPMF u v ≠ 0) u v := by
  refine Relation.ReflTransGen.mono (fun a b hab' => ?_) u v h
  obtain ⟨r, hr, hab⟩ := hab'
  set M := massAction N κ hκ
  have hT : M.totalRate a ≠ 0 := by
    refine (lt_of_lt_of_le hr ?_).ne'
    exact single_le_sum (f := fun r => M.propensity r a) (fun r _ => M.propensity_nonneg r a)
      (mem_univ r)
  rw [← PMF.mem_support_iff, StochasticCRN.jumpPMF, dite_eq_right hT, PMF.mem_support_map_iff]
  refine ⟨r, ?_, by rw [jump_massAction]; exact hab⟩
  rw [PMF.mem_support_iff, StochasticCRN.reactionPMF, PMF.ofFintype_apply, ne_eq,
    ENNReal.ofReal_eq_zero, not_le]
  exact div_pos hr (lt_of_le_of_ne (M.totalRate_nonneg a) (Ne.symm hT))

/-- **Non-explosion in the form of `StochasticCRNErgodicity.NoExplosion`.** If the jump times of
the chain tend to `∞` (`StochasticCRNNonExplosion`), its path stays bounded on bounded time
intervals. This connects the two formulations of non-explosion. -/
theorem noExplosion_path (M : StochasticCRN S ρ) (x : S → ℕ)
    (hT : ∀ᵐ ω ∂M.inputMeasure, Tendsto (M.jumpTime x ω) atTop atTop) :
    NoExplosion M.inputMeasure (fun s ω => M.path x ω s) := by
  filter_upwards [JumpHold.ae_clock_nonneg M.jumpPMF, hT] with ω hE hTω
  intro t
  obtain ⟨n, hn⟩ := (hTω.eventually_gt_atTop t).exists
  refine ⟨∑ k ∈ range n, ∑ i, ctmcJumpChain x ω k i, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨k, hk1, hk2⟩ := exists_jumpTime_le_lt (q := M.holdRate) hTω hs.1
  have hkn : k < n := by
    by_contra h
    have := jumpTime_mono (x := x) M.holdRate_pos hE (not_lt.1 h)
    have : JumpHold.jumpTime M.holdRate x ω n ≤ s := this.trans hk1
    exact absurd (this.trans hs.2) (not_le.2 hn)
  simp only
  rw [StochasticCRN.path, JumpHold.path_eq_ctmcJumpChain M.holdRate_pos hE hk1 hk2]
  exact single_le_sum (f := fun k => ∑ i, ctmcJumpChain x ω k i) (fun _ _ => Nat.zero_le _)
    (mem_range.2 hkn)

/-- **The forward-equation transfer, in Laplace form.** For a complex-balanced network whose
chain is non-explosive (drift bound `L V ≤ a V + b`, `∑_s x_s ≤ V(x)`), the product-form law
`π_c` is stationary for the chain in the Laplace sense: for every `a > 0` and `0 ≤ g ≤ 1`,
`∑_x π_c(x) E_x[∫_0^∞ a e^{-a t} g(X_t) dt] = ∑_x π_c(x) g(x)`. For `g` the indicator of a state
`y` this says that `t ↦ P_{π_c}(X_t = y)` has the Laplace transform of the constant `π_c(y)`;
the fixed-time identity `P_{π_c}(X_t = y) = π_c(y)` (the hypothesis `htransfer` of
`StochasticCRNErgodicity.ergodic_of_isComplexBalanced`) would follow by uniqueness of Laplace
transforms, which is not proved here. -/
theorem tsum_poissonWeight_mul_lintegral_laplace_path (N : ReactionNetwork S ρ) {κ : ρ → ℝ}
    (hκ : ∀ r, 0 ≤ κ r) {c : S → ℝ} (hcb : N.IsComplexBalanced κ c) (hc : ∀ s, 0 ≤ c s)
    (V : (S → ℕ) → ℝ≥0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdrift : ∀ x, (massAction N κ hκ).generator (fun y => (V y : ℝ)) x ≤ a * V x + b)
    (hcoer : ∀ x, (∑ s, (x s : ℝ)) ≤ V x) {g : (S → ℕ) → ℝ} (hg0 : ∀ y, 0 ≤ g y)
    (hg1 : ∀ y, g y ≤ 1) {θ : ℝ} (hθ : 0 < θ) :
    ∑' x, ENNReal.ofReal (poissonWeight c x) *
        ∫⁻ ω, (∫⁻ t in Set.Ioi 0, ENNReal.ofReal (θ * Real.exp (-(θ * t)) *
          g ((massAction N κ hκ).path x ω t))) ∂(massAction N κ hκ).inputMeasure =
      ∑' x, ENNReal.ofReal (poissonWeight c x) * ENNReal.ofReal (g x) := by
  set M := massAction N κ hκ
  have hT := fun x => M.ae_tendsto_jumpTime_atTop_of_coercive V ha hb hdrift hcoer x
  rw [← tsum_mul_lintegral_abelSum M.jumpPMF M.holdRate g M.holdRate_pos hg1 hθ _
    (tsum_poissonWeight_mul_holdRate_mul_jumpPMF N hκ hcb hc)
    (tsum_ofReal_poissonWeight_mul_holdRate_ne_top N hκ hc)]
  refine tsum_congr fun x => ?_
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [JumpHold.ae_clock_nonneg M.jumpPMF, hT x] with ω hE hTω
  exact lintegral_exp_path_eq_abelSum M.holdRate_pos hE hTω hg0 hθ

/-- **Ergodic theorem for complex-balanced stochastic reaction networks, with the forward
equation and the regeneration proved.** Let `c > 0` be complex balanced for the rate constants
`κ ≥ 0`, let the stochastic mass-action chain satisfy a Foster–Lyapunov drift bound
`L V ≤ a V + b` with `∑_s x_s ≤ V(x)` (non-explosion, `StochasticCRNNonExplosion`), and let every
state be reachable from `x₀` along reactions with positive propensity. Then for the chain built
by the jump–hold construction:

* it returns to `x₀` almost surely, and the mean return time to `x₀` is finite (positive
  recurrence);
* from every initial state `x`, the time averages `t⁻¹ ∫₀ᵗ f (X s) ds` of every bounded
  observable converge almost surely to the product-form mean `∑_y π_c(y) f(y)`.

Compared with `StochasticCRNErgodicity.ergodic_of_isComplexBalanced`, the transfer of the
stationary master equation to the chain (in Laplace form, `tsum_mul_lintegral_abelSum`) and the
regeneration at `x₀` (recurrence `measure_return_eq_one`, i.i.d. cycles
`identDistrib_cycleSum`, `indepFun_cycleSum_of_lt`) are proved, not assumed. -/
theorem ergodic_of_isComplexBalanced_of_reachable (N : ReactionNetwork S ρ) {κ : ρ → ℝ}
    (hκ : ∀ r, 0 ≤ κ r) {c : S → ℝ} (hcb : N.IsComplexBalanced κ c) (hc : ∀ s, 0 < c s)
    (V : (S → ℕ) → ℝ≥0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdrift : ∀ x, (massAction N κ hκ).generator (fun y => (V y : ℝ)) x ≤ a * V x + b)
    (hcoer : ∀ x, (∑ s, (x s : ℝ)) ≤ V x) (x₀ : S → ℕ)
    (hreach : ∀ y, Relation.ReflTransGen
      (fun u v => ∃ r, 0 < propensity N κ r u ∧ fire N r u = v) x₀ y) :
    (massAction N κ hκ).inputMeasure {ω | visit x₀ x₀ 1 ω ≠ ⊤} = 1 ∧
      Integrable (fun ω => (massAction N κ hκ).jumpTime x₀ ω (visit x₀ x₀ 1 ω).toNat)
        (massAction N κ hκ).inputMeasure ∧
      ∀ (x : S → ℕ) (f : (S → ℕ) → ℝ) (B : ℝ), (∀ y, |f y| ≤ B) →
        ∀ᵐ ω ∂(massAction N κ hκ).inputMeasure,
          Tendsto (fun t => occupation (fun s ω => (massAction N κ hκ).path x ω s) f t ω / t)
            atTop (𝓝 (∑' y, poissonWeight c y * f y)) := by
  set M := massAction N κ hκ
  have hc0 : ∀ s, 0 ≤ c s := fun s => (hc s).le
  have hπ := poissonWeight_nonneg hc0
  have hw : ∑' x, ENNReal.ofReal (poissonWeight c x) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hπ (hasSum_poissonWeight hc0).summable,
      (hasSum_poissonWeight hc0).tsum_eq, ENNReal.ofReal_one]
  have hT : ∀ x, ∀ᵐ ω ∂JumpHold.inputMeasure M.jumpPMF,
      Tendsto (JumpHold.jumpTime M.holdRate x ω) atTop atTop := fun x =>
    M.ae_tendsto_jumpTime_atTop_of_coercive V ha hb hdrift hcoer x
  have hx₀ : ENNReal.ofReal (poissonWeight c x₀) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact poissonWeight_pos hc x₀
  obtain ⟨hp, hint, hlim⟩ := ergodic_of_balanced M.jumpPMF M.holdRate M.holdRate_pos
    (fun x => ENNReal.ofReal (poissonWeight c x)) hw
    (tsum_poissonWeight_mul_holdRate_mul_jumpPMF N hκ hcb hc0)
    (tsum_ofReal_poissonWeight_mul_holdRate_ne_top N hκ hc0) hT hx₀
    (fun y => reflTransGen_jumpPMF N hκ (hreach y))
  refine ⟨hp, ?_, fun x f B hB => ?_⟩
  · refine hint.congr (ae_of_all _ fun ω => ?_)
    simp only [returnReward, reward_one]
    rfl
  · filter_upwards [hlim x f B hB] with ω hω
    simp only [ENNReal.toReal_ofReal (hπ _)] at hω
    exact hω

/-- **The same limit from the product-form initial law.** For the chain started from `π_c` (an
initial state drawn from `countLaw π_c`, independent of the steps), the time averages of every
bounded observable converge almost surely to `∑_y π_c(y) f(y)`; this is the conclusion of
`StochasticCRNErgodicity.ergodic_of_isComplexBalanced` with its hypotheses `htransfer`, `hreg`
and `hnonexp` replaced by complex balance, reachability and a drift bound. -/
theorem ergodic_of_isComplexBalanced_of_reachable_countLaw (N : ReactionNetwork S ρ)
    {κ : ρ → ℝ} (hκ : ∀ r, 0 ≤ κ r) {c : S → ℝ} (hcb : N.IsComplexBalanced κ c)
    (hc : ∀ s, 0 < c s) (V : (S → ℕ) → ℝ≥0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdrift : ∀ x, (massAction N κ hκ).generator (fun y => (V y : ℝ)) x ≤ a * V x + b)
    (hcoer : ∀ x, (∑ s, (x s : ℝ)) ≤ V x) (x₀ : S → ℕ)
    (hreach : ∀ y, Relation.ReflTransGen
      (fun u v => ∃ r, 0 < propensity N κ r u ∧ fire N r u = v) x₀ y)
    (f : (S → ℕ) → ℝ) (B : ℝ) (hB : ∀ y, |f y| ≤ B) :
    ∀ᵐ z ∂(countLaw (poissonWeight c)).prod (massAction N κ hκ).inputMeasure,
      Tendsto (fun t => occupation (fun s z => (massAction N κ hκ).path z.1 z.2 s) f t z / t)
        atTop (𝓝 (∑' y, poissonWeight c y * f y)) := by
  set μ := (massAction N κ hκ).inputMeasure
  have hlim := (ergodic_of_isComplexBalanced_of_reachable N hκ hcb hc V ha hb hdrift hcoer x₀
    hreach).2.2
  set P : (S → ℕ) → (ℕ → ((S → ℕ) → (S → ℕ)) × ℝ) → Prop := fun x ω =>
    Tendsto (fun t => occupation (fun s ω => (massAction N κ hκ).path x ω s) f t ω / t)
      atTop (𝓝 (∑' y, poissonWeight c y * f y))
  have hnull : ∀ x, μ (toMeasurable μ {ω | ¬ P x ω}) = 0 := fun x => by
    rw [measure_toMeasurable]; exact ae_iff.1 (hlim x f B hB)
  rw [ae_iff]
  refine measure_mono_null (t := ⋃ x, {x} ×ˢ toMeasurable μ {ω | ¬ P x ω}) ?_
    (measure_iUnion_null fun x => ?_)
  · intro z hz
    exact Set.mem_iUnion.2 ⟨z.1, Set.mem_prod.2 ⟨rfl, subset_toMeasurable _ _ hz⟩⟩
  · rw [Measure.prod_prod, hnull x, mul_zero]

end CRN

end MathlibExt.Biology.Dynamics.StochasticCRNRegeneration
