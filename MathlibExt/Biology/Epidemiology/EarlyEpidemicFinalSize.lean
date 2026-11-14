/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Epidemiology.EarlyEpidemicBranching
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Topology.Order.Compact

/-!
# Final size of the early epidemic

The generation-based SIR epidemic of `MathlibExt.Biology.Epidemiology.EarlyEpidemicBranching`
is started by one index case in a population `Fin N` with initially susceptible individuals
`S₀`; the `i`-th infective of generation `n` makes `ξ n i` contacts and contact number `j` goes to
`U j`. That file proves that a major outbreak (survival for every number of generations in the
large-population limit) has probability `1 - q`, `q` the extinction probability of the
offspring law `ν`, but says nothing about how many individuals are ultimately infected. This file
proves the **final-size limit**: as `N → ∞`, the fraction of the population ultimately infected
converges in law to `q δ₀ + (1 - q) δ_τ`, where `τ ∈ (0, 1)` is the non-zero root of the
final-size equation `1 - τ = e^{-R₀ τ}`, `R₀ = mean ν > 1`.

## Setting

* `finalSize ξ U S₀`: the number of individuals of the population ever infected (the index case
  is not counted), i.e. the number of hits among all `totalContacts ξ U S₀` contacts.
* `IsFinalSizeEpidemic`: the hypotheses `IsEarlyEpidemic`, together with measurable targets that
  are independent of the offspring numbers. `IsEarlyEpidemic` makes no assumption on the joint
  law of `ξ` and `U`, and without one the final size is not determined by `ν` and `N`.
* The offspring law has a finite second moment, `Integrable (fun k => (k : ℝ) ^ 2) ν`; its mean
  `offspringMean ν = (mean ν).toReal` and variance `offspringVar ν` are finite.
* Along a sequence of models `k`, `N k → ∞` and `N k - #S₀ k = o(N k)`, as in the
  large-population results of the early-epidemic file.

## Main results

* `finalSizeRoot R`, `one_sub_finalSizeRoot`, `eq_finalSizeRoot`: for `R > 1`, the final-size
  equation `1 - x = e^{-R x}` has exactly one positive root `τ = finalSizeRoot R ∈ (0, 1)`.
* `tendsto_measureReal_finalSize_far`: with probability tending to `1`, the fraction `F / N`
  ultimately infected is below `δ` or within `δ` of `τ`.
* `exists_eventually_measureReal_finalSize_lt_le`, `eventually_le_measureReal_finalSize_lt`:
  the probability that `F < δ N` is eventually at most `q + θ`, for some `δ > 0`, and at least
  `q - θ`, for every `δ > 0`.
* `tendsto_measureReal_finalSize_div_lt`: `P(F / N < δ) → q` for `0 < δ < τ`.
* `tendsto_measureReal_abs_finalSize_div_sub_lt`: `P(|F / N - τ| < δ) → 1 - q` for
  `0 < δ < τ`. The major outbreaks of the early-epidemic file, of probability `1 - q`, are
  therefore exactly the outbreaks that infect a fraction `≈ τ` of the population.
* `isFinalSizeEpidemic_canonical`: the hypotheses are satisfiable (product-space model).

## Proof

* *Deterministic identities*: `F = hits(C)` where `C = totalContacts` is the sum of the contact
  numbers of the `F + 1` infectives (`finalSize_eq_hits`, `totalContacts_eq_sum`,
  `sum_epiSize_eq_finalSize_add_one`).
* *Contact counts*: the centered count `truncDev`, which sums `ξ n i - R₀` over the infectives
  of the generations holding at most `L` infectives, has `E[truncDev²] ≤ σ² L`
  (`integral_truncDev_sq_le`): each offspring number is independent of everything that decides
  whether it is used (`integral_mul_offspring`), so the increments are orthogonal.
* *Occupancy*: the number of hits among `c` contacts has variance at most `#S₀`
  (`measureReal_le_abs_hits_sub`), and monotonicity in `c` makes the law of large numbers
  `hits(c) ≈ N (1 - e^{-c/N})` uniform in `c ≤ K N` (`tendsto_measureReal_exists_abs_hits_sub`).
* *Large outbreaks*: combining both, `x = F / N` solves `1 - e^{-R₀ x} = x` up to `o(1)`, so it
  is close to `0` or to `τ` (`exists_pos_forall_abs_finalSizeGap_le`).
* *Small outbreaks*: on the dyadic block `2^j ≤ F < 2^{j+1}` the `C - F ≈ (R₀ - 1) F` contacts
  that do not hit must go outside `S₀` or repeat (`dyadic_case_split`); the probabilities of these
  blocks are summable (`measureReal_dyadic_le`), and an outbreak with fewer than `K` infections
  is a branching-process extinction unless one of the first `K` contacts is wasted
  (`exists_bpSize_eq_zero_of_finalSize_lt`), which has probability `O(K² / N)`.

## References

* F. Ball, P. Donnelly, *Strong approximations for epidemic models*, Stochastic Process. Appl.
  55 (1995), 1–21.
* B. von Bahr, A. Martin-Löf, *Threshold limit theorems for some epidemic processes*, Adv.
  Appl. Probab. 12 (1980), 319–349.
* H. Andersson, T. Britton, *Stochastic Epidemic Models and Their Statistical Analysis*,
  Lecture Notes in Statistics 151, Springer (2000), ch. 4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

namespace MathlibExt.Biology.Epidemiology.EarlyEpidemicFinalSize

open MathlibExt.Probability MathlibExt.Probability.GaltonWatson
open MathlibExt.Biology.Epidemiology.EarlyEpidemicBranching

/-! ### Deterministic final size -/

section Deterministic

variable (ξ : ℕ → ℕ → ℕ) {α : Type*} [DecidableEq α] (U : ℕ → α) (S₀ : Finset α)

/-- After extinction the state of the epidemic no longer changes. -/
theorem epi_eq_of_epiSize_eq_zero {n n' : ℕ} (hnn' : n ≤ n') (h : epiSize ξ U S₀ n = 0) :
    epi ξ U S₀ n' = epi ξ U S₀ n := by
  induction n', hnn' using Nat.le_induction with
  | base => rfl
  | succ n' _ ih =>
    have h' : (epi ξ U S₀ n').1 = 0 := by rw [ih]; exact h
    have h0 : (epi ξ U S₀ n).1 = 0 := h
    simp only [epi, h', range_zero, sum_empty, add_zero, Ico_self, filter_empty, card_empty]
    rw [ih]
    exact Prod.ext h0.symm rfl

/-- The epidemic is over by generation `#S₀ + 1`. -/
theorem epi_eq_epi_card_add_one {n : ℕ} (hn : S₀.card + 1 ≤ n) :
    epi ξ U S₀ n = epi ξ U S₀ (S₀.card + 1) :=
  epi_eq_of_epiSize_eq_zero ξ U S₀ hn (epiSize_card_add_one_eq_zero ξ U S₀)

/-- The contacts made by generations `0, …, n - 1` of the epidemic. -/
theorem epi_snd_eq_sum (n : ℕ) :
    (epi ξ U S₀ n).2 = ∑ m ∈ range n, ∑ i ∈ range (epiSize ξ U S₀ m), ξ m i := by
  induction n with
  | zero => simp [epi]
  | succ n ih => rw [sum_range_succ, ← ih]; rfl

/-- The total number of contacts made during the epidemic. -/
def totalContacts : ℕ :=
  (epi ξ U S₀ (S₀.card + 1)).2

/-- The *final size* of the epidemic: the number of individuals of the population who are ever
infected, i.e. the number of contacts that hit (the index case is not counted). -/
def finalSize : ℕ :=
  ((range (totalContacts ξ U S₀)).filter (epiHit U S₀)).card

/-- The final size is the total number of infectives of generations `1, 2, …`. -/
theorem finalSize_eq_sum : finalSize ξ U S₀ = ∑ m ∈ range (S₀.card + 1), epiSize ξ U S₀ (m + 1) :=
  (sum_epiSize_eq_card ξ U S₀ _).symm

/-- At most `#S₀` individuals are ever infected. -/
theorem finalSize_le_card : finalSize ξ U S₀ ≤ S₀.card :=
  card_filter_epiHit_le U S₀ _

/-- The infectives of all generations, index case included, number `finalSize + 1`. -/
theorem sum_epiSize_eq_finalSize_add_one :
    ∑ m ∈ range (S₀.card + 1), epiSize ξ U S₀ m = finalSize ξ U S₀ + 1 := by
  rw [finalSize_eq_sum, sum_range_succ', sum_range_succ (fun m => epiSize ξ U S₀ (m + 1)),
    epiSize_card_add_one_eq_zero]
  rfl

/-- The total number of contacts is the sum of the contact numbers of all infectives. -/
theorem totalContacts_eq_sum : totalContacts ξ U S₀ =
    ∑ m ∈ range (S₀.card + 1), ∑ i ∈ range (epiSize ξ U S₀ m), ξ m i :=
  epi_snd_eq_sum ξ U S₀ _

/-- If the epidemic is extinct by generation `n`, fewer individuals than the infectives of
generations `0, …, n - 1` are ever infected. -/
theorem finalSize_lt_of_epiSize_eq_zero {n : ℕ} (h : epiSize ξ U S₀ n = 0) :
    finalSize ξ U S₀ < ∑ m ∈ range n, epiSize ξ U S₀ m := by
  have hC : totalContacts ξ U S₀ = (epi ξ U S₀ n).2 := by
    rw [totalContacts, ← epi_eq_epi_card_add_one ξ U S₀ (le_max_right n _),
      epi_eq_of_epiSize_eq_zero ξ U S₀ (le_max_left n _) h]
  have h1 := sum_epiSize_eq_card ξ U S₀ n
  have h2 : ∑ m ∈ range (n + 1), epiSize ξ U S₀ m =
      ∑ m ∈ range n, epiSize ξ U S₀ (m + 1) + 1 := by
    rw [sum_range_succ']; rfl
  rw [sum_range_succ, h, add_zero] at h2
  rw [finalSize, hC, ← h1]
  omega

end Deterministic

/-! ### The final-size equation -/

section FinalSizeEquation

/-- The final-size function `g(x) = 1 - e^{-R x} - x`; its zeros are the solutions of the
final-size equation `1 - x = e^{-R x}`. -/
noncomputable def finalSizeGap (R x : ℝ) : ℝ :=
  1 - Real.exp (-(R * x)) - x

theorem continuous_finalSizeGap (R : ℝ) : Continuous (finalSizeGap R) := by
  unfold finalSizeGap; fun_prop

theorem finalSizeGap_zero (R : ℝ) : finalSizeGap R 0 = 0 := by
  simp [finalSizeGap]

/-- For `R > 1` the final-size equation has a root in `(0, 1)`. -/
theorem exists_finalSizeGap_eq_zero {R : ℝ} (hR : 1 < R) :
    ∃ x, 0 < x ∧ x < 1 ∧ finalSizeGap R x = 0 := by
  have hR0 : 0 < R := by linarith
  set x₀ := (R - 1) / (2 * R ^ 2) with hx₀
  have hx₀pos : 0 < x₀ := by positivity
  have hRx₀ : R * x₀ = (R - 1) / (2 * R) := by rw [hx₀]; field_simp
  have hRx₀le : R * x₀ ≤ 1 / 2 := by
    rw [hRx₀, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hx₀lt : x₀ < 1 := by
    have : x₀ ≤ R * x₀ := le_mul_of_one_le_left hx₀pos.le hR.le
    linarith
  have hg₀ : 0 ≤ finalSizeGap R x₀ := by
    have hb := Real.abs_exp_sub_one_sub_id_le (x := -(R * x₀)) (by
      rw [abs_neg, abs_of_pos (by positivity)]; linarith)
    have hb' := (abs_le.1 hb).2
    have : R ^ 2 * x₀ = (R - 1) / 2 := by rw [hx₀]; field_simp
    unfold finalSizeGap
    nlinarith
  have hg₁ : finalSizeGap R 1 < 0 := by
    unfold finalSizeGap; have := Real.exp_pos (-(R * 1)); linarith
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc' hx₀lt.le
    (continuous_finalSizeGap R).continuousOn ⟨hg₁.le, hg₀⟩
  refine ⟨x, hx₀pos.trans_le hx.1, lt_of_le_of_ne hx.2 ?_, hgx⟩
  rintro rfl
  exact hg₁.ne hgx

/-- For `R > 0` the final-size equation has at most one positive root. -/
theorem eq_of_finalSizeGap_eq_zero {R x y : ℝ} (hR : 0 < R) (hx : 0 < x) (hy : 0 < y)
    (hgx : finalSizeGap R x = 0) (hgy : finalSizeGap R y = 0) : x = y := by
  wlog hxy : x < y generalizing x y
  · rcases (not_lt.1 hxy).eq_or_lt with h | h
    · exact h.symm
    · exact (this hy hx hgy hgx h).symm
  set t := x / y with ht
  have ht0 : 0 < t := div_pos hx hy
  have ht1 : t < 1 := (div_lt_one hy).2 hxy
  have hxt : x = t * y := by rw [ht]; field_simp
  have hconv := strictConvexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-(R * y)))
    (by have : 0 < R * y := mul_pos hR hy; linarith) (by linarith : 0 < 1 - t) ht0
    (by ring : 1 - t + t = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hconv
  have he : Real.exp (t * -(R * y)) = Real.exp (-(R * x)) := by rw [hxt]; ring_nf
  rw [he] at hconv
  unfold finalSizeGap at hgx hgy
  nlinarith

/-- The non-zero root `τ ∈ (0, 1)` of the final-size equation `1 - τ = e^{-R τ}` (for `R > 1`;
`0` otherwise, where `0` is the only root in `[0, 1]`). -/
noncomputable def finalSizeRoot (R : ℝ) : ℝ :=
  if h : 1 < R then Classical.choose (exists_finalSizeGap_eq_zero h) else 0

theorem finalSizeRoot_spec {R : ℝ} (hR : 1 < R) :
    0 < finalSizeRoot R ∧ finalSizeRoot R < 1 ∧ finalSizeGap R (finalSizeRoot R) = 0 := by
  simp only [finalSizeRoot, hR, ↓reduceDIte]
  exact Classical.choose_spec (exists_finalSizeGap_eq_zero hR)

theorem finalSizeRoot_pos {R : ℝ} (hR : 1 < R) : 0 < finalSizeRoot R :=
  (finalSizeRoot_spec hR).1

theorem finalSizeRoot_lt_one {R : ℝ} (hR : 1 < R) : finalSizeRoot R < 1 :=
  (finalSizeRoot_spec hR).2.1

/-- `τ` solves the final-size equation `1 - τ = e^{-R τ}`. -/
theorem one_sub_finalSizeRoot {R : ℝ} (hR : 1 < R) :
    1 - finalSizeRoot R = Real.exp (-(R * finalSizeRoot R)) := by
  have := (finalSizeRoot_spec hR).2.2
  unfold finalSizeGap at this
  linarith

/-- `τ` is the only positive root of the final-size equation. -/
theorem eq_finalSizeRoot {R x : ℝ} (hR : 1 < R) (hx : 0 < x)
    (h : 1 - x = Real.exp (-(R * x))) : x = finalSizeRoot R :=
  eq_of_finalSizeGap_eq_zero (by linarith) hx (finalSizeRoot_pos hR)
    (by unfold finalSizeGap; linarith) (finalSizeRoot_spec hR).2.2

/-- **Approximate roots.** A point of `[0, 1]` that solves the final-size equation up to a small
enough error is close to `0` or to `τ`. -/
theorem exists_pos_forall_abs_finalSizeGap_le {R : ℝ} (hR : 1 < R) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ x ∈ Set.Icc (0 : ℝ) 1, |finalSizeGap R x| ≤ η →
      x < δ ∨ |x - finalSizeRoot R| < δ := by
  set K := Set.Icc δ 1 ∩ {x | δ ≤ |x - finalSizeRoot R|} with hK
  have hKc : IsCompact K :=
    isCompact_Icc.inter_right (isClosed_le continuous_const (by fun_prop))
  have key : ∀ x ∈ K, 0 < |finalSizeGap R x| := by
    intro x hx
    refine abs_pos.2 fun h0 => ?_
    have := eq_of_finalSizeGap_eq_zero (by linarith) (hδ.trans_le hx.1.1) (finalSizeRoot_pos hR)
      h0 (finalSizeRoot_spec hR).2.2
    have h2 := hx.2
    simp only [Set.mem_ofPred_eq, this, sub_self, abs_zero] at h2
    linarith
  by_cases hne : K.Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ := hKc.exists_isMinOn hne
      ((continuous_finalSizeGap R).abs.continuousOn)
    refine ⟨|finalSizeGap R x₀| / 2, half_pos (key x₀ hx₀), fun x hx hgx => ?_⟩
    by_contra hc
    push Not at hc
    have hxK : x ∈ K := ⟨⟨hc.1, hx.2⟩, hc.2⟩
    have := hmin hxK
    have := key x₀ hx₀
    simp only [Set.mem_ofPred_eq] at *
    linarith
  · refine ⟨1, one_pos, fun x hx _ => ?_⟩
    by_contra hc
    push Not at hc
    exact hne ⟨x, ⟨hc.1, hx.2⟩, hc.2⟩

end FinalSizeEquation

/-! ### Configurations, measurability and independence -/

section Configuration

/-- The epidemic up to generation `n` depends only on the offspring numbers of generations
`< n`. -/
theorem epi_congr {ξ ξ' : ℕ → ℕ → ℕ} {α : Type*} [DecidableEq α] (U : ℕ → α) (S₀ : Finset α)
    {n : ℕ} (h : ∀ m < n, ∀ i, ξ m i = ξ' m i) : epi ξ U S₀ n = epi ξ' U S₀ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ih' := ih fun m hm => h m (Nat.lt_succ_of_lt hm)
    have hs : ∑ i ∈ range (epi ξ' U S₀ n).1, ξ n i = ∑ i ∈ range (epi ξ' U S₀ n).1, ξ' n i :=
      sum_congr rfl fun i _ => h n n.lt_succ_self i
    simp only [epi, ih', hs]

variable {N : ℕ} (S₀ : Finset (Fin N))

/-- A configuration of the coupled model: offspring numbers indexed by
`(generation, individual)`, and contact targets. -/
abbrev Config (N : ℕ) := (ℕ × ℕ → ℕ) × (ℕ → Fin N)

/-- The epidemic state as a function of a configuration. -/
def epiOf (w : Config N) (n : ℕ) : ℕ × ℕ :=
  epi (fun m i => w.1 (m, i)) w.2 S₀ n

theorem measurableSet_epiHit (j : ℕ) : MeasurableSet {v : ℕ → Fin N | epiHit v S₀ j} := by
  have : {v : ℕ → Fin N | epiHit v S₀ j} = (fun v => v j) ⁻¹' (S₀ : Set (Fin N)) ∩
      ⋂ j' ∈ range j, (fun v : ℕ → Fin N => (v j', v j)) ⁻¹' {p | p.1 ≠ p.2} := by
    ext v; simp [epiHit]
  rw [this]
  exact ((measurable_pi_apply j) MeasurableSet.of_discrete).inter
    (MeasurableSet.biInter (Set.to_countable _) fun j' _ =>
      ((measurable_pi_apply j').prodMk (measurable_pi_apply j)) MeasurableSet.of_discrete)

theorem measurable_card_filter_epiHit (a b : ℕ) :
    Measurable fun v : ℕ → Fin N => ((Ico a b).filter (epiHit v S₀)).card := by
  simp_rw [card_filter]
  exact Finset.measurable_sum _ fun j _ =>
    Measurable.ite (measurableSet_epiHit S₀ j) measurable_const measurable_const

theorem measurable_epiOf (n : ℕ) : Measurable fun w : Config N => epiOf S₀ w n := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hsum (a : ℕ) : Measurable fun w : Config N => ∑ i ∈ range a, w.1 (n, i) :=
      Finset.measurable_sum _ fun i _ => (measurable_pi_apply (n, i)).comp measurable_fst
    have hstep (y : ℕ × ℕ) : Measurable fun w : Config N =>
        (((Ico y.2 (y.2 + ∑ i ∈ range y.1, w.1 (n, i))).filter (epiHit w.2 S₀)).card,
          y.2 + ∑ i ∈ range y.1, w.1 (n, i)) := by
      have hc : Measurable fun q : ℕ × (ℕ → Fin N) =>
          ((Ico y.2 (y.2 + q.1)).filter (epiHit q.2 S₀)).card :=
        measurable_from_prod_countable_right fun s => by
          dsimp only; exact measurable_card_filter_epiHit S₀ _ _
      exact (hc.comp ((hsum y.1).prodMk measurable_snd)).prodMk
        (measurable_const.add (hsum y.1))
    refine measurable_to_countable' fun x => ?_
    have : (fun w : Config N => epiOf S₀ w (n + 1)) ⁻¹' {x} = ⋃ y : ℕ × ℕ,
        ((fun w : Config N => epiOf S₀ w n) ⁻¹' {y} ∩ (fun w : Config N =>
          (((Ico y.2 (y.2 + ∑ i ∈ range y.1, w.1 (n, i))).filter (epiHit w.2 S₀)).card,
            y.2 + ∑ i ∈ range y.1, w.1 (n, i))) ⁻¹' {x}) := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hw; exact ⟨_, rfl, hw⟩
      · rintro ⟨y, rfl, hw⟩; exact hw
    rw [this]
    exact MeasurableSet.iUnion fun y => (ih (measurableSet_singleton y)).inter
      (hstep y (measurableSet_singleton x))

theorem measurable_finalSizeOf :
    Measurable fun w : Config N => finalSize (fun n i => w.1 (n, i)) w.2 S₀ := by
  have hc : Measurable fun q : ℕ × (ℕ → Fin N) => ((range q.1).filter (epiHit q.2 S₀)).card :=
    measurable_from_prod_countable_right fun s => by
      dsimp only; rw [range_eq_Ico]; exact measurable_card_filter_epiHit S₀ 0 s
  exact hc.comp ((measurable_snd.comp (measurable_epiOf S₀ (S₀.card + 1))).prodMk measurable_snd)

end Configuration

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν : Measure ℕ} {N : ℕ}
  {ξ : ℕ → ℕ → Ω → ℕ} {U : ℕ → Ω → Fin N}

/-- **The model of the final-size theorem.** The hypotheses `IsEarlyEpidemic` of the early
epidemic, together with measurable contact targets that are independent of the offspring
numbers. (`IsEarlyEpidemic` makes no assumption on the joint law of offspring numbers and
targets; without one the final size is not determined by `ν` and `N`.) -/
structure IsFinalSizeEpidemic (P : Measure Ω) (ν : Measure ℕ) (N : ℕ) (ξ : ℕ → ℕ → Ω → ℕ)
    (U : ℕ → Ω → Fin N) : Prop extends IsEarlyEpidemic P ν N ξ U where
  measurable_target : ∀ j, Measurable (U j)
  indepFun_offspring_target : IndepFun (fun ω (p : ℕ × ℕ) => ξ p.1 p.2 ω) (fun ω j => U j ω) P

/-- The configuration of the model at `ω`. -/
def config (ξ : ℕ → ℕ → Ω → ℕ) (U : ℕ → Ω → Fin N) (ω : Ω) : Config N :=
  (fun p => ξ p.1 p.2 ω, fun j => U j ω)

/-- The configuration at `ω` with the offspring number `p₀` replaced by `0`. -/
def configWithout (ξ : ℕ → ℕ → Ω → ℕ) (U : ℕ → Ω → Fin N) (p₀ : ℕ × ℕ) (ω : Ω) : Config N :=
  (Function.update (fun p => ξ p.1 p.2 ω) p₀ 0, fun j => U j ω)

/-- The σ-algebras of the targets (`none`) and of the single offspring numbers (`some p`). -/
@[instance_reducible]
private def sigmaFamily (ξ : ℕ → ℕ → Ω → ℕ) (U : ℕ → Ω → Fin N) :
    Option (ℕ × ℕ) → MeasurableSpace Ω
  | none => MeasurableSpace.comap (fun ω j => U j ω) inferInstance
  | some p => MeasurableSpace.comap (ξ p.1 p.2) inferInstance

namespace IsFinalSizeEpidemic

theorem measurable_config (h : IsFinalSizeEpidemic P ν N ξ U) : Measurable (config ξ U) :=
  (measurable_pi_iff.2 fun p : ℕ × ℕ => h.measurable p.1 p.2).prodMk
    (measurable_pi_iff.2 h.measurable_target)

theorem measurable_configWithout (h : IsFinalSizeEpidemic P ν N ξ U) (p₀ : ℕ × ℕ) :
    Measurable (configWithout ξ U p₀) := by
  refine Measurable.prodMk (measurable_pi_iff.2 fun p => ?_)
    (measurable_pi_iff.2 h.measurable_target)
  by_cases hp : p = p₀
  · subst hp; simp only [Function.update_self]; exact measurable_const
  · simp only [Function.update_of_ne hp]; exact h.measurable p.1 p.2

theorem measurable_finalSize (h : IsFinalSizeEpidemic P ν N ξ U) (S₀ : Finset (Fin N)) :
    Measurable fun ω => finalSize (ξ · · ω) (U · ω) S₀ := by
  have := (measurable_finalSizeOf S₀).comp h.measurable_config
  exact this

private lemma iIndep_sigmaFamily [IsProbabilityMeasure ν] (h : IsFinalSizeEpidemic P ν N ξ U) :
    iIndep (sigmaFamily ξ U) P := by
  have := h.isProbabilityMeasure
  have hind := (iIndep_iff _ P).1 ((iIndepFun_iff_iIndep _ _ P).1 h.indep)
  have hXV := (IndepFun_iff _ _ _).1 h.indepFun_offspring_target
  have key : ∀ (t : Finset (ℕ × ℕ)) (g : ℕ × ℕ → Set Ω) (B : Set Ω),
      MeasurableSet[MeasurableSpace.comap (fun ω j => U j ω) inferInstance] B →
      (∀ p ∈ t, MeasurableSet[MeasurableSpace.comap (ξ p.1 p.2) inferInstance] (g p)) →
      P ((⋂ p ∈ t, g p) ∩ B) = (∏ p ∈ t, P (g p)) * P B := by
    intro t g B hB hg
    have hA : MeasurableSet[MeasurableSpace.comap (fun ω (p : ℕ × ℕ) => ξ p.1 p.2 ω)
        inferInstance] (⋂ p ∈ t, g p) := by
      refine MeasurableSet.biInter (Set.to_countable _) fun p hp => ?_
      obtain ⟨s, hs, hgs⟩ := hg p hp
      exact ⟨(fun x => x p) ⁻¹' s, measurable_pi_apply p hs, hgs⟩
    rw [hXV _ _ hA hB, hind t hg]
  rw [iIndep_iff]
  intro s f hf
  by_cases hs : none ∈ s
  · have hI : (⋂ i ∈ s, f i) = (⋂ p ∈ s.eraseNone, f (some p)) ∩ f none := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_inter_iff, mem_eraseNone]
      constructor
      · intro H; exact ⟨fun p hp => H _ hp, H _ hs⟩
      · rintro ⟨H, H0⟩ i hi
        cases i with
        | none => exact H0
        | some p => exact H p hi
    have hP : ∏ i ∈ s, P (f i) = (∏ p ∈ s.eraseNone, P (f (some p))) * P (f none) := by
      conv_lhs => rw [← insert_eq_of_mem hs, ← insertNone_eraseNone]
      rw [prod_insertNone, mul_comm]
    rw [hI, hP]
    exact key _ _ _ (hf none hs) fun p hp => hf (some p) (mem_eraseNone.1 hp)
  · have hI : (⋂ i ∈ s, f i) = (⋂ p ∈ s.eraseNone, f (some p)) ∩ Set.univ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_inter_iff, mem_eraseNone, Set.mem_univ, and_true]
      constructor
      · intro H p hp; exact H _ hp
      · intro H i hi
        cases i with
        | none => exact absurd hi hs
        | some p => exact H p hi
    have hP : ∏ i ∈ s, P (f i) = (∏ p ∈ s.eraseNone, P (f (some p))) * P Set.univ := by
      rw [measure_univ, mul_one]
      conv_lhs => rw [← erase_eq_of_notMem hs, ← map_some_eraseNone]
      rw [prod_map]
      rfl
    rw [hI, hP]
    exact key _ _ _ MeasurableSet.univ fun p hp => hf (some p) (mem_eraseNone.1 hp)

/-- An offspring number is independent of all the other offspring numbers and the targets. -/
theorem indepFun_configWithout [IsProbabilityMeasure ν] (h : IsFinalSizeEpidemic P ν N ξ U)
    (p₀ : ℕ × ℕ) :
    IndepFun (configWithout ξ U p₀) (ξ p₀.1 p₀.2) P := by
  have hle : ∀ i, sigmaFamily ξ U i ≤ ‹MeasurableSpace Ω› := by
    rintro (_ | p)
    · exact (measurable_pi_iff.2 h.measurable_target).comap_le
    · exact (h.measurable p.1 p.2).comap_le
  have hI := indep_iSup_of_disjoint hle h.iIndep_sigmaFamily
    (S := ({some p₀}ᶜ : Set (Option (ℕ × ℕ)))) (T := {some p₀}) disjoint_compl_left
  rw [IndepFun_iff_Indep]
  set mR : MeasurableSpace Ω := ⨆ i ∈ ({some p₀}ᶜ : Set (Option (ℕ × ℕ))), sigmaFamily ξ U i
  have hmR : ∀ i ∈ ({some p₀}ᶜ : Set (Option (ℕ × ℕ))), sigmaFamily ξ U i ≤ mR := fun i hi =>
    le_iSup₂ (f := fun i (_ : i ∈ ({some p₀}ᶜ : Set (Option (ℕ × ℕ)))) => sigmaFamily ξ U i) i hi
  have hm : Measurable[mR] (configWithout ξ U p₀) := by
    refine Measurable.prodMk (m := mR) (measurable_pi_iff.2 fun p => ?_)
      (measurable_pi_iff.2 fun j => ?_)
    · by_cases hp : p = p₀
      · subst hp; simp only [Function.update_self]; exact measurable_const
      · simp only [Function.update_of_ne hp]
        exact Measurable.mono (comap_measurable (ξ p.1 p.2)) (hmR (some p) (by simpa using hp))
          le_rfl
    · have : Measurable[sigmaFamily ξ U none] fun ω => U j ω := fun s hs =>
        ⟨(fun v => v j) ⁻¹' s, measurable_pi_apply j hs, rfl⟩
      exact Measurable.mono this (hmR none (by simp)) le_rfl
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hI hm.comap_le) ?_
  exact le_iSup₂ (f := fun i (_ : i ∈ ({some p₀} : Set (Option (ℕ × ℕ)))) =>
    sigmaFamily ξ U i) (some p₀) rfl

/-- **Factorization.** For a function `φ` of the configuration without the offspring number
`p₀`, `E[φ · f(ξ p₀)] = E[φ] E[f(ξ p₀)]`. -/
theorem integral_mul_offspring [IsProbabilityMeasure ν] (h : IsFinalSizeEpidemic P ν N ξ U)
    (p₀ : ℕ × ℕ)
    {φ : Config N → ℝ} (hφ : Measurable φ) (f : ℕ → ℝ) :
    ∫ ω, φ (configWithout ξ U p₀ ω) * f (ξ p₀.1 p₀.2 ω) ∂P =
      (∫ ω, φ (configWithout ξ U p₀ ω) ∂P) * ∫ ω, f (ξ p₀.1 p₀.2 ω) ∂P :=
  ((h.indepFun_configWithout p₀).comp hφ (measurable_of_countable f)).integral_mul_eq_mul_integral
    (hφ.comp (h.measurable_configWithout p₀)).aestronglyMeasurable
    ((measurable_of_countable f).comp (h.measurable p₀.1 p₀.2)).aestronglyMeasurable

end IsFinalSizeEpidemic

end Probability

/-! ### The centered contact count -/

section Gate

variable {N : ℕ} (S₀ : Finset (Fin N))

theorem epiOf_congr {w w' : Config N} {n : ℕ} (h : ∀ m < n, ∀ i, w.1 (m, i) = w'.1 (m, i))
    (h2 : w.2 = w'.2) : epiOf S₀ w n = epiOf S₀ w' n := by
  unfold epiOf; rw [h2]; exact epi_congr _ _ h

/-- The number of infectives of generations `0, …, n`. -/
def cumOf (w : Config N) (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), (epiOf S₀ w k).1

/-- `1` if the `p.2`-th individual of generation `p.1` is an infective and the generations
`0, …, p.1` contain at most `L` infectives; `0` otherwise. It depends only on the offspring
numbers of the generations `< p.1`. -/
noncomputable def gate (L : ℕ) (w : Config N) (p : ℕ × ℕ) : ℝ :=
  if cumOf S₀ w p.1 ≤ L ∧ p.2 < (epiOf S₀ w p.1).1 then 1 else 0

/-- The contacts made by the infectives of the generations `0, …, n` with at most `L`
infectives in total, centered at `m` per infective. Once `finalSize + 1 ≤ L` this is
`totalContacts - m (finalSize + 1)` (`truncDev_eq`). -/
noncomputable def truncDev (m : ℝ) (L : ℕ) (w : Config N) : ℝ :=
  ∑ p ∈ range (S₀.card + 1) ×ˢ range L, gate S₀ L w p * ((w.1 p : ℝ) - m)

theorem measurable_cumOf (n : ℕ) : Measurable fun w : Config N => cumOf S₀ w n :=
  Finset.measurable_sum _ fun k _ => measurable_fst.comp (measurable_epiOf S₀ k)

theorem measurable_gate (L : ℕ) (p : ℕ × ℕ) : Measurable fun w : Config N => gate S₀ L w p :=
  (measurable_of_countable fun q : ℕ × ℕ => if q.1 ≤ L ∧ p.2 < q.2 then (1 : ℝ) else 0).comp
    ((measurable_cumOf S₀ p.1).prodMk (measurable_fst.comp (measurable_epiOf S₀ p.1)))

theorem gate_nonneg (L : ℕ) (w : Config N) (p : ℕ × ℕ) : 0 ≤ gate S₀ L w p := by
  unfold gate; split_ifs <;> norm_num

theorem gate_le_one (L : ℕ) (w : Config N) (p : ℕ × ℕ) : gate S₀ L w p ≤ 1 := by
  unfold gate; split_ifs <;> norm_num

theorem gate_mul_self (L : ℕ) (w : Config N) (p : ℕ × ℕ) :
    gate S₀ L w p * gate S₀ L w p = gate S₀ L w p := by
  unfold gate; split_ifs <;> norm_num

theorem gate_congr {L : ℕ} {w w' : Config N} {p : ℕ × ℕ}
    (h : ∀ m < p.1, ∀ i, w.1 (m, i) = w'.1 (m, i)) (h2 : w.2 = w'.2) :
    gate S₀ L w p = gate S₀ L w' p := by
  have hk : ∀ k ≤ p.1, epiOf S₀ w k = epiOf S₀ w' k := fun k hk =>
    epiOf_congr S₀ (fun m hm i => h m (lt_of_lt_of_le hm hk) i) h2
  have hc : cumOf S₀ w p.1 = cumOf S₀ w' p.1 :=
    sum_congr rfl fun k hk' => by rw [hk k (Nat.lt_succ_iff.1 (mem_range.1 hk'))]
  unfold gate; rw [hc, hk p.1 le_rfl]

private lemma sum_ite_cum_le (f : ℕ → ℕ) (L K : ℕ) :
    ∑ n ∈ range K, (if ∑ k ∈ range (n + 1), f k ≤ L then f n else 0) ≤ L := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ]
    split_ifs with hK
    · have hle : ∑ n ∈ range K, (if ∑ k ∈ range (n + 1), f k ≤ L then f n else 0) ≤
          ∑ n ∈ range K, f n := sum_le_sum fun n _ => by split_ifs <;> omega
      rw [sum_range_succ] at hK
      omega
    · simpa using ih

/-- The gates add up to at most `L`. -/
theorem sum_gate_le (L : ℕ) (w : Config N) :
    ∑ p ∈ range (S₀.card + 1) ×ˢ range L, gate S₀ L w p ≤ L := by
  rw [sum_product]
  have hinner : ∀ n, ∑ i ∈ range L, gate S₀ L w (n, i) ≤
      ((if cumOf S₀ w n ≤ L then (epiOf S₀ w n).1 else 0 : ℕ) : ℝ) := by
    intro n
    unfold gate
    dsimp only
    by_cases hc : cumOf S₀ w n ≤ L
    · simp only [hc, true_and, ite_true]
      rw [sum_boole]
      exact_mod_cast (card_le_card (s := (range L).filter (· < (epiOf S₀ w n).1))
        (t := range (epiOf S₀ w n).1) fun i hi => mem_range.2 (mem_filter.1 hi).2).trans
        (card_range _).le
    · simp [hc]
  calc _ ≤ ∑ n ∈ range (S₀.card + 1),
        ((if cumOf S₀ w n ≤ L then (epiOf S₀ w n).1 else 0 : ℕ) : ℝ) :=
          sum_le_sum fun n _ => hinner n
    _ ≤ L := by
      rw [← Nat.cast_sum]
      exact_mod_cast sum_ite_cum_le (fun k => (epiOf S₀ w k).1) L _

/-- Once all infectives are counted, the centered contact count is
`totalContacts - m (finalSize + 1)`. -/
theorem truncDev_eq (m : ℝ) {L : ℕ} (w : Config N)
    (hL : finalSize (fun n i => w.1 (n, i)) w.2 S₀ + 1 ≤ L) :
    truncDev S₀ m L w = (totalContacts (fun n i => w.1 (n, i)) w.2 S₀ : ℝ) -
      m * (finalSize (fun n i => w.1 (n, i)) w.2 S₀ + 1) := by
  set ξw : ℕ → ℕ → ℕ := fun n i => w.1 (n, i)
  have hsum := sum_epiSize_eq_finalSize_add_one ξw w.2 S₀
  have hcum : ∀ n ∈ range (S₀.card + 1), cumOf S₀ w n ≤ L := fun n hn =>
    le_trans (sum_le_sum_of_subset (range_subset_range.2 (mem_range.1 hn))) (hsum ▸ hL)
  have hI : ∀ n ∈ range (S₀.card + 1), (epiOf S₀ w n).1 ≤ L := fun n hn =>
    le_trans (single_le_sum (f := fun k => (epiOf S₀ w k).1) (fun _ _ => Nat.zero_le _)
      (self_mem_range_succ n)) (hcum n hn)
  unfold truncDev
  rw [sum_product]
  have hrow : ∀ n ∈ range (S₀.card + 1), ∑ i ∈ range L, gate S₀ L w (n, i) * ((w.1 (n, i) : ℝ) - m)
      = ∑ i ∈ range (epiSize ξw w.2 S₀ n), ((ξw n i : ℝ) - m) := by
    intro n hn
    unfold gate
    simp only [hcum n hn, true_and, ite_mul, one_mul, zero_mul]
    rw [← sum_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range]
    exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h (hI n hn), h⟩⟩
  rw [sum_congr rfl hrow, totalContacts_eq_sum]
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  rw [← sum_mul, mul_comm m]
  have hcast : (∑ i ∈ range (S₀.card + 1), (epiSize ξw w.2 S₀ i : ℝ)) =
      (finalSize ξw w.2 S₀ : ℝ) + 1 := by exact_mod_cast hsum
  push_cast
  rw [hcast]

end Gate

/-! ### Second-moment bound for the contact count -/

section Variance

/-- The mean `m = ∫ k dν` of the offspring law, as a real number. -/
noncomputable def offspringMean (ν : Measure ℕ) : ℝ :=
  ∫ k, (k : ℝ) ∂ν

/-- The variance `σ² = ∫ (k - m)² dν` of the offspring law. -/
noncomputable def offspringVar (ν : Measure ℕ) : ℝ :=
  ∫ k, ((k : ℝ) - offspringMean ν) ^ 2 ∂ν

theorem offspringVar_nonneg (ν : Measure ℕ) : 0 ≤ offspringVar ν :=
  integral_nonneg fun _ => sq_nonneg _

theorem integrable_natCast_of_sq {ν : Measure ℕ} (h2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) ν) :
    Integrable (fun k : ℕ => (k : ℝ)) ν :=
  h2.mono' (measurable_of_countable _).aestronglyMeasurable (Eventually.of_forall fun k => by
    rw [Real.norm_natCast]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith)

theorem integrable_sub_sq {ν : Measure ℕ} [IsFiniteMeasure ν]
    (h2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) ν) (m : ℝ) :
    Integrable (fun k : ℕ => ((k : ℝ) - m) ^ 2) ν := by
  have h1 := integrable_natCast_of_sq h2
  have : (fun k : ℕ => ((k : ℝ) - m) ^ 2) = fun k : ℕ => (k : ℝ) ^ 2 - 2 * m * k + m ^ 2 := by
    ext k; ring
  rw [this]
  exact (h2.sub (h1.const_mul (2 * m))).add (integrable_const _)

/-- With a finite second moment, the mean `R₀ = mean ν` of the early-epidemic file is the real
mean `offspringMean ν`. -/
theorem mean_eq_ofReal_offspringMean {ν : Measure ℕ}
    (h2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) ν) : mean ν = ENNReal.ofReal (offspringMean ν) := by
  rw [mean, offspringMean, ofReal_integral_eq_lintegral_ofReal (integrable_natCast_of_sq h2)
    (Eventually.of_forall fun k => Nat.cast_nonneg k)]
  simp_rw [ENNReal.ofReal_natCast]

theorem offspringMean_eq_toReal_mean {ν : Measure ℕ}
    (h2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) ν) : offspringMean ν = (mean ν).toReal := by
  rw [mean_eq_ofReal_offspringMean h2, ENNReal.toReal_ofReal
    (show 0 ≤ offspringMean ν from integral_nonneg fun k => Nat.cast_nonneg k)]

theorem one_lt_offspringMean {ν : Measure ℕ} (h2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) ν)
    (hm : 1 < mean ν) : 1 < offspringMean ν := by
  rw [mean_eq_ofReal_offspringMean h2] at hm
  exact ENNReal.one_lt_ofReal.1 hm

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν : Measure ℕ} {N : ℕ}
  {ξ : ℕ → ℕ → Ω → ℕ} {U : ℕ → Ω → Fin N}

omit [MeasurableSpace Ω] in
theorem configWithout_fst_of_ne (p₀ : ℕ × ℕ) (ω : Ω) {p : ℕ × ℕ} (hp : p ≠ p₀) :
    (configWithout ξ U p₀ ω).1 p = ξ p.1 p.2 ω := by
  simp [configWithout, Function.update_of_ne hp]

omit [MeasurableSpace Ω] in
theorem gate_configWithout (S₀ : Finset (Fin N)) (L : ℕ) (ω : Ω) {p p₀ : ℕ × ℕ}
    (hp : p.1 ≤ p₀.1) : gate S₀ L (configWithout ξ U p₀ ω) p = gate S₀ L (config ξ U ω) p :=
  gate_congr S₀ (fun m hm i => configWithout_fst_of_ne p₀ ω fun he => by
    rw [← he] at hp; exact absurd hm (not_lt.2 hp)) rfl

namespace IsFinalSizeEpidemic

theorem integral_offspring (h : IsFinalSizeEpidemic P ν N ξ U) (p : ℕ × ℕ) (f : ℕ → ℝ) :
    ∫ ω, f (ξ p.1 p.2 ω) ∂P = ∫ k, f k ∂ν := by
  rw [← h.map_eq p.1 p.2, integral_map (h.measurable _ _).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable]

theorem integrable_offspring (h : IsFinalSizeEpidemic P ν N ξ U) (p : ℕ × ℕ) {f : ℕ → ℝ}
    (hf : Integrable f ν) : Integrable (fun ω => f (ξ p.1 p.2 ω)) P := by
  rw [← h.map_eq p.1 p.2] at hf
  exact (integrable_map_measure (measurable_of_countable f).aestronglyMeasurable
    (h.measurable _ _).aemeasurable).1 hf

/-- **Second moment of the centered contact count.**
`E[(truncDev L)²] ≤ σ² L`: the increments are orthogonal, and the gates add up to at most `L`. -/
theorem integral_truncDev_sq_le [IsProbabilityMeasure ν] (h : IsFinalSizeEpidemic P ν N ξ U)
    (h2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) ν) (S₀ : Finset (Fin N)) (L : ℕ) :
    ∫ ω, truncDev S₀ (offspringMean ν) L (config ξ U ω) ^ 2 ∂P ≤ offspringVar ν * L := by
  have := h.isProbabilityMeasure
  set m := offspringMean ν
  set T := range (S₀.card + 1) ×ˢ range L
  set e : ℕ × ℕ → Ω → ℝ := fun p ω => (ξ p.1 p.2 ω : ℝ) - m with he_def
  set G : ℕ × ℕ → Ω → ℝ := fun p ω => gate S₀ L (config ξ U ω) p with hG_def
  have hD : ∀ ω, truncDev S₀ m L (config ξ U ω) ^ 2 =
      ∑ a ∈ T, ∑ b ∈ T, G a ω * e a ω * (G b ω * e b ω) := fun ω => by
    rw [sq]; exact sum_mul_sum _ _ _ _
  have hme : ∀ p, Measurable (e p) := fun p =>
    (measurable_of_countable fun k : ℕ => (k : ℝ) - m).comp (h.measurable p.1 p.2)
  have hmG : ∀ p, Measurable (G p) := fun p => (measurable_gate S₀ L p).comp h.measurable_config
  have he2 : ∀ p, Integrable (fun ω => e p ω ^ 2) P := fun p =>
    h.integrable_offspring p (f := fun k : ℕ => ((k : ℝ) - m) ^ 2) (integrable_sub_sq h2 m)
  have hint : ∀ a b, Integrable (fun ω => G a ω * e a ω * (G b ω * e b ω)) P := by
    intro a b
    refine ((he2 a).add (he2 b)).mono'
      (((hmG a).mul (hme a)).mul ((hmG b).mul (hme b))).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    have hGa := gate_nonneg S₀ L (config ξ U ω) a
    have hGa' := gate_le_one S₀ L (config ξ U ω) a
    have hGb := gate_nonneg S₀ L (config ξ U ω) b
    have hGb' := gate_le_one S₀ L (config ξ U ω) b
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hGa, abs_of_nonneg hGb]
    have h1 : G a ω * |e a ω| ≤ |e a ω| := mul_le_of_le_one_left (abs_nonneg _) hGa'
    have h2' : G b ω * |e b ω| ≤ |e b ω| := mul_le_of_le_one_left (abs_nonneg _) hGb'
    have h3 : |e a ω| * |e b ω| ≤ e a ω ^ 2 + e b ω ^ 2 := by
      nlinarith [sq_nonneg (|e a ω| - |e b ω|), sq_abs (e a ω), sq_abs (e b ω),
        abs_nonneg (e a ω), abs_nonneg (e b ω)]
    calc G a ω * |e a ω| * (G b ω * |e b ω|) ≤ |e a ω| * |e b ω| :=
          mul_le_mul h1 h2' (mul_nonneg hGb (abs_nonneg _)) (abs_nonneg _)
      _ ≤ _ := h3
  have hmean0 : ∀ p : ℕ × ℕ, ∫ ω, (fun k : ℕ => (k : ℝ) - m) (ξ p.1 p.2 ω) ∂P = 0 := by
    intro p
    refine (h.integral_offspring p (fun k : ℕ => (k : ℝ) - m)).trans ?_
    rw [integral_sub (integrable_natCast_of_sq h2) (integrable_const m)]
    simp [m, offspringMean]
  have hGint : ∀ p, Integrable (G p) P := fun p =>
    (integrable_const (1 : ℝ)).mono' (hmG p).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (gate_nonneg S₀ L _ p)]
        exact gate_le_one S₀ L _ p)
  have hmx : ∀ a : ℕ × ℕ, Measurable fun w : Config N => ((w.1 a : ℕ) : ℝ) - m := fun a =>
    (measurable_of_countable fun k : ℕ => (k : ℝ) - m).comp
      ((measurable_pi_apply a).comp measurable_fst)
  have hoff : ∀ a b, a ≠ b → a.1 ≤ b.1 →
      ∫ ω, G a ω * e a ω * (G b ω * e b ω) ∂P = 0 := by
    intro a b hab hle
    have hfun : (fun ω => G a ω * e a ω * (G b ω * e b ω)) = fun ω =>
        (fun w : Config N => gate S₀ L w a * ((w.1 a : ℝ) - m) * gate S₀ L w b)
          (configWithout ξ U b ω) * (fun k : ℕ => (k : ℝ) - m) (ξ b.1 b.2 ω) := by
      ext ω
      simp only [hG_def, he_def]
      rw [gate_configWithout S₀ L ω hle, gate_configWithout S₀ L ω le_rfl,
        configWithout_fst_of_ne b ω hab]
      ring
    rw [hfun]
    refine (h.integral_mul_offspring b
      (φ := fun w : Config N => gate S₀ L w a * ((w.1 a : ℝ) - m) * gate S₀ L w b)
      (((measurable_gate S₀ L a).mul (hmx a)).mul (measurable_gate S₀ L b))
      (fun k : ℕ => (k : ℝ) - m)).trans ?_
    rw [hmean0 b, mul_zero]
  have hdiag : ∀ a, ∫ ω, G a ω * e a ω * (G a ω * e a ω) ∂P =
      (∫ ω, G a ω ∂P) * offspringVar ν := by
    intro a
    have hfun : (fun ω => G a ω * e a ω * (G a ω * e a ω)) = fun ω =>
        (fun w : Config N => gate S₀ L w a) (configWithout ξ U a ω) *
          (fun k : ℕ => ((k : ℝ) - m) ^ 2) (ξ a.1 a.2 ω) := by
      ext ω
      simp only [hG_def, he_def]
      rw [gate_configWithout S₀ L ω le_rfl]
      have hgg := gate_mul_self S₀ L (config ξ U ω) a
      calc _ = (gate S₀ L (config ξ U ω) a * gate S₀ L (config ξ U ω) a) *
            ((ξ a.1 a.2 ω : ℝ) - m) ^ 2 := by ring
        _ = _ := by rw [hgg]
    rw [hfun]
    refine (h.integral_mul_offspring a (φ := fun w : Config N => gate S₀ L w a)
      (measurable_gate S₀ L a) (fun k : ℕ => ((k : ℝ) - m) ^ 2)).trans ?_
    rw [h.integral_offspring a (fun k : ℕ => ((k : ℝ) - m) ^ 2)]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun ω => gate_configWithout S₀ L ω le_rfl)
  calc ∫ ω, truncDev S₀ m L (config ξ U ω) ^ 2 ∂P
      = ∑ a ∈ T, ∑ b ∈ T, ∫ ω, G a ω * e a ω * (G b ω * e b ω) ∂P := by
        simp_rw [hD]
        rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b]
        exact sum_congr rfl fun a _ => integral_finsetSum _ fun b _ => hint a b
    _ = ∑ a ∈ T, (∫ ω, G a ω ∂P) * offspringVar ν := by
        refine sum_congr rfl fun a ha => ?_
        rw [sum_eq_single_of_mem a ha fun b _ hba => ?_, hdiag a]
        rcases le_total a.1 b.1 with hle | hle
        · exact hoff a b (Ne.symm hba) hle
        · rw [show (fun ω => G a ω * e a ω * (G b ω * e b ω)) =
              fun ω => G b ω * e b ω * (G a ω * e a ω) from funext fun ω => mul_comm _ _]
          exact hoff b a hba hle
    _ = offspringVar ν * ∫ ω, ∑ a ∈ T, G a ω ∂P := by
        rw [integral_finsetSum _ fun a _ => hGint a, mul_sum]
        exact sum_congr rfl fun a _ => mul_comm _ _
    _ ≤ offspringVar ν * L := by
        refine mul_le_mul_of_nonneg_left ?_ (offspringVar_nonneg ν)
        calc ∫ ω, ∑ a ∈ T, G a ω ∂P ≤ ∫ _, (L : ℝ) ∂P :=
              integral_mono (integrable_finsetSum _ fun a _ => hGint a) (integrable_const _)
                fun ω => sum_gate_le S₀ L (config ξ U ω)
          _ = L := by simp

end IsFinalSizeEpidemic

end Variance

/-! ### Occupancy bounds for the contact targets -/

section Chebyshev

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Markov's inequality for the square: `P(t ≤ |X|) ≤ E[X²] / t²`. -/
theorem measureReal_le_abs_le {X : Ω → ℝ} (hX : Integrable (fun ω => X ω ^ 2) P) {t : ℝ}
    (ht : 0 < t) : P.real {ω | t ≤ |X ω|} ≤ (∫ ω, X ω ^ 2 ∂P) / t ^ 2 := by
  rw [le_div_iff₀ (by positivity), mul_comm]
  refine le_trans (mul_le_mul_of_nonneg_left (measureReal_mono fun ω (hω : t ≤ |X ω|) => ?_)
    (by positivity)) (mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall fun ω => sq_nonneg (X ω)) hX (t ^ 2))
  change t ^ 2 ≤ X ω ^ 2
  nlinarith [abs_nonneg (X ω), sq_abs (X ω)]

/-- **Second-moment bound for a count of events.** If the events `E i`, `i ∈ s`, have
probability `p` and are pairwise at most as likely as independent events, the number of them
that occur is within `t` of `#s p` except with probability `≤ #s p / t²`. -/
theorem measureReal_le_abs_sum_indicator_sub {ι : Type*} (s : Finset ι) {E : ι → Set Ω}
    (hE : ∀ i, MeasurableSet (E i)) {p : ℝ} (hp : ∀ i ∈ s, P.real (E i) = p)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P.real (E i ∩ E j) ≤ p ^ 2) {t : ℝ} (ht : 0 < t) :
    P.real {ω | t ≤ |∑ i ∈ s, (E i).indicator (1 : Ω → ℝ) ω - s.card * p|} ≤
      s.card * p / t ^ 2 := by
  classical
  set Z : Ω → ℝ := fun ω => ∑ i ∈ s, (E i).indicator (1 : Ω → ℝ) ω
  set a : ℝ := s.card * p
  have hind : ∀ i, Integrable ((E i).indicator (1 : Ω → ℝ)) P := fun i =>
    (integrable_const (1 : ℝ)).indicator (hE i)
  have hindij : ∀ i j, Integrable ((E i ∩ E j).indicator (1 : Ω → ℝ)) P := fun i j =>
    (integrable_const (1 : ℝ)).indicator ((hE i).inter (hE j))
  have hZi : Integrable Z P := integrable_finsetSum _ fun i _ => hind i
  have hZ2eq : ∀ ω, Z ω ^ 2 = ∑ i ∈ s, ∑ j ∈ s, (E i ∩ E j).indicator (1 : Ω → ℝ) ω := by
    intro ω
    rw [sq, sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [Set.inter_indicator_one]; rfl
  have hZ2i : Integrable (fun ω => Z ω ^ 2) P := by
    simp_rw [hZ2eq]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hindij i j
  have hZ : ∫ ω, Z ω ∂P = a := by
    simp only [Z]
    rw [integral_finsetSum _ fun i _ => hind i]
    rw [sum_congr rfl fun i hi => (integral_indicator_one (hE i)).trans (hp i hi)]
    simp [a]
  have hZ2 : ∫ ω, Z ω ^ 2 ∂P ≤ a + a ^ 2 := by
    simp_rw [hZ2eq]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hindij i j]
    have hrow : ∀ i ∈ s, ∫ ω, ∑ j ∈ s, (E i ∩ E j).indicator (1 : Ω → ℝ) ω ∂P ≤
        p + s.card * p ^ 2 := by
      intro i hi
      rw [integral_finsetSum _ fun j _ => hindij i j,
        sum_congr rfl fun j _ => integral_indicator_one ((hE i).inter (hE j)),
        ← add_sum_erase _ _ hi, Set.inter_self, hp i hi]
      gcongr
      calc ∑ j ∈ s.erase i, P.real (E i ∩ E j) ≤ ∑ j ∈ s.erase i, p ^ 2 :=
            sum_le_sum fun j hj => hpair i hi j (mem_of_mem_erase hj) (ne_of_mem_erase hj).symm
        _ ≤ s.card * p ^ 2 := by
            rw [sum_const, nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_erase_le) (sq_nonneg p)
    calc _ ≤ ∑ i ∈ s, (p + s.card * p ^ 2) := sum_le_sum hrow
      _ = a + a ^ 2 := by rw [sum_const, nsmul_eq_mul]; ring
  have hint2 : Integrable (fun ω => (Z ω - a) ^ 2) P := by
    have : (fun ω => (Z ω - a) ^ 2) = fun ω => Z ω ^ 2 - 2 * a * Z ω + a ^ 2 := by
      ext ω; ring
    rw [this]
    exact (hZ2i.sub (hZi.const_mul (2 * a))).add (integrable_const _)
  have h2 : ∫ ω, (Z ω - a) ^ 2 ∂P ≤ a := by
    have : (fun ω => (Z ω - a) ^ 2) = fun ω => Z ω ^ 2 - 2 * a * Z ω + a ^ 2 := by
      ext ω; ring
    have hZa : Integrable (fun ω => 2 * a * Z ω) P := hZi.const_mul (2 * a)
    have h1 : Integrable (fun ω => Z ω ^ 2 - 2 * a * Z ω) P := hZ2i.sub hZa
    rw [this, integral_add h1 (integrable_const _), integral_sub hZ2i hZa, integral_const_mul, hZ]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    nlinarith
  exact (measureReal_le_abs_le hint2 ht).trans (div_le_div_of_nonneg_right h2 (by positivity))

end Chebyshev

section Targets

variable {N : ℕ} (S₀ : Finset (Fin N))

/-- The number of hits among the first `c` contacts. -/
def hits (v : ℕ → Fin N) (c : ℕ) : ℕ :=
  ((range c).filter (epiHit v S₀)).card

/-- The number of the first `m` contacts that go outside `S₀`. -/
def outsideContacts (v : ℕ → Fin N) (m : ℕ) : ℕ :=
  ((range m).filter fun j => v j ∉ S₀).card

/-- The number of the first `m` contacts that go to an individual contacted before. -/
def repeatContacts (v : ℕ → Fin N) (m : ℕ) : ℕ :=
  ((range m).filter fun j => ∃ j' < j, v j' = v j).card

theorem finalSize_eq_hits (ξ : ℕ → ℕ → ℕ) (v : ℕ → Fin N) :
    finalSize ξ v S₀ = hits S₀ v (totalContacts ξ v S₀) :=
  rfl

theorem hits_mono (v : ℕ → Fin N) : Monotone (hits S₀ v) := fun _ _ hcc' =>
  card_le_card (filter_subset_filter _ (range_subset_range.2 hcc'))

theorem hits_le (v : ℕ → Fin N) (c : ℕ) : hits S₀ v c ≤ c :=
  (card_filter_le _ _).trans (card_range c).le

/-- Every hit goes to a distinct individual of `S₀`, and every individual of `S₀` contacted
among the first `c` contacts is hit exactly once: the hits and the individuals of `S₀` never
contacted add up to `#S₀`. -/
theorem hits_add_card_filter (v : ℕ → Fin N) (c : ℕ) :
    hits S₀ v c + (S₀.filter fun a => ∀ j < c, v j ≠ a).card = S₀.card := by
  have hbij : hits S₀ v c = (S₀.filter fun a => ¬ ∀ j < c, v j ≠ a).card := by
    refine card_bij (fun j _ => v j) (fun j hj => ?_) (fun j hj j' hj' hjj' => ?_) (fun a ha => ?_)
    · obtain ⟨hjc, hS, -⟩ := mem_filter.1 hj
      exact mem_filter.2 ⟨hS, fun H => H j (mem_range.1 hjc) rfl⟩
    · have h1 := (mem_filter.1 hj).2.2
      have h2 := (mem_filter.1 hj').2.2
      rcases lt_trichotomy j j' with hlt | heq | hgt
      · exact absurd hjj' (h2 j hlt)
      · exact heq
      · exact absurd hjj'.symm (h1 j' hgt)
    · obtain ⟨haS, ha'⟩ := mem_filter.1 ha
      push Not at ha'
      have hex : ∃ j, j < c ∧ v j = a := ha'
      refine ⟨Nat.find hex, mem_filter.2 ⟨mem_range.2 (Nat.find_spec hex).1, ?_, ?_⟩,
        (Nat.find_spec hex).2⟩
      · rw [(Nat.find_spec hex).2]; exact haS
      · intro j' hj' heq
        rw [(Nat.find_spec hex).2] at heq
        exact Nat.find_min hex hj' ⟨hj'.trans (Nat.find_spec hex).1, heq⟩
  rw [hbij, add_comm, card_filter_add_card_filter_not]

/-- A contact that does not hit goes outside `S₀` or to an individual contacted before. -/
theorem sub_hits_le (v : ℕ → Fin N) (c : ℕ) :
    c - hits S₀ v c ≤ outsideContacts S₀ v c + repeatContacts v c := by
  have hc : c - hits S₀ v c = ((range c).filter fun j => ¬ epiHit v S₀ j).card := by
    have := card_filter_add_card_filter_not (s := range c) (epiHit v S₀)
    rw [card_range] at this
    unfold hits; omega
  rw [hc]
  refine (card_le_card fun j hj => ?_).trans (card_union_le _ _)
  obtain ⟨hjc, hj⟩ := mem_filter.1 hj
  simp only [epiHit, not_and_or, not_forall, not_not] at hj
  rw [mem_union, mem_filter, mem_filter]
  rcases hj with h1 | ⟨j', hj', h2⟩
  · exact Or.inl ⟨hjc, h1⟩
  · exact Or.inr ⟨hjc, j', hj', h2⟩

theorem outsideContacts_mono (v : ℕ → Fin N) : Monotone (outsideContacts S₀ v) := fun _ _ h =>
  card_le_card (filter_subset_filter _ (range_subset_range.2 h))

theorem repeatContacts_mono (v : ℕ → Fin N) : Monotone (repeatContacts v) := fun _ _ h =>
  card_le_card (filter_subset_filter _ (range_subset_range.2 h))

end Targets

section TargetProbability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν : Measure ℕ} {N : ℕ}
  {ξ : ℕ → ℕ → Ω → ℕ} {U : ℕ → Ω → Fin N}

namespace IsFinalSizeEpidemic

theorem measure_target_mem (h : IsFinalSizeEpidemic P ν N ξ U) (j : ℕ) (A : Finset (Fin N)) :
    P (U j ⁻¹' (A : Set (Fin N))) = A.card * (N : ℝ≥0∞)⁻¹ := by
  have hA : U j ⁻¹' (A : Set (Fin N)) = ⋃ a ∈ A, U j ⁻¹' {a} := by ext; simp
  rw [hA, measure_biUnion_finset
    (fun a _ b _ hab => Disjoint.preimage _ (Set.disjoint_singleton.2 hab))
    (fun a _ => h.measurable_target j (measurableSet_singleton a))]
  simp [h.measure_target]

/-- `P(U j ∈ A for all j ∈ J) = (#A / N)^{#J}`. -/
theorem measureReal_forall_mem (h : IsFinalSizeEpidemic P ν N ξ U) (J : Finset ℕ)
    (A : Finset (Fin N)) :
    P.real {ω | ∀ j ∈ J, U j ω ∈ A} = ((A.card : ℝ) / N) ^ J.card := by
  have hset : {ω | ∀ j ∈ J, U j ω ∈ A} = ⋂ j ∈ J, U j ⁻¹' (A : Set (Fin N)) := by ext; simp
  rw [measureReal_def, hset, h.indep_target.measure_inter_preimage_eq_mul J
    (sets := fun _ => (A : Set (Fin N))) (fun _ _ => MeasurableSet.of_discrete)]
  simp only [h.measure_target_mem, prod_const, ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_inv, div_eq_mul_inv]

theorem measurableSet_forall_mem (h : IsFinalSizeEpidemic P ν N ξ U) (J : Finset ℕ)
    (A : Finset (Fin N)) : MeasurableSet {ω | ∀ j ∈ J, U j ω ∈ A} := by
  have hset : {ω | ∀ j ∈ J, U j ω ∈ A} = ⋂ j ∈ J, U j ⁻¹' (A : Set (Fin N)) := by ext; simp
  rw [hset]
  exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
    h.measurable_target j MeasurableSet.of_discrete

variable [IsProbabilityMeasure ν]

/-- **Concentration of the number of hits.** Among the first `c` contacts the number of hits is
within `t` of its mean `#S₀ (1 - (1 - 1/N)^c)` except with probability `≤ #S₀ / t²`. -/
theorem measureReal_le_abs_hits_sub (h : IsFinalSizeEpidemic P ν N ξ U) (S₀ : Finset (Fin N))
    (c : ℕ) {t : ℝ} (ht : 0 < t) :
    P.real {ω | t ≤ |(hits S₀ (U · ω) c : ℝ) - S₀.card * (1 - ((N - 1 : ℝ) / N) ^ c)|} ≤
      S₀.card / t ^ 2 := by
  have := h.isProbabilityMeasure
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h.ne_zero
  set E : Fin N → Set Ω := fun a => {ω | ∀ j ∈ range c, U j ω ∈ univ.erase a}
  set p : ℝ := ((N - 1 : ℝ) / N) ^ c
  have hp : ∀ a ∈ S₀, P.real (E a) = p := fun a _ => by
    rw [h.measureReal_forall_mem, card_erase_of_mem (mem_univ a), card_univ, Fintype.card_fin,
      card_range, Nat.cast_sub (by exact_mod_cast hN), Nat.cast_one]
  have hpair : ∀ a ∈ S₀, ∀ b ∈ S₀, a ≠ b → P.real (E a ∩ E b) ≤ p ^ 2 := by
    intro a _ b _ hab
    have hEE : E a ∩ E b = {ω | ∀ j ∈ range c, U j ω ∈ (univ.erase a).erase b} := by
      ext ω
      simp only [E, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_erase, mem_univ, and_true]
      exact ⟨fun H j hj => ⟨fun he => H.2 j hj he, H.1 j hj⟩,
        fun H => ⟨fun j hj => (H j hj).2, fun j hj => (H j hj).1⟩⟩
    have h2 : 2 ≤ N := by
      have := card_le_univ ({a, b} : Finset (Fin N))
      rw [card_pair hab, Fintype.card_fin] at this; exact this
    have h2' : (2 : ℝ) ≤ N := by exact_mod_cast h2
    have hcard : (((univ.erase a).erase b).card : ℝ) = N - 2 := by
      rw [card_erase_of_mem (mem_erase.2 ⟨hab.symm, mem_univ b⟩),
        card_erase_of_mem (mem_univ a), card_univ, Fintype.card_fin]
      push_cast [Nat.sub_sub, Nat.cast_sub h2]
      ring
    rw [hEE, h.measureReal_forall_mem, hcard, card_range, ← pow_mul, mul_comm, pow_mul]
    refine pow_le_pow_left₀ ?_ ?_ c
    · exact div_nonneg (by linarith) (by linarith)
    · rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  have hE : ∀ a, MeasurableSet (E a) := fun a => h.measurableSet_forall_mem _ _
  have hcount : ∀ ω, (hits S₀ (U · ω) c : ℝ) - S₀.card * (1 - p) =
      -(∑ a ∈ S₀, (E a).indicator (1 : Ω → ℝ) ω - S₀.card * p) := by
    intro ω
    have h1 := hits_add_card_filter S₀ (U · ω) c
    have h2 : ((S₀.filter fun a => ∀ j < c, U j ω ≠ a).card : ℝ) =
        ∑ a ∈ S₀, (E a).indicator (1 : Ω → ℝ) ω := by
      rw [card_filter]
      push_cast
      refine sum_congr rfl fun a _ => ?_
      simp only [Set.indicator, E, Set.mem_ofPred_eq, mem_range, mem_erase, mem_univ, and_true,
        Pi.one_apply]
    have h3 : (hits S₀ (U · ω) c : ℝ) + ((S₀.filter fun a => ∀ j < c, U j ω ≠ a).card : ℝ) =
        S₀.card := by exact_mod_cast h1
    rw [← h2]
    linarith
  simp_rw [hcount, abs_neg]
  refine (measureReal_le_abs_sum_indicator_sub S₀ hE hp hpair ht).trans ?_
  have hp1 : p ≤ 1 := pow_le_one₀ (div_nonneg (by linarith) (by linarith))
    ((div_le_one (by linarith)).2 (by linarith))
  exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (Nat.cast_nonneg _) hp1)
    (by positivity)

/-- **Concentration of the contacts outside `S₀`.** Among the first `m` contacts, the number
going outside `S₀` is within `t` of `m (N - #S₀) / N` except with probability
`≤ m (N - #S₀) / (N t²)`. -/
theorem measureReal_le_abs_outsideContacts_sub (h : IsFinalSizeEpidemic P ν N ξ U)
    (S₀ : Finset (Fin N)) (m : ℕ) {t : ℝ} (ht : 0 < t) :
    P.real {ω | t ≤ |(outsideContacts S₀ (U · ω) m : ℝ) -
      m * (((N - S₀.card : ℕ) : ℝ) / N)|} ≤ m * (((N - S₀.card : ℕ) : ℝ) / N) / t ^ 2 := by
  have := h.isProbabilityMeasure
  set E : ℕ → Set Ω := fun j => {ω | ∀ j' ∈ ({j} : Finset ℕ), U j' ω ∈ univ \ S₀}
  have hcardc : ((univ \ S₀).card : ℝ) = ((N - S₀.card : ℕ) : ℝ) := by
    rw [card_univ_sdiff, Fintype.card_fin]
  have hp : ∀ j ∈ range m, P.real (E j) = ((N - S₀.card : ℕ) : ℝ) / N := fun j _ => by
    rw [h.measureReal_forall_mem, hcardc, card_singleton, pow_one]
  have hpair : ∀ i ∈ range m, ∀ j ∈ range m, i ≠ j →
      P.real (E i ∩ E j) ≤ (((N - S₀.card : ℕ) : ℝ) / N) ^ 2 := by
    intro i _ j _ hij
    have hEE : E i ∩ E j = {ω | ∀ j' ∈ ({i, j} : Finset ℕ), U j' ω ∈ univ \ S₀} := by
      ext ω; simp [E]
    rw [hEE, h.measureReal_forall_mem, hcardc, card_pair hij]
  have hE : ∀ j, MeasurableSet (E j) := fun j => h.measurableSet_forall_mem _ _
  have hcount : ∀ ω, (outsideContacts S₀ (U · ω) m : ℝ) =
      ∑ j ∈ range m, (E j).indicator (1 : Ω → ℝ) ω := by
    intro ω
    rw [outsideContacts, card_filter]
    push_cast
    refine sum_congr rfl fun j _ => ?_
    simp [Set.indicator, E]
  simp_rw [hcount]
  have := measureReal_le_abs_sum_indicator_sub (range m) hE hp hpair ht
  rwa [card_range] at this

/-- **Markov bound for repeated contacts.** `P(t ≤ #repeated contacts among the first m) ≤
m² / (N t)`. -/
theorem measureReal_le_repeatContacts (h : IsFinalSizeEpidemic P ν N ξ U) (m : ℕ) {t : ℝ}
    (ht : 0 < t) : P.real {ω | t ≤ (repeatContacts (U · ω) m : ℝ)} ≤ m ^ 2 / (N * t) := by
  have := h.isProbabilityMeasure
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero h.ne_zero
  set E : ℕ → ℕ → Set Ω := fun j j' => {ω | U j' ω = U j ω}
  have hE : ∀ j j', MeasurableSet (E j j') := fun j j' =>
    measurableSet_eq_fun (h.measurable_target j') (h.measurable_target j)
  have hEi : ∀ j j', Integrable ((E j j').indicator (1 : Ω → ℝ)) P := fun j j' =>
    (integrable_const (1 : ℝ)).indicator (hE j j')
  set V : Ω → ℝ := fun ω => ∑ j ∈ range m, ∑ j' ∈ range j, (E j j').indicator (1 : Ω → ℝ) ω
  have hVi : Integrable V P := integrable_finsetSum _ fun j _ => integrable_finsetSum _
    fun j' _ => hEi j j'
  have hle : ∀ ω, (repeatContacts (U · ω) m : ℝ) ≤ V ω := by
    intro ω
    rw [repeatContacts, card_filter]
    push_cast
    refine sum_le_sum fun j _ => ?_
    split_ifs with hj
    · obtain ⟨j', hj', he⟩ := hj
      refine le_trans ?_ (single_le_sum (f := fun j' => (E j j').indicator (1 : Ω → ℝ) ω)
        (fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) (mem_range.2 hj'))
      simp [Set.indicator, E, he]
    · exact sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hint : ∫ ω, V ω ∂P ≤ m ^ 2 / N := by
    simp only [V]
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun j' _ => hEi j j']
    calc ∑ j ∈ range m, ∫ ω, ∑ j' ∈ range j, (E j j').indicator (1 : Ω → ℝ) ω ∂P
        ≤ ∑ j ∈ range m, ∑ j' ∈ range m, (1 / N : ℝ) := by
          refine sum_le_sum fun j hj => ?_
          rw [integral_finsetSum _ fun j' _ => hEi j j']
          refine le_trans (sum_le_sum fun j' hj' => ?_)
            (sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (mem_range.1 hj).le)
              fun _ _ _ => by positivity)
          rw [integral_indicator_one (hE j j'), measureReal_def, one_div,
            ← ENNReal.toReal_natCast N, ← ENNReal.toReal_inv]
          exact ENNReal.toReal_mono (by simp [h.ne_zero])
            (h.measure_target_eq_le (mem_range.1 hj').ne)
      _ = m ^ 2 / N := by simp [sum_const, card_range]; ring
  rw [le_div_iff₀ (by positivity)]
  have hm := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω =>
    (Nat.cast_nonneg _).trans (hle ω)) hVi t
  have hsub : P.real {ω | t ≤ (repeatContacts (U · ω) m : ℝ)} ≤ P.real {ω | t ≤ V ω} :=
    measureReal_mono fun ω (hω : t ≤ _) => hω.trans (hle ω)
  calc P.real {ω | t ≤ (repeatContacts (U · ω) m : ℝ)} * (N * t)
      ≤ P.real {ω | t ≤ V ω} * (N * t) := by gcongr
    _ = N * (t * P.real {ω | t ≤ V ω}) := by ring
    _ ≤ N * (m ^ 2 / N) := by gcongr; exact hm.trans hint
    _ = m ^ 2 := by field_simp

end IsFinalSizeEpidemic

end TargetProbability

section TruncDevBound

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν : Measure ℕ} {N : ℕ}
  {ξ : ℕ → ℕ → Ω → ℕ} {U : ℕ → Ω → Fin N}

namespace IsFinalSizeEpidemic

variable [IsProbabilityMeasure ν]

theorem integrable_truncDev_sq (h : IsFinalSizeEpidemic P ν N ξ U)
    (h2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) ν) (S₀ : Finset (Fin N)) (m : ℝ) (L : ℕ) :
    Integrable (fun ω => truncDev S₀ m L (config ξ U ω) ^ 2) P := by
  have := h.isProbabilityMeasure
  have hme : ∀ p : ℕ × ℕ, Measurable fun ω => (ξ p.1 p.2 ω : ℝ) - m := fun p =>
    (measurable_of_countable fun k : ℕ => (k : ℝ) - m).comp (h.measurable p.1 p.2)
  have he : ∀ p : ℕ × ℕ, MemLp (fun ω => (ξ p.1 p.2 ω : ℝ) - m) 2 P := fun p =>
    (memLp_two_iff_integrable_sq (hme p).aestronglyMeasurable).2
      (h.integrable_offspring p (f := fun k : ℕ => ((k : ℝ) - m) ^ 2) (integrable_sub_sq h2 m))
  have hG : ∀ p : ℕ × ℕ, MemLp (fun ω => gate S₀ L (config ξ U ω) p *
      ((ξ p.1 p.2 ω : ℝ) - m)) 2 P := fun p =>
    (he p).mono (((measurable_gate S₀ L p).comp h.measurable_config).mul
      (hme p)).aestronglyMeasurable (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (gate_nonneg S₀ L _ p)]
        exact mul_le_of_le_one_left (abs_nonneg _) (gate_le_one S₀ L _ p))
  exact (memLp_finsetSum (range (S₀.card + 1) ×ˢ range L) fun p _ => hG p).integrable_sq

/-- **Chebyshev bound for the centered contact count.** -/
theorem measureReal_le_abs_truncDev (h : IsFinalSizeEpidemic P ν N ξ U)
    (h2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) ν) (S₀ : Finset (Fin N)) (L : ℕ) {t : ℝ}
    (ht : 0 < t) :
    P.real {ω | t ≤ |truncDev S₀ (offspringMean ν) L (config ξ U ω)|} ≤
      offspringVar ν * L / t ^ 2 := by
  have := h.isProbabilityMeasure
  exact (measureReal_le_abs_le (h.integrable_truncDev_sq h2 S₀ _ L) ht).trans
    (div_le_div_of_nonneg_right (h.integral_truncDev_sq_le h2 S₀ L) (by positivity))

end IsFinalSizeEpidemic

end TruncDevBound

/-! ### Real-analysis helpers -/

section Analysis

theorem abs_exp_sub_exp_le_of_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a]; exact this hb ha (le_of_not_ge hab)
  have hea : Real.exp a ≤ Real.exp b := Real.exp_le_exp.2 hab
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  have h1 : Real.exp b - Real.exp a = Real.exp b * (1 - Real.exp (a - b)) := by
    rw [mul_sub, ← Real.exp_add]; ring_nf
  have h2 : 1 - Real.exp (a - b) ≤ b - a := by linarith [Real.add_one_le_exp (a - b)]
  have h3 : 0 ≤ 1 - Real.exp (a - b) := by
    have := Real.exp_le_one_iff.2 (by linarith : a - b ≤ 0); linarith
  have h4 : Real.exp b ≤ 1 := Real.exp_le_one_iff.2 hb
  nlinarith [Real.exp_pos b]

/-- `|(1 - 1/n)^c - e^{-c/n}| ≤ c / n²`. -/
theorem abs_one_sub_inv_pow_sub_exp_le {n : ℝ} (hn : 1 ≤ n) (c : ℕ) :
    |((n - 1) / n) ^ c - Real.exp (-(c / n))| ≤ c / n ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hb : Real.exp (-(c / n)) = Real.exp (-(1 / n)) ^ c := by
    rw [← Real.exp_nat_mul]; ring_nf
  have ha0 : 0 ≤ (n - 1) / n := div_nonneg (by linarith) hn0.le
  have ha1 : (n - 1) / n ≤ 1 := (div_le_one hn0).2 (by linarith)
  have hab : |(n - 1) / n - Real.exp (-(1 / n))| ≤ 1 / n ^ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := -(1 / n))
      (by rw [abs_neg, abs_of_pos (by positivity)]; exact (div_le_one hn0).2 hn)
    have e1 : (n - 1) / n - Real.exp (-(1 / n)) = -(Real.exp (-(1 / n)) - 1 - -(1 / n)) := by
      field_simp; ring
    have e2 : (-(1 / n)) ^ 2 = 1 / n ^ 2 := by ring
    rw [e1, abs_neg, ← e2]; exact h
  rw [hb]
  refine (abs_pow_sub_pow_le _ _ c).trans ?_
  have hmax : max |(n - 1) / n| |Real.exp (-(1 / n))| ≤ 1 :=
    max_le (by rwa [abs_of_nonneg ha0]) (by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (by have : 0 < 1 / n := by positivity
                                      linarith))
  calc |(n - 1) / n - Real.exp (-(1 / n))| * c * max |(n - 1) / n| |Real.exp (-(1 / n))| ^ (c - 1)
      ≤ 1 / n ^ 2 * c * 1 := by
        gcongr
        exact pow_le_one₀ (le_max_of_le_left (abs_nonneg _)) hmax
    _ = c / n ^ 2 := by ring

/-- The mean number of hits `s (1 - (1 - 1/n)^c)` is within `(n - s) + c / n` of
`n (1 - e^{-c/n})`. -/
theorem abs_mean_hits_sub_le {n s : ℝ} (hn : 1 ≤ n) (hsn : s ≤ n) (c : ℕ) :
    |s * (1 - ((n - 1) / n) ^ c) - n * (1 - Real.exp (-(c / n)))| ≤ (n - s) + c / n := by
  have hn0 : 0 < n := by linarith
  set A := ((n - 1) / n) ^ c
  have hA0 : 0 ≤ A := pow_nonneg (div_nonneg (by linarith) hn0.le) c
  have hA1 : A ≤ 1 := pow_le_one₀ (div_nonneg (by linarith) hn0.le)
    ((div_le_one hn0).2 (by linarith))
  have hAB := abs_one_sub_inv_pow_sub_exp_le hn c
  have e : s * (1 - A) - n * (1 - Real.exp (-(c / n))) =
      (s - n) * (1 - A) + n * (Real.exp (-(c / n)) - A) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonpos (by linarith : s - n ≤ 0), abs_of_nonneg (by linarith :
    0 ≤ 1 - A), abs_of_pos hn0, abs_sub_comm]
  have : n * |A - Real.exp (-(c / n))| ≤ n * (c / n ^ 2) := mul_le_mul_of_nonneg_left hAB hn0.le
  have e2 : n * (c / n ^ 2) = c / n := by field_simp
  nlinarith

/-- **Grid control.** A monotone `H` that is `θ`-close on the grid `d ℕ` to an `f` with
`f y - f x ≤ y - x` (`0 ≤ x ≤ y`) on the
grid `d ℕ` is `(θ + d)`-close to it at every `c`. -/
theorem abs_sub_le_of_grid {H : ℕ → ℝ} {f : ℝ → ℝ} (hH : Monotone H)
    (hlip : ∀ x y, 0 ≤ x → x ≤ y → f y - f x ≤ y - x) {d : ℕ} (hd : 0 < d) {θ : ℝ} (c : ℕ)
    (hgrid : ∀ i ≤ c / d + 1, |H (i * d) - f ((i * d : ℕ) : ℝ)| ≤ θ) :
    |H c - f c| ≤ θ + d := by
  set i := c / d
  have h1 : i * d ≤ c := Nat.div_mul_le_self c d
  have h2 : c < (i + 1) * d := by rw [add_mul, one_mul]; exact Nat.lt_div_mul_add hd
  have hlo := abs_le.1 (hgrid i (Nat.le_succ i))
  have hhi := abs_le.1 (hgrid (i + 1) le_rfl)
  have hH1 : H (i * d) ≤ H c := hH h1
  have hH2 : H c ≤ H ((i + 1) * d) := hH h2.le
  have c1 : ((i * d : ℕ) : ℝ) ≤ c := by exact_mod_cast h1
  have c2 : (c : ℝ) ≤ ((i + 1) * d : ℕ) := by exact_mod_cast h2.le
  have c3 : (((i + 1) * d : ℕ) : ℝ) - ((i * d : ℕ) : ℝ) = d := by push_cast; ring
  have hf1 := hlip _ _ (Nat.cast_nonneg _) c1
  have hf2 := hlip _ _ (Nat.cast_nonneg _) c2
  rw [abs_le]; constructor <;> linarith

theorem sum_Ico_half_pow_le (j₀ M : ℕ) : ∑ j ∈ Ico j₀ M, (1 / 2 : ℝ) ^ j ≤ 2 * (1 / 2) ^ j₀ := by
  rw [sum_Ico_eq_sum_range]
  simp_rw [pow_add]
  rw [← mul_sum, mul_comm]
  exact mul_le_mul_of_nonneg_right (sum_geometric_two_le _) (by positivity)

theorem sum_Ico_ite_two_pow_lt_le {y : ℝ} (hy : 0 ≤ y) (j₀ M : ℕ) :
    ∑ j ∈ Ico j₀ M, (if (2 : ℝ) ^ j < y then (2 : ℝ) ^ j else 0) ≤ 2 * y := by
  have hnn : ∀ j, 0 ≤ (if (2 : ℝ) ^ j < y then (2 : ℝ) ^ j else 0) := fun j => by
    split_ifs <;> positivity
  refine le_trans (sum_le_sum_of_subset_of_nonneg (by
    intro j hj; exact mem_range.2 (mem_Ico.1 hj).2) fun j _ _ => hnn j) ?_
  induction M with
  | zero => simp; linarith
  | succ M ih =>
    rw [sum_range_succ]
    split_ifs with hM
    · have hle : ∑ j ∈ range M, (if (2 : ℝ) ^ j < y then (2 : ℝ) ^ j else 0) ≤
          ∑ j ∈ range M, (2 : ℝ) ^ j := sum_le_sum fun j _ => by
        split_ifs
        · exact le_rfl
        · positivity
      have hgeom : ∑ j ∈ range M, (2 : ℝ) ^ j = 2 ^ M - 1 := by
        rw [geom_sum_eq (by norm_num)]; ring
      linarith
    · simpa using ih

end Analysis


/-! ### Small outbreaks -/

section SmallOutbreak

variable {N : ℕ} (S₀ : Finset (Fin N))

theorem epi_snd_mono (ξ : ℕ → ℕ → ℕ) (v : ℕ → Fin N) : Monotone fun n => (epi ξ v S₀ n).2 :=
  monotone_nat_of_le_succ fun n => by
    change (epi ξ v S₀ n).2 ≤ (epi ξ v S₀ n).2 + _
    exact Nat.le_add_right _ _

theorem epi_snd_le_totalContacts (ξ : ℕ → ℕ → ℕ) (v : ℕ → Fin N) (n : ℕ) :
    (epi ξ v S₀ n).2 ≤ totalContacts ξ v S₀ := by
  rw [totalContacts, ← epi_eq_epi_card_add_one ξ v S₀ (le_max_right n (S₀.card + 1))]
  exact epi_snd_mono S₀ ξ v (le_max_left _ _)

/-- **Small outbreaks are branching-process extinctions.** If the first `K` contacts all hit
and fewer than `K` individuals are ever infected, the branching process dies out. -/
theorem exists_bpSize_eq_zero_of_finalSize_lt (ξ : ℕ → ℕ → ℕ) (v : ℕ → Fin N) {K : ℕ}
    (hhit : ∀ j < K, epiHit v S₀ j) (hF : finalSize ξ v S₀ < K) : ∃ n, bpSize ξ n = 0 := by
  have hC : totalContacts ξ v S₀ < K := by
    by_contra hCK
    push Not at hCK
    have : K ≤ finalSize ξ v S₀ := by
      rw [finalSize_eq_hits]
      calc K = hits S₀ v K := by
            rw [hits, filter_true_of_mem fun j hj => hhit j (mem_range.1 hj), card_range]
        _ ≤ _ := hits_mono S₀ v hCK
    omega
  have key : ∀ n, bpContacts ξ n ≤ K := by
    intro n
    induction n with
    | zero => simp [bpContacts]
    | succ n ih =>
      have he := epi_eq_of_forall_hit ξ v S₀ hhit ih
      have : bpContacts ξ (n + 1) = (epi ξ v S₀ (n + 1)).2 := by
        rw [bpContacts_succ, bpSize_succ]
        change _ = (epi ξ v S₀ n).2 + ∑ i ∈ range (epi ξ v S₀ n).1, ξ n i
        rw [he]
      rw [this]
      exact ((epi_snd_le_totalContacts S₀ ξ v _).trans hC.le)
  refine ⟨S₀.card + 1, ?_⟩
  have he := epi_eq_of_forall_hit ξ v S₀ hhit (key (S₀.card + 1))
  have h0 := epiSize_card_add_one_eq_zero ξ v S₀
  rw [epiSize, he] at h0
  exact h0

/-- **Dyadic case split.** If `2^j ≤ F < 2^{j+1}`, either the centered contact count is large,
or many of the first `⌊4 R 2^j⌋` contacts go outside `S₀` or repeat. -/
theorem dyadic_case_split (w : Config N) {R : ℝ} (hR : 1 < R) (j : ℕ)
    (hF1 : 2 ^ j ≤ finalSize (fun n i => w.1 (n, i)) w.2 S₀)
    (hF2 : finalSize (fun n i => w.1 (n, i)) w.2 S₀ < 2 ^ (j + 1)) :
    (R - 1) * 2 ^ j / 2 ≤ |truncDev S₀ R (2 ^ (j + 1) + 1) w| ∨
    (R - 1) * 2 ^ j / 4 ≤ outsideContacts S₀ w.2 ⌊4 * R * 2 ^ j⌋₊ ∨
    (R - 1) * 2 ^ j / 4 ≤ repeatContacts w.2 ⌊4 * R * 2 ^ j⌋₊ := by
  set F := finalSize (fun n i => w.1 (n, i)) w.2 S₀ with hF
  set C := totalContacts (fun n i => w.1 (n, i)) w.2 S₀ with hC
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨hD, hO, hRep⟩ := hcon
  have hDeq := truncDev_eq S₀ R w (L := 2 ^ (j + 1) + 1) (by omega)
  rw [hDeq] at hD
  have hD' := abs_lt.1 hD
  have hF1r : (2 : ℝ) ^ j ≤ F := by exact_mod_cast hF1
  have hF2r : (F : ℝ) + 1 ≤ 2 * 2 ^ j := by
    have : F + 1 ≤ 2 ^ (j + 1) := hF2
    rw [pow_succ] at this; exact_mod_cast (by omega : F + 1 ≤ 2 * 2 ^ j)
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hCle : (C : ℝ) ≤ 4 * R * 2 ^ j := by nlinarith
  have hCfl : C ≤ ⌊4 * R * 2 ^ j⌋₊ := Nat.le_floor hCle
  have hFC : F ≤ C := by rw [hF, finalSize_eq_hits]; exact hits_le S₀ w.2 C
  have hwaste := sub_hits_le S₀ w.2 C
  rw [← finalSize_eq_hits] at hwaste
  have h1 : ((C - F : ℕ) : ℝ) ≤ outsideContacts S₀ w.2 ⌊4 * R * 2 ^ j⌋₊ +
      repeatContacts w.2 ⌊4 * R * 2 ^ j⌋₊ := by
    exact_mod_cast hwaste.trans (add_le_add (outsideContacts_mono S₀ w.2 hCfl)
      (repeatContacts_mono w.2 hCfl))
  rw [Nat.cast_sub hFC] at h1
  nlinarith

end SmallOutbreak


section Dyadic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν : Measure ℕ} {N : ℕ}
  {ξ : ℕ → ℕ → Ω → ℕ} {U : ℕ → Ω → Fin N}

namespace IsFinalSizeEpidemic

variable [IsProbabilityMeasure ν]

/-- **One dyadic block of small outbreaks.** The probability that `2^j ≤ F < 2^{j+1}` and
`F < δ N` is at most `12 σ² / (r² 2^j) + 256 R p₀ / (r² 2^j)`, plus `64 R² 2^j / (r N)` if
`2^j < δ N`, where `R = m > 1`, `r = R - 1` and `p₀ = (N - #S₀) / N ≤ r / (32 R)`. -/
theorem measureReal_dyadic_le (h : IsFinalSizeEpidemic P ν N ξ U)
    (h2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) ν) (hm : 1 < offspringMean ν)
    (S₀ : Finset (Fin N)) (j : ℕ) (δ : ℝ)
    (hp : ((N - S₀.card : ℕ) : ℝ) / N ≤ (offspringMean ν - 1) / (32 * offspringMean ν)) :
    P.real {ω | 2 ^ j ≤ finalSize (ξ · · ω) (U · ω) S₀ ∧
        finalSize (ξ · · ω) (U · ω) S₀ < 2 ^ (j + 1) ∧
        (finalSize (ξ · · ω) (U · ω) S₀ : ℝ) < δ * N} ≤
      12 * offspringVar ν / (offspringMean ν - 1) ^ 2 * (1 / 2) ^ j +
      256 * offspringMean ν * (((N - S₀.card : ℕ) : ℝ) / N) / (offspringMean ν - 1) ^ 2 *
        (1 / 2) ^ j +
      (if (2 : ℝ) ^ j < δ * N then 64 * offspringMean ν ^ 2 / ((offspringMean ν - 1) * N) *
        2 ^ j else 0) := by
  have := h.isProbabilityMeasure
  set R := offspringMean ν with hR
  set r := R - 1 with hr_def
  set σ2 := offspringVar ν
  set p₀ := ((N - S₀.card : ℕ) : ℝ) / N with hp₀
  set c : ℕ := ⌊4 * R * 2 ^ j⌋₊ with hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero h.ne_zero
  have hr : 0 < r := by linarith
  have hR0 : 0 < R := by linarith
  have hσ : 0 ≤ σ2 := offspringVar_nonneg ν
  have hp0 : 0 ≤ p₀ := by positivity
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hcle : (c : ℝ) ≤ 4 * R * 2 ^ j := Nat.floor_le (by positivity)
  have hhalf : (1 / 2 : ℝ) ^ j = 1 / 2 ^ j := by rw [one_div_pow]
  have hnn : 0 ≤ 12 * σ2 / r ^ 2 * (1 / 2) ^ j + 256 * R * p₀ / r ^ 2 * (1 / 2) ^ j := by
    positivity
  by_cases hj : (2 : ℝ) ^ j < δ * N
  · simp only [hj, ↓reduceIte]
    have hsub : {ω | 2 ^ j ≤ finalSize (ξ · · ω) (U · ω) S₀ ∧
        finalSize (ξ · · ω) (U · ω) S₀ < 2 ^ (j + 1) ∧
        (finalSize (ξ · · ω) (U · ω) S₀ : ℝ) < δ * N} ⊆
        ({ω | r * 2 ^ j / 2 ≤ |truncDev S₀ R (2 ^ (j + 1) + 1) (config ξ U ω)|} ∪
          {ω | r * 2 ^ j / 8 ≤ |(outsideContacts S₀ (U · ω) c : ℝ) - c * p₀|}) ∪
          {ω | r * 2 ^ j / 4 ≤ (repeatContacts (U · ω) c : ℝ)} := by
      rintro ω ⟨h1, h2', -⟩
      rcases dyadic_case_split S₀ (config ξ U ω) hm j h1 h2' with H | H | H
      · exact Or.inl (Or.inl H)
      · refine Or.inl (Or.inr ?_)
        have hcp : (c : ℝ) * p₀ ≤ r * 2 ^ j / 8 := by
          calc (c : ℝ) * p₀ ≤ 4 * R * 2 ^ j * (r / (32 * R)) := by gcongr
            _ = r * 2 ^ j / 8 := by field_simp; ring
        have H' : r * 2 ^ j / 4 ≤ (outsideContacts S₀ (U · ω) c : ℝ) := H
        change r * 2 ^ j / 8 ≤ |(outsideContacts S₀ (U · ω) c : ℝ) - c * p₀|
        exact le_trans (by linarith) (le_abs_self _)
      · exact Or.inr H
    have b1 := h.measureReal_le_abs_truncDev h2 S₀ (2 ^ (j + 1) + 1)
      (by positivity : 0 < r * 2 ^ j / 2)
    have b2 := h.measureReal_le_abs_outsideContacts_sub S₀ c (by positivity : 0 < r * 2 ^ j / 8)
    have b3 := h.measureReal_le_repeatContacts c (by positivity : 0 < r * 2 ^ j / 4)
    have b1' : σ2 * ((2 ^ (j + 1) + 1 : ℕ) : ℝ) / (r * 2 ^ j / 2) ^ 2 ≤
        12 * σ2 / r ^ 2 * (1 / 2) ^ j := by
      have hL : ((2 ^ (j + 1) + 1 : ℕ) : ℝ) ≤ 3 * 2 ^ j := by
        push_cast; rw [pow_succ]
        have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
        linarith
      calc σ2 * ((2 ^ (j + 1) + 1 : ℕ) : ℝ) / (r * 2 ^ j / 2) ^ 2
          ≤ σ2 * (3 * 2 ^ j) / (r * 2 ^ j / 2) ^ 2 := by gcongr
        _ = 12 * σ2 / r ^ 2 * (1 / 2) ^ j := by rw [hhalf]; field_simp; ring
    have b2' : (c : ℝ) * p₀ / (r * 2 ^ j / 8) ^ 2 ≤ 256 * R * p₀ / r ^ 2 * (1 / 2) ^ j := by
      calc (c : ℝ) * p₀ / (r * 2 ^ j / 8) ^ 2 ≤ 4 * R * 2 ^ j * p₀ / (r * 2 ^ j / 8) ^ 2 := by
            gcongr
        _ = 256 * R * p₀ / r ^ 2 * (1 / 2) ^ j := by rw [hhalf]; field_simp; ring
    have b3' : (c : ℝ) ^ 2 / (N * (r * 2 ^ j / 4)) ≤ 64 * R ^ 2 / (r * N) * 2 ^ j := by
      calc (c : ℝ) ^ 2 / (N * (r * 2 ^ j / 4)) ≤ (4 * R * 2 ^ j) ^ 2 / (N * (r * 2 ^ j / 4)) := by
            gcongr
        _ = 64 * R ^ 2 / (r * N) * 2 ^ j := by field_simp; ring
    calc _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ _ := measureReal_union_le _ _
      _ ≤ _ := add_le_add_left (measureReal_union_le _ _) _
      _ ≤ _ := by linarith
  · simp only [hj, ↓reduceIte, add_zero]
    have hempty : {ω | 2 ^ j ≤ finalSize (ξ · · ω) (U · ω) S₀ ∧
        finalSize (ξ · · ω) (U · ω) S₀ < 2 ^ (j + 1) ∧
        (finalSize (ξ · · ω) (U · ω) S₀ : ℝ) < δ * N} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 _ h3
      have : (2 : ℝ) ^ j ≤ finalSize (ξ · · ω) (U · ω) S₀ := by exact_mod_cast h1
      exact hj (lt_of_le_of_lt this h3)
    rw [hempty, measureReal_empty]
    exact hnn

end IsFinalSizeEpidemic

end Dyadic

/-! ### The model is satisfiable -/

section Canonical

variable (ν : Measure ℕ) [IsProbabilityMeasure ν] (N : ℕ) [NeZero N]

/-- **Non-vacuity.** The coordinate maps of the canonical product space (`canonicalMeasure`) form
a model of the final-size theorem: on top of `IsEarlyEpidemic`, the targets are measurable and
independent of the offspring numbers. -/
theorem isFinalSizeEpidemic_canonical :
    IsFinalSizeEpidemic (canonicalMeasure ν N) ν N (fun n i ω => ω.1 (n, i))
      (fun j ω => ω.2 j) where
  toIsEarlyEpidemic := isEarlyEpidemic_canonical ν N
  measurable_target := fun j => (measurable_pi_apply j).comp measurable_snd
  indepFun_offspring_target := by
    have := isProbabilityMeasure_uniformOfFinset_univ N
    have hP : canonicalMeasure ν N = (Measure.infinitePi fun _ : ℕ × ℕ => ν).prod
        (Measure.infinitePi fun _ : ℕ => Measure.uniformOfFinset (univ : Finset (Fin N))) := rfl
    have : IsProbabilityMeasure (canonicalMeasure ν N) := by rw [hP]; infer_instance
    change IndepFun (fun ω : (ℕ × ℕ → ℕ) × (ℕ → Fin N) => ω.1) (fun ω => ω.2) _
    rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      measurable_snd.aemeasurable, hP, Measure.map_fst_prod, Measure.map_snd_prod]
    simp

end Canonical

/-! ### Large-population limits -/

section LargePopulation

variable {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)] {P : ∀ k, Measure (Ω k)} {ν : Measure ℕ}
  [IsProbabilityMeasure ν] {N : ℕ → ℕ} {ξ : ∀ k, ℕ → ℕ → Ω k → ℕ}
  {U : ∀ k, ℕ → Ω k → Fin (N k)} {S₀ : ∀ k, Finset (Fin (N k))}

/-- **Uniform law of large numbers for the hits.** With probability tending to `1`, the number
of hits among the first `c` contacts is within `ε N` of `N (1 - e^{-c/N})`, simultaneously for
all `c ≤ K N`. -/
theorem tendsto_measureReal_exists_abs_hits_sub
    (h : ∀ k, IsFinalSizeEpidemic (P k) ν (N k) (ξ k) (U k)) (hN : Tendsto N atTop atTop)
    (hS : Tendsto (fun k => ((N k - (S₀ k).card : ℕ) : ℝ) / N k) atTop (𝓝 0)) {ε K : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : 0 ≤ K) :
    Tendsto (fun k => (P k).real {ω | ∃ c : ℕ, (c : ℝ) ≤ K * N k ∧
      ε * N k < |(hits (S₀ k) (U k · ω) c : ℝ) - N k * (1 - Real.exp (-(c / N k)))|})
      atTop (𝓝 0) := by
  set B : ℝ := (8 * K / ε + 2) * (16 / ε ^ 2)
  have hNr : Tendsto (fun k => (N k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hS' : Tendsto (fun k => ((N k - (S₀ k).card : ℕ) : ℝ) / N k + (K + 1) / N k) atTop
      (𝓝 0) := by simpa using hS.add (tendsto_const_nhds.div_atTop hNr)
  refine squeeze_zero' (Eventually.of_forall fun k => measureReal_nonneg) ?_
    (tendsto_const_nhds.div_atTop hNr : Tendsto (fun k => B / N k) atTop (𝓝 0))
  filter_upwards [hNr.eventually_ge_atTop (8 / ε + 1),
    hS'.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))] with k hk1 hk2
  have := (h k).isProbabilityMeasure
  set n : ℝ := (N k : ℝ) with hn
  have hn1 : 1 ≤ n := le_trans (by have : 0 < 8 / ε := by positivity
                                   linarith) hk1
  have hn0 : 0 < n := by linarith
  have hεn : 8 < ε * n := by
    have : 8 / ε * ε = 8 := div_mul_cancel₀ 8 hε.ne'
    nlinarith
  have hsnN : (S₀ k).card ≤ N k := (card_le_univ (S₀ k)).trans (Fintype.card_fin _).le
  have hsn : ((S₀ k).card : ℝ) ≤ n := by rw [hn]; exact_mod_cast hsnN
  have hgap : (n - (S₀ k).card) + (K + 1) < ε * n / 4 := by
    have e : (((N k - (S₀ k).card : ℕ) : ℝ)) = n - (S₀ k).card := by
      rw [Nat.cast_sub hsnN, hn]
    rw [e, ← add_div, div_lt_iff₀ hn0] at hk2
    linarith
  set d : ℕ := ⌈ε * n / 8⌉₊ with hd
  have hd0 : 0 < d := Nat.ceil_pos.2 (by positivity)
  have hdlo : ε * n / 8 ≤ d := Nat.le_ceil _
  have hdhi : (d : ℝ) ≤ ε * n / 4 := by
    have := Nat.ceil_lt_add_one (by positivity : 0 ≤ ε * n / 8); rw [← hd] at this; linarith
  have hd0r : (0 : ℝ) < d := by exact_mod_cast hd0
  set I : ℕ := ⌊K * n / d⌋₊ + 1 with hI
  set μ : ℕ → ℝ := fun c => (S₀ k).card * (1 - ((n - 1) / n) ^ c)
  set f : ℝ → ℝ := fun x => n * (1 - Real.exp (-(x / n)))
  have hlip : ∀ x y, 0 ≤ x → x ≤ y → f y - f x ≤ y - x := by
    intro x y hx hxy
    have h1 := abs_exp_sub_exp_le_of_nonpos (a := -(x / n)) (b := -(y / n))
      (by have := div_nonneg hx hn0.le; linarith)
      (by have := div_nonneg (hx.trans hxy) hn0.le; linarith)
    have h2 : |-(x / n) - -(y / n)| = (y - x) / n := by
      rw [show -(x / n) - -(y / n) = (y - x) / n by ring, abs_of_nonneg (div_nonneg
        (by linarith) hn0.le)]
    rw [h2] at h1
    have h3 := (abs_le.1 h1).2
    simp only [f]
    have : n * ((y - x) / n) = y - x := by field_simp
    nlinarith
  have hsub : {ω | ∃ c : ℕ, (c : ℝ) ≤ K * n ∧
      ε * n < |(hits (S₀ k) (U k · ω) c : ℝ) - n * (1 - Real.exp (-(c / n)))|} ⊆
      ⋃ i ∈ range (I + 1),
        {ω | ε * n / 4 ≤ |(hits (S₀ k) (U k · ω) (i * d) : ℝ) - μ (i * d)|} := by
    rintro ω ⟨c, hcK, hc⟩
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le, mem_range] at hnot
    have hgrid : ∀ i ≤ c / d + 1,
        |(hits (S₀ k) (U k · ω) (i * d) : ℝ) - f ((i * d : ℕ) : ℝ)| ≤ ε * n / 2 := by
      intro i hi
      have hcI : c / d + 1 ≤ I := by
        have : c / d ≤ ⌊K * n / d⌋₊ := Nat.le_floor (by
          rw [le_div_iff₀ hd0r]
          calc ((c / d : ℕ) : ℝ) * d ≤ c := by exact_mod_cast Nat.div_mul_le_self c d
            _ ≤ K * n := hcK)
        omega
      have hiI : i ≤ I := hi.trans hcI
      have h1 := hnot i (Nat.lt_succ_of_le hiI)
      have hid : ((i * d : ℕ) : ℝ) ≤ K * n + d := by
        have hi' : (i : ℝ) ≤ K * n / d + 1 := by
          have := Nat.floor_le (by positivity : 0 ≤ K * n / d)
          have hiI' : (i : ℝ) ≤ I := by exact_mod_cast hiI
          rw [hI] at hiI'; push_cast at hiI'; linarith
        push_cast
        calc (i : ℝ) * d ≤ (K * n / d + 1) * d := by gcongr
          _ = K * n + d := by field_simp
      have h2 := abs_mean_hits_sub_le hn1 hsn (i * d)
      have h3 : ((i * d : ℕ) : ℝ) / n ≤ K + 1 := by
        rw [div_le_iff₀ hn0]; nlinarith
      calc |(hits (S₀ k) (U k · ω) (i * d) : ℝ) - f ((i * d : ℕ) : ℝ)|
          ≤ |(hits (S₀ k) (U k · ω) (i * d) : ℝ) - μ (i * d)| +
            |μ (i * d) - f ((i * d : ℕ) : ℝ)| := abs_sub_le _ _ _
        _ ≤ ε * n / 4 + ((n - (S₀ k).card) + (K + 1)) :=
            add_le_add h1.le (h2.trans (by linarith))
        _ ≤ ε * n / 2 := by linarith
    have := abs_sub_le_of_grid (H := fun c => (hits (S₀ k) (U k · ω) c : ℝ))
      (fun a b hab => Nat.cast_le.2 (hits_mono (S₀ k) (fun x => U k x ω) hab)) hlip hd0 c hgrid
    simp only [f] at this
    linarith
  have hI1 : ((I + 1 : ℕ) : ℝ) ≤ 8 * K / ε + 2 := by
    have h1 := Nat.floor_le (by positivity : 0 ≤ K * n / d)
    have h2 : K * n / d ≤ K * n / (ε * n / 8) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hdlo
    have h3 : K * n / (ε * n / 8) = 8 * K / ε := by field_simp
    rw [hI]; push_cast; linarith
  calc (P k).real {ω | ∃ c : ℕ, (c : ℝ) ≤ K * n ∧
        ε * n < |(hits (S₀ k) (U k · ω) c : ℝ) - n * (1 - Real.exp (-(c / n)))|}
      ≤ (P k).real (⋃ i ∈ range (I + 1),
          {ω | ε * n / 4 ≤ |(hits (S₀ k) (U k · ω) (i * d) : ℝ) - μ (i * d)|}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i ∈ range (I + 1), (P k).real
          {ω | ε * n / 4 ≤ |(hits (S₀ k) (U k · ω) (i * d) : ℝ) - μ (i * d)|} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ range (I + 1), (16 / (ε ^ 2 * n)) := by
        refine sum_le_sum fun i _ => ((h k).measureReal_le_abs_hits_sub (S₀ k) (i * d)
          (by positivity : 0 < ε * n / 4)).trans ?_
        calc ((S₀ k).card : ℝ) / (ε * n / 4) ^ 2 ≤ n / (ε * n / 4) ^ 2 := by gcongr
          _ = 16 / (ε ^ 2 * n) := by field_simp; ring
    _ = ((I + 1 : ℕ) : ℝ) * (16 / (ε ^ 2 * n)) := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ (8 * K / ε + 2) * (16 / (ε ^ 2 * n)) := by gcongr
    _ = B / n := by simp only [B]; field_simp

/-- The centered contact count is `o(N)` in probability. -/
theorem tendsto_measureReal_le_abs_truncDev
    (h : ∀ k, IsFinalSizeEpidemic (P k) ν (N k) (ξ k) (U k))
    (h2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) ν) (hN : Tendsto N atTop atTop) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun k => (P k).real {ω | ε * N k ≤
      |truncDev (S₀ k) (offspringMean ν) (N k + 1) (config (ξ k) (U k) ω)|}) atTop (𝓝 0) := by
  have hNr : Tendsto (fun k => (N k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  refine squeeze_zero' (Eventually.of_forall fun k => measureReal_nonneg) ?_
    (tendsto_const_nhds.div_atTop hNr :
      Tendsto (fun k => 2 * offspringVar ν / ε ^ 2 / N k) atTop (𝓝 0))
  filter_upwards [hNr.eventually_ge_atTop 1] with k hk
  have hσ := offspringVar_nonneg ν
  refine ((h k).measureReal_le_abs_truncDev h2 (S₀ k) (N k + 1) (by positivity)).trans ?_
  push_cast
  calc offspringVar ν * ((N k : ℝ) + 1) / (ε * N k) ^ 2
      ≤ offspringVar ν * (2 * N k) / (ε * N k) ^ 2 := by gcongr; linarith
    _ = 2 * offspringVar ν / ε ^ 2 / N k := by field_simp

/-- **Major outbreaks have final size `τ N`.** As `N → ∞`, with probability tending to `1` the
fraction `F / N` of the population ultimately infected is either below `δ` or within `δ` of the
non-zero root `τ` of the final-size equation `1 - τ = e^{-R₀ τ}`. -/
theorem tendsto_measureReal_finalSize_far
    (h : ∀ k, IsFinalSizeEpidemic (P k) ν (N k) (ξ k) (U k))
    (h2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) ν) (hm : 1 < offspringMean ν)
    (hN : Tendsto N atTop atTop)
    (hS : Tendsto (fun k => ((N k - (S₀ k).card : ℕ) : ℝ) / N k) atTop (𝓝 0)) {δ : ℝ}
    (hδ : 0 < δ) :
    Tendsto (fun k => (P k).real {ω | δ ≤ (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) / N k ∧
      δ ≤ |(finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) / N k -
        finalSizeRoot (offspringMean ν)|}) atTop (𝓝 0) := by
  set R := offspringMean ν with hR
  obtain ⟨η, hη, hηprop⟩ := exists_pos_forall_abs_finalSizeGap_le hm hδ
  set ε := min (η / 4) 1 with hε_def
  have hε : 0 < ε := lt_min (by positivity) one_pos
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hεη : ε ≤ η / 4 := min_le_left _ _
  have hA := tendsto_measureReal_le_abs_truncDev (S₀ := S₀) h h2 hN hε
  have hB := tendsto_measureReal_exists_abs_hits_sub h hN hS hε hε1
    (K := 2 * R + 1) (by linarith)
  have hNr : Tendsto (fun k => (N k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  refine squeeze_zero' (Eventually.of_forall fun k => measureReal_nonneg) ?_
    (by simpa using hA.add hB)
  filter_upwards [hNr.eventually_ge_atTop (max 1 (4 * R / η))] with k hk
  have := (h k).isProbabilityMeasure
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  rintro ω ⟨hx1, hx2⟩
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, not_exists, not_and,
    not_lt] at hcon
  obtain ⟨hA', hB'⟩ := hcon
  set n : ℝ := (N k : ℝ) with hn
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hk
  have hn0 : 0 < n := by linarith
  have hnR : R / n ≤ η / 4 := by
    rw [div_le_iff₀ hn0]
    have := le_trans (le_max_right _ _) hk
    rw [div_le_iff₀ hη] at this
    linarith
  set F := finalSize (ξ k · · ω) (U k · ω) (S₀ k) with hF
  set C := totalContacts (ξ k · · ω) (U k · ω) (S₀ k) with hC
  have hFN : F ≤ N k :=
    (finalSize_le_card _ _ _).trans ((card_le_univ _).trans (Fintype.card_fin _).le)
  have hD : truncDev (S₀ k) R (N k + 1) (config (ξ k) (U k) ω) = (C : ℝ) - R * (F + 1) :=
    truncDev_eq (S₀ k) R (config (ξ k) (U k) ω) (by change F + 1 ≤ N k + 1; omega)
  rw [hD] at hA'
  have hFr : (F : ℝ) ≤ n := by rw [hn]; exact_mod_cast hFN
  have hF0 : (0 : ℝ) ≤ F := Nat.cast_nonneg _
  have hCle : (C : ℝ) ≤ (2 * R + 1) * n := by
    have := (abs_lt.1 hA').2
    nlinarith
  have hH := hB' C hCle
  rw [← finalSize_eq_hits] at hH
  set x := (F : ℝ) / n with hx
  have hx0 : 0 ≤ x := div_nonneg hF0 hn0.le
  have hx1' : x ≤ 1 := (div_le_one hn0).2 hFr
  have ha : |1 - Real.exp (-(C / n)) - x| ≤ ε := by
    have e : 1 - Real.exp (-(C / n)) - x = -((F - n * (1 - Real.exp (-(C / n)))) / n) := by
      rw [hx]; field_simp; ring
    rw [e, abs_neg, abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
    linarith
  have hb : |Real.exp (-(C / n)) - Real.exp (-(R * x))| ≤ ε + η / 4 := by
    refine (abs_exp_sub_exp_le_of_nonpos (by have := div_nonneg (Nat.cast_nonneg C) hn0.le
                                             linarith)
      (by have := mul_nonneg (by linarith : (0 : ℝ) ≤ R) hx0; linarith)).trans ?_
    have e : -(C / n) - -(R * x) = -(((C : ℝ) - R * (F + 1) + R) / n) := by
      rw [hx]; field_simp; ring
    rw [e, abs_neg, abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
    have h1 := abs_add_le ((C : ℝ) - R * (F + 1)) R
    rw [abs_of_pos (by linarith : (0 : ℝ) < R)] at h1
    have : R ≤ η / 4 * n := by rwa [div_le_iff₀ hn0] at hnR
    nlinarith
  have hgap : |finalSizeGap R x| ≤ η := by
    have e : finalSizeGap R x = (1 - Real.exp (-(C / n)) - x) +
        (Real.exp (-(C / n)) - Real.exp (-(R * x))) := by unfold finalSizeGap; ring
    rw [e]
    linarith [abs_add_le (1 - Real.exp (-(C / n)) - x)
      (Real.exp (-(C / n)) - Real.exp (-(R * x)))]
  rcases hηprop x ⟨hx0, hx1'⟩ hgap with h' | h' <;> linarith

/-- **Small outbreaks are minor.** For every `θ > 0` there is `δ₀ > 0` such that eventually
`P(F < δ₀ N) ≤ q + θ`, where `q` is the extinction probability of the branching process: an
outbreak that survives the branching phase reaches a positive fraction of the population. -/
theorem exists_eventually_measureReal_finalSize_lt_le
    (h : ∀ k, IsFinalSizeEpidemic (P k) ν (N k) (ξ k) (U k))
    (h2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) ν) (hm : 1 < offspringMean ν)
    (hN : Tendsto N atTop atTop)
    (hS : Tendsto (fun k => ((N k - (S₀ k).card : ℕ) : ℝ) / N k) atTop (𝓝 0)) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ δ₀ > 0, ∀ᶠ k in atTop, (P k).real
      {ω | (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) < δ₀ * N k} ≤ extinctionProb ν + θ := by
  set R := offspringMean ν with hR
  set r := R - 1 with hr_def
  set σ2 := offspringVar ν with hσ2
  have hr : 0 < r := by linarith
  have hR0 : 0 < R := by linarith
  have hσ := offspringVar_nonneg ν
  have hgeo : Tendsto (fun j : ℕ => 12 * σ2 / r ^ 2 * (2 * (1 / 2 : ℝ) ^ j)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul 2).const_mul (12 * σ2 / r ^ 2)
  obtain ⟨j₀, hj₀⟩ := (hgeo.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < θ / 4))).exists
  set K : ℕ := 2 ^ j₀ with hK
  set δ₀ : ℝ := θ * r / (512 * R ^ 2) with hδ₀
  refine ⟨δ₀, by positivity, ?_⟩
  have hNr : Tendsto (fun k => (N k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hb : Tendsto (fun k => ((K * (N k - (S₀ k).card) + K.choose 2 : ℕ) : ℝ) / N k) atTop
      (𝓝 0) := by
    have heq : (fun k => ((K * (N k - (S₀ k).card) + K.choose 2 : ℕ) : ℝ) / N k) =
        fun k => (K : ℝ) * (((N k - (S₀ k).card : ℕ) : ℝ) / N k) + (K.choose 2 : ℝ) / N k := by
      ext k; simp only [Nat.cast_add, Nat.cast_mul]; ring
    rw [heq]
    simpa using (hS.const_mul (K : ℝ)).add (tendsto_const_nhds.div_atTop hNr)
  have hpmin : 0 < min (r / (32 * R)) (θ * r ^ 2 / (2048 * R)) := lt_min (by positivity)
    (by positivity)
  filter_upwards [hS.eventually (gt_mem_nhds hpmin), hb.eventually (gt_mem_nhds
    (by positivity : (0 : ℝ) < θ / 4))] with k hp hb'
  have := (h k).isProbabilityMeasure
  set p₀ := ((N k - (S₀ k).card : ℕ) : ℝ) / N k with hp₀
  have hp0 : 0 ≤ p₀ := by positivity
  have hp1 : p₀ ≤ r / (32 * R) := (lt_of_lt_of_le hp (min_le_left _ _)).le
  have hp2 : 512 * R * p₀ / r ^ 2 ≤ θ / 4 := by
    have := (lt_of_lt_of_le hp (min_le_right _ _)).le
    rw [div_le_iff₀ (by positivity)]
    calc 512 * R * p₀ ≤ 512 * R * (θ * r ^ 2 / (2048 * R)) := by gcongr
      _ = θ / 4 * r ^ 2 := by field_simp; ring
  have hN0 : (0 : ℝ) < N k := by exact_mod_cast Nat.pos_of_ne_zero (h k).ne_zero
  set Fω : Ω k → ℕ := fun ω => finalSize (ξ k · · ω) (U k · ω) (S₀ k) with hFω
  set B : ℕ → Set (Ω k) := fun j => {ω | 2 ^ j ≤ Fω ω ∧ Fω ω < 2 ^ (j + 1) ∧
    (Fω ω : ℝ) < δ₀ * N k} with hB
  have hcover : {ω | (Fω ω : ℝ) < δ₀ * N k} ⊆
      ({ω | ∃ n, bpSize (ξ k · · ω) n = 0} ∪
        {ω | ∃ j < K, ¬ epiHit (U k · ω) (S₀ k) j}) ∪ ⋃ j ∈ Ico j₀ (N k + 1), B j := by
    intro ω hω
    by_cases hFK : Fω ω < K
    · refine Or.inl ?_
      by_cases hall : ∀ j < K, epiHit (U k · ω) (S₀ k) j
      · exact Or.inl (exists_bpSize_eq_zero_of_finalSize_lt (S₀ k) _ _ hall hFK)
      · push Not at hall; exact Or.inr hall
    · push Not at hFK
      refine Or.inr (Set.mem_biUnion (x := Nat.log 2 (Fω ω)) ?_ ?_)
      · have hFN : Fω ω ≤ N k := (finalSize_le_card _ _ _).trans
          ((card_le_univ _).trans (Fintype.card_fin _).le)
        refine mem_Ico.2 ⟨Nat.le_log_of_pow_le (by norm_num) hFK, ?_⟩
        exact Nat.lt_succ_of_le ((Nat.log_le_self 2 _).trans hFN)
      · have hF0 : Fω ω ≠ 0 := by
          have : 1 ≤ K := Nat.one_le_two_pow; omega
        exact ⟨Nat.pow_log_le_self 2 hF0, Nat.lt_pow_succ_log_self (by norm_num) _, hω⟩
  have hbp : (P k).real {ω | ∃ n, bpSize (ξ k · · ω) n = 0} = extinctionProb ν :=
    (h k).toIsEarlyEpidemic.toIsOffspringFamily.measureReal_exists_bpSize_eq_zero
  have hhit : (P k).real {ω | ∃ j < K, ¬ epiHit (U k · ω) (S₀ k) j} ≤
      ((K * (N k - (S₀ k).card) + K.choose 2 : ℕ) : ℝ) / N k := by
    rw [measureReal_def, div_eq_mul_inv, ← ENNReal.toReal_natCast (N k),
      ← ENNReal.toReal_natCast (K * (N k - (S₀ k).card) + K.choose 2), ← ENNReal.toReal_inv,
      ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.inv_ne_top.2 (by simp [(h k).ne_zero])))
      ((h k).measure_exists_not_epiHit_le (S₀ k) K)
  have hdy : ∀ j ∈ Ico j₀ (N k + 1), (P k).real (B j) ≤
      12 * σ2 / r ^ 2 * (1 / 2) ^ j + 256 * R * p₀ / r ^ 2 * (1 / 2) ^ j +
        64 * R ^ 2 / (r * N k) * (if (2 : ℝ) ^ j < δ₀ * N k then 2 ^ j else 0) := by
    intro j _
    rw [mul_ite, mul_zero]
    exact (h k).measureReal_dyadic_le h2 hm (S₀ k) j δ₀ hp1
  have hsum : ∑ j ∈ Ico j₀ (N k + 1), (12 * σ2 / r ^ 2 * (1 / 2) ^ j +
      256 * R * p₀ / r ^ 2 * (1 / 2) ^ j +
        64 * R ^ 2 / (r * N k) * (if (2 : ℝ) ^ j < δ₀ * N k then 2 ^ j else 0)) ≤ 3 * θ / 4 := by
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
    have g1 := sum_Ico_half_pow_le j₀ (N k + 1)
    have g2 := sum_Ico_ite_two_pow_lt_le (by positivity : 0 ≤ δ₀ * N k) j₀ (N k + 1)
    have hhalf : (1 / 2 : ℝ) ^ j₀ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have t1 : 12 * σ2 / r ^ 2 * ∑ j ∈ Ico j₀ (N k + 1), (1 / 2 : ℝ) ^ j ≤ θ / 4 :=
      (mul_le_mul_of_nonneg_left g1 (by positivity)).trans hj₀.le
    have t2 : 256 * R * p₀ / r ^ 2 * ∑ j ∈ Ico j₀ (N k + 1), (1 / 2 : ℝ) ^ j ≤ θ / 4 := by
      refine (mul_le_mul_of_nonneg_left (g1.trans (by linarith : 2 * (1 / 2 : ℝ) ^ j₀ ≤ 2))
        (by positivity)).trans ?_
      calc 256 * R * p₀ / r ^ 2 * 2 = 512 * R * p₀ / r ^ 2 := by ring
        _ ≤ θ / 4 := hp2
    have t3 : 64 * R ^ 2 / (r * N k) *
        ∑ j ∈ Ico j₀ (N k + 1), (if (2 : ℝ) ^ j < δ₀ * N k then (2 : ℝ) ^ j else 0) ≤ θ / 4 := by
      refine (mul_le_mul_of_nonneg_left g2 (by positivity)).trans (le_of_eq ?_)
      rw [hδ₀]; field_simp; ring
    linarith
  calc (P k).real {ω | (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) < δ₀ * N k}
      ≤ (P k).real ({ω | ∃ n, bpSize (ξ k · · ω) n = 0} ∪
          {ω | ∃ j < K, ¬ epiHit (U k · ω) (S₀ k) j}) +
        (P k).real (⋃ j ∈ Ico j₀ (N k + 1), B j) :=
        (measureReal_mono hcover (measure_ne_top _ _)).trans (measureReal_union_le _ _)
    _ ≤ (extinctionProb ν + θ / 4) + 3 * θ / 4 := by
        gcongr
        · exact (measureReal_union_le _ _).trans (by rw [hbp]; linarith)
        · exact (measureReal_biUnion_finset_le _ _).trans ((sum_le_sum hdy).trans hsum)
    _ = extinctionProb ν + θ := by ring

private lemma tendsto_measureReal_Ioi' (μ : Measure ℕ) [IsFiniteMeasure μ] :
    Tendsto (fun L : ℕ => μ.real (Set.Ioi L)) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun L : ℕ => Set.Ioi L)
    (fun _ => measurableSet_Ioi.nullMeasurableSet) (fun _ _ hab => Set.Ioi_subset_Ioi hab)
    ⟨0, measure_ne_top _ _⟩
  have he : (⋂ L : ℕ, Set.Ioi L) = ∅ :=
    Set.eq_empty_of_forall_notMem fun k hk => lt_irrefl k (Set.mem_iInter.1 hk k)
  rw [he, measure_empty] at h
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

/-- **Minor outbreaks stay small.** For every `δ > 0`, eventually
`P(F < δ N) ≥ q - θ`: an epidemic whose branching process dies out quickly infects a bounded
number of individuals. -/
theorem eventually_le_measureReal_finalSize_lt
    (h : ∀ k, IsFinalSizeEpidemic (P k) ν (N k) (ξ k) (U k)) (hN : Tendsto N atTop atTop)
    {δ θ : ℝ} (hδ : 0 < δ) (hθ : 0 < θ) :
    ∀ᶠ k in atTop, extinctionProb ν - θ ≤
      (P k).real {ω | (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) < δ * N k} := by
  obtain ⟨n, hn⟩ := ((tendsto_law_real_zero ν).eventually
    (lt_mem_nhds (by linarith : extinctionProb ν - θ / 2 < extinctionProb ν))).exists
  have htail : Tendsto (fun L : ℕ => ∑ m ∈ range n, (law ν m).real (Set.Ioi L)) atTop
      (𝓝 0) := by
    simpa using tendsto_finsetSum (range n) fun m _ => tendsto_measureReal_Ioi' (law ν m)
  obtain ⟨L, hL⟩ := (htail.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < θ / 2))).exists
  have hNr : Tendsto (fun k => (N k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  filter_upwards [hNr.eventually_gt_atTop (((n * L : ℕ) : ℝ) / δ)] with k hk
  have := (h k).isProbabilityMeasure
  have hZ := (h k).toIsEarlyEpidemic.toIsOffspringFamily
  have hnL : ((n * L : ℕ) : ℝ) < δ * N k := by
    have := (div_lt_iff₀ hδ).1 hk; linarith [mul_comm (N k : ℝ) δ]
  have hsub : {ω | bpSize (ξ k · · ω) n = 0} ⊆
      {ω | (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) < δ * N k} ∪
        ⋃ m ∈ range n, (fun ω => bpSize (ξ k · · ω) m) ⁻¹' Set.Ioi L := by
    intro ω (hω : bpSize _ n = 0)
    by_cases hall : ∀ m ∈ range n, bpSize (ξ k · · ω) m ≤ L
    · left
      have hI : epiSize (ξ k · · ω) (U k · ω) (S₀ k) n = 0 :=
        Nat.eq_zero_of_le_zero (hω ▸ epiSize_le_bpSize _ _ _ n)
      have h1 := finalSize_lt_of_epiSize_eq_zero _ _ _ hI
      have h2 : ∑ m ∈ range n, epiSize (ξ k · · ω) (U k · ω) (S₀ k) m ≤ n * L :=
        (sum_le_sum fun m hm => (epiSize_le_bpSize _ _ _ m).trans (hall m hm)).trans
          (by simp)
      have h3 : (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) < ((n * L : ℕ) : ℝ) := by
        exact_mod_cast lt_of_lt_of_le h1 h2
      change (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) < δ * N k
      linarith
    · right
      push Not at hall
      obtain ⟨m, hm, hmL⟩ := hall
      exact Set.mem_biUnion hm hmL
  have hlaw : ∀ m, (P k).real ((fun ω => bpSize (ξ k · · ω) m) ⁻¹' Set.Ioi L) =
      (law ν m).real (Set.Ioi L) := fun m => by
    rw [← (hZ.hasLaw_bpSize m).map_eq, map_measureReal_apply (hZ.measurable_bpSize m)
      measurableSet_Ioi]
  have h0 := hZ.measureReal_bpSize_eq_zero n
  have hle := (measureReal_mono (μ := P k) hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_biUnion_finset_le _ _)))
  rw [h0] at hle
  simp_rw [hlaw] at hle
  linarith

/-- **Final size: minor outbreaks.** For `R₀ = mean ν > 1` (finite variance), in the
large-population limit the probability that less than a fraction `δ ∈ (0, τ)` of the population
is ultimately infected converges to the extinction probability `q` of the branching process. -/
theorem tendsto_measureReal_finalSize_div_lt
    (h : ∀ k, IsFinalSizeEpidemic (P k) ν (N k) (ξ k) (U k))
    (h2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) ν) (hm : 1 < mean ν)
    (hN : Tendsto N atTop atTop)
    (hS : Tendsto (fun k => ((N k - (S₀ k).card : ℕ) : ℝ) / N k) atTop (𝓝 0)) {δ : ℝ}
    (hδ : 0 < δ) (hδτ : δ < finalSizeRoot (mean ν).toReal) :
    Tendsto (fun k => (P k).real
      {ω | (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) / N k < δ}) atTop
      (𝓝 (extinctionProb ν)) := by
  have hm' := one_lt_offspringMean h2 hm
  rw [← offspringMean_eq_toReal_mean h2] at hδτ
  set τ := finalSizeRoot (offspringMean ν)
  have hNr : Tendsto (fun k => (N k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hset : ∀ᶠ k in atTop, {ω | (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) / N k < δ} =
      {ω | (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) < δ * N k} := by
    filter_upwards [hNr.eventually_gt_atTop 0] with k hk
    ext ω; simp only [Set.mem_ofPred_eq, div_lt_iff₀ hk]
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [eventually_le_measureReal_finalSize_lt (S₀ := S₀) h hN hδ
      (by linarith : 0 < (extinctionProb ν - b) / 2), hset] with k hk hk'
    rw [hk']; linarith
  · obtain ⟨δ₀, hδ₀, hev⟩ := exists_eventually_measureReal_finalSize_lt_le h h2 hm' hN hS
      (by linarith : 0 < (b - extinctionProb ν) / 3)
    set ε := min δ₀ (τ - δ)
    have hε : 0 < ε := lt_min hδ₀ (by linarith)
    have hfar := tendsto_measureReal_finalSize_far h h2 hm' hN hS hε
    filter_upwards [hev, hfar.eventually (gt_mem_nhds (by linarith :
      (0 : ℝ) < (b - extinctionProb ν) / 3)), hNr.eventually_gt_atTop 0] with k hk1 hk2 hk3
    have := (h k).isProbabilityMeasure
    refine lt_of_le_of_lt ((measureReal_mono (s₂ :=
      {ω | (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) < δ₀ * N k} ∪
      {ω | ε ≤ (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) / N k ∧
        ε ≤ |(finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) / N k - τ|}) ?_
        (measure_ne_top _ _)).trans (measureReal_union_le _ _)) (by linarith)
    intro ω (hω : _ < δ)
    by_cases hx : (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) / N k < ε
    · left
      change _ < δ₀ * N k
      rw [← div_lt_iff₀ hk3]
      exact lt_of_lt_of_le hx (min_le_left _ _)
    · right
      push Not at hx
      refine ⟨hx, ?_⟩
      rw [abs_sub_comm, abs_of_pos (by linarith)]
      have := min_le_right δ₀ (τ - δ)
      linarith

/-- **Final size: major outbreaks.** For `R₀ = mean ν > 1` (finite variance), in the
large-population limit the probability that the fraction of the population ultimately infected
is within `δ` of the non-zero root `τ` of the final-size equation `1 - τ = e^{-R₀ τ}` converges
to the survival probability `1 - q` of the branching process (`0 < δ < τ`). Together with
`tendsto_measureReal_finalSize_div_lt`, the fraction ultimately infected converges in law to
`q δ₀ + (1 - q) δ_τ`. -/
theorem tendsto_measureReal_abs_finalSize_div_sub_lt
    (h : ∀ k, IsFinalSizeEpidemic (P k) ν (N k) (ξ k) (U k))
    (h2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) ν) (hm : 1 < mean ν)
    (hN : Tendsto N atTop atTop)
    (hS : Tendsto (fun k => ((N k - (S₀ k).card : ℕ) : ℝ) / N k) atTop (𝓝 0)) {δ : ℝ}
    (hδ : 0 < δ) (hδτ : δ < finalSizeRoot (mean ν).toReal) :
    Tendsto (fun k => (P k).real
      {ω | |(finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) / N k -
        finalSizeRoot (mean ν).toReal| < δ}) atTop (𝓝 (1 - extinctionProb ν)) := by
  have hm' := one_lt_offspringMean h2 hm
  have hτ := hδτ
  rw [← offspringMean_eq_toReal_mean h2] at hτ ⊢
  set τ := finalSizeRoot (offspringMean ν)
  have hlow := tendsto_measureReal_finalSize_div_lt h h2 hm hN hS hδ hδτ
  have hhigh := tendsto_measureReal_finalSize_div_lt h h2 hm hN hS (δ := τ - δ) (by linarith)
    (by rw [← offspringMean_eq_toReal_mean h2]; linarith)
  have hfar := tendsto_measureReal_finalSize_far h h2 hm' hN hS hδ
  have hL : Tendsto (fun k => 1 -
      (P k).real {ω | (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) / N k < δ} -
      (P k).real {ω | δ ≤ (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) / N k ∧
        δ ≤ |(finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) / N k - τ|}) atTop
      (𝓝 (1 - extinctionProb ν)) := by
    simpa using (tendsto_const_nhds.sub hlow).sub hfar
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hL (tendsto_const_nhds.sub hhigh) ?_ ?_
  · intro k
    have := (h k).isProbabilityMeasure
    set x : Ω k → ℝ := fun ω => (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) / N k
    have hcov : Set.univ ⊆ ({ω | |x ω - τ| < δ} ∪ {ω | x ω < δ}) ∪
        {ω | δ ≤ x ω ∧ δ ≤ |x ω - τ|} := by
      intro ω _
      by_cases h1 : |x ω - τ| < δ
      · exact Or.inl (Or.inl h1)
      · by_cases h2 : x ω < δ
        · exact Or.inl (Or.inr h2)
        · push Not at h1 h2; exact Or.inr ⟨h2, h1⟩
    have := (measureReal_mono (μ := P k) hcov (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl))
    rw [probReal_univ] at this
    simp only [x] at this
    dsimp only
    linarith
  · intro k
    have := (h k).isProbabilityMeasure
    have hmeas : Measurable fun ω => (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) / N k :=
      (measurable_of_countable fun F : ℕ => (F : ℝ) / N k).comp ((h k).measurable_finalSize (S₀ k))
    have hdisj : Disjoint
        {ω | |(finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) / N k - τ| < δ}
        {ω | (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) / N k < τ - δ} :=
      Set.disjoint_left.2 fun ω h1 h2 => by
        simp only [Set.mem_ofPred_eq] at h1 h2
        have := (abs_lt.1 h1).1
        linarith
    have hU := measureReal_union (μ := P k) hdisj (measurableSet_lt hmeas measurable_const)
      (measure_ne_top _ _) (measure_ne_top _ _)
    have h1 := measureReal_le_one (μ := P k) (s :=
      {ω | |(finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) / N k - τ| < δ} ∪
        {ω | (finalSize (ξ k · · ω) (U k · ω) (S₀ k) : ℝ) / N k < τ - δ})
    dsimp only
    linarith

end LargePopulation

end MathlibExt.Biology.Epidemiology.EarlyEpidemicFinalSize
