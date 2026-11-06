/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RandomWalkLimsup
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
import MathlibExt.Probability.HewittSavage
import Mathlib.Probability.Independence.InfinitePi

/-!
# Random-walk dichotomy

Let `X₁, X₂, …` be i.i.d. real-valued random variables and
`Sₙ = X₁ + ⋯ + Xₙ`. Almost surely, exactly one of the following occurs:
`Sₙ = 0` for every `n` (the degenerate case `Xᵢ ≡ 0`),
`Sₙ → +∞`, `Sₙ → -∞`, or `liminf Sₙ = -∞` and `limsup Sₙ = +∞`
(the walk oscillates).

## Proof outline

The proof goes through the canonical sequence space `(ℕ → ℝ)` with the
i.i.d. product measure, where the Hewitt–Savage 0–1 law (already in
`MathlibExt.Probability.HewittSavage`) applies to the permutation-invariant
events built from `limsup Sₙ` and `liminf Sₙ`:

* `limsup Sₙ` and `liminf Sₙ` are invariant under finitely supported
  permutations of the coordinates (because a finite permutation does not
  change the tail of the partial sums), so the events
  `{limsup Sₙ < +∞}` and `{liminf Sₙ > -∞}` each have probability `0` or `1`.
* If both probabilities are `1`, the walk is a.s. bounded, so `limsup Sₙ`
  is a.s. equal to a finite constant `u` (a general 0–1 criterion for
  `EReal`-valued variables). The one-step shift identity
  `limsup Sₙ = X₀ + limsup Sₙ ∘ shift` plus shift-invariance of the product
  measure then forces `X₀ = 0` a.s., hence every `Xᵢ = 0` a.s., and the walk
  is zero at every time.
* If `{limsup Sₙ < +∞}` has probability `1` and `{liminf Sₙ > -∞}` has
  probability `0`, the a.s. constant `u = limsup Sₙ` is either `-∞`
  (the walk drifts to `-∞`) or finite (which forces `X₀ = 0` a.s. as
  above, contradicting `liminf Sₙ = -∞` a.s.). The symmetric case gives
  drift to `+∞`, and if both probabilities are `0` the walk oscillates.
* The general case follows by pushing the i.i.d. sequence forward to
  sequence space: the joint law of an i.i.d. sequence is the product
  measure (`iIndepFun.map_fun_eq_infinitePi_map₀'`), so each of the four
  a.s. properties transfers back along the sequence map.

## Source

This proves the target "Theorem (Random walk dichotomy)" (Lecture 23) in
`v1/Atlas/TheoryOfProbability/targets.yaml`, including its all-times zero-walk
alternative. The finite-convergence form used by the v1 formalization is a
separate corollary here. The v1 formalization is
`v1/Atlas/TheoryOfProbability/code/RandomWalkDichotomyProof.lean`, whose
covering lemma `randomWalk_events_cover_ae` is left unproved there; the
proof here is new. The tail-measurability of the four events is Batch 25
(`MathlibExt.Probability.RandomWalkTailMeasurability`); this file proves
the dichotomy itself, which Batch 25 explicitly left out.

## Scope

In: the four-way dichotomy for i.i.d. real random walks, on a general
probability space.

Out: the classification of *which* alternative occurs for a given law
(e.g. in terms of `E X₁` or the SLLN); the random-walk dichotomy for
`ℤᵈ`-valued walks; the Hewitt–Savage 0–1 law itself (already in
`MathlibExt.Probability.HewittSavage`).
-/

@[expose] public section

open MeasureTheory Filter Topology ProbabilityTheory
open MathlibExt.Probability.RandomWalkTailMeasurability (randomWalkPartialSum)

namespace MathlibExt.Probability.RandomWalkDichotomy

/-- **Zero random walk.** Let $\mu$ be a probability measure on a measurable space $\Omega$, let
$X_0, X_1, \ldots$ be real-valued functions on $\Omega$, and let $S_n = \sum_{i < n} X_i$ be the
partial sums of the random walk. The walk is a zero walk when, for $\mu$-almost every
$\omega \in \Omega$, we have $S_n(\omega) = 0$ for every $n \in \mathbb{N}$. -/
def ZeroWalk {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, ∀ n, randomWalkPartialSum X n ω = 0

/-- **Random walk drifting to $+\infty$.** Let $X_0, X_1, \dots$ be real random variables on a
probability space $(\Omega, \mu)$ and $S_n = \sum_{i < n} X_i$. The random walk $(S_n)$ drifts
to $+\infty$ if for $\mu$-almost every $\omega$, $S_n(\omega) \to +\infty$ as $n \to \infty$. -/
def DriftsToTop {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n => randomWalkPartialSum X n ω) Filter.atTop Filter.atTop

/-- **Random walk drifting to $-\infty$.** Let $X_0, X_1, \dots$ be real random variables on a
probability space $(\Omega, \mu)$ and $S_n = \sum_{i < n} X_i$. The random walk $(S_n)$ drifts
to $-\infty$ if for $\mu$-almost every $\omega$, $S_n(\omega) \to -\infty$ as $n \to \infty$. -/
def DriftsToBot {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n => randomWalkPartialSum X n ω) Filter.atTop Filter.atBot

/-- **Oscillating random walk.** Let $X_0, X_1, \dots$ be real random variables on a probability
space $(\Omega, \mu)$ and $S_n = \sum_{i < n} X_i$. The random walk $(S_n)$ oscillates if for
$\mu$-almost every $\omega$, $\limsup_n S_n(\omega) = +\infty$ and
$\liminf_n S_n(\omega) = -\infty$, the limits taken in the extended reals. -/
def Oscillates {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, randomWalkLimsup X ω = ⊤ ∧ randomWalkLiminf X ω = ⊥

/-- **Random walk with a finite limit.** Let $X_0, X_1, \dots$ be real random variables on a
probability space $(\Omega, \mu)$ and $S_n = \sum_{i < n} X_i$. The random walk $(S_n)$
converges to a finite limit if for $\mu$-almost every $\omega$ there is $l \in \mathbb{R}$ with
$S_n(\omega) \to l$ as $n \to \infty$.

The limit may depend on $\omega$; the zero-walk alternative of the i.i.d. random-walk dichotomy
implies this property. -/
def ConvergesFinite {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, ∃ l : ℝ, Tendsto (fun n => randomWalkPartialSum X n ω) Filter.atTop
    (𝓝 l)

/-- **A random walk is zero exactly when its steps are.** Let $X_0, X_1, \dots$ be real random
variables on a probability space and $S_n = \sum_{i < n} X_i$. Then almost surely $S_n = 0$ for
every $n$ if and only if almost surely $X_i = 0$ for every $i$. -/
theorem zeroWalk_iff_ae_forall_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} :
    ZeroWalk μ X ↔ ∀ᵐ ω ∂μ, ∀ i, X i ω = 0 := by
  constructor
  · intro h
    filter_upwards [h] with ω hω i
    have hs := partialSum_succ X i ω
    rw [hω (i + 1), hω i, zero_add] at hs
    exact hs.symm
  · intro h
    filter_upwards [h] with ω hω n
    exact Finset.sum_eq_zero fun i _ => hω i

/-- **A zero walk converges to a finite limit.** Let $X_0, X_1, \dots$ be real random
variables on a probability space and $S_n = \sum_{i < n} X_i$. If almost surely $S_n = 0$ for
every $n$, then almost surely there is $l \in \mathbb{R}$ with $S_n \to l$ as $n \to \infty$. -/
theorem ZeroWalk.convergesFinite {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (h : ZeroWalk μ X) : ConvergesFinite μ X :=
  convergesFinite_of_ae_forall_eq_zero (zeroWalk_iff_ae_forall_eq_zero.mp h)

/-- A set of full measure is almost surely inhabited: from `μ E = 1`,
every `ω` lies in `E` almost surely. -/
private theorem ae_mem_of_measure_eq_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {E : Set Ω} (hm : MeasurableSet E)
    (h : μ E = 1) : ∀ᵐ ω ∂μ, ω ∈ E := by
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨E, ?_, fun ω hω => hω⟩
  rw [mem_ae_iff]
  have hcompl : μ Eᶜ = μ Set.univ - μ E := measure_compl hm (μ := μ) (measure_ne_top _ _)
  rw [h, measure_univ] at hcompl
  simpa using hcompl

/-- A null set is almost surely avoided. -/
private theorem ae_not_mem_of_measure_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {E : Set Ω} (h : μ E = 0) :
    ∀ᵐ ω ∂μ, ω ∉ E := by
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Eᶜ, ?_, fun ω hω => hω⟩
  rw [mem_ae_iff, compl_compl]
  exact h

/-- A set containing almost every point has measure `1`. -/
private theorem measure_eq_one_of_ae_mem {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {E : Set Ω} (hm : MeasurableSet E)
    (h : ∀ᵐ ω ∂μ, ω ∈ E) : μ E = 1 := by
  have h0 : μ Eᶜ = 0 := by
    have h' : μ {ω | ω ∉ E} = 0 := ae_iff.mp h
    exact h'
  have hcompl : μ Eᶜ = μ Set.univ - μ E := measure_compl hm (μ := μ) (measure_ne_top _ _)
  rw [h0, measure_univ] at hcompl
  have hle : (1 : ENNReal) ≤ μ E := tsub_eq_zero_iff_le.mp hcompl.symm
  exact le_antisymm prob_le_one hle

/-- The marginal of one coordinate of the i.i.d. product measure. -/
private theorem infinitePi_marginal (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (i : ℕ)
    (s : Set ℝ) (hs : MeasurableSet s) :
    Measure.infinitePi (fun _ : ℕ => ρ) {ω : ℕ → ℝ | ω i ∈ s} = ρ s := by
  have hset : {ω : ℕ → ℝ | ω i ∈ s} =
      Set.pi (↑({i} : Finset ℕ)) (fun j => if j = i then s else Set.univ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_singleton]
    constructor
    · intro h j hj
      rw [hj]
      simpa using h
    · intro h
      have hi := h i rfl
      simpa using hi
  rw [hset, Measure.infinitePi_pi]
  · simp
  · intro j hj
    simp only [Finset.mem_singleton] at hj
    rw [hj, ite_eq_left rfl]
    exact hs

/-- If `F : (ℕ → ℝ) → EReal` is a.s. equal to a finite constant `c` and
satisfies the shift identity `F ω = ω 0 + F (shift ω)`, then the `0`-th
coordinate vanishes a.s. (the same holds for `limsup` and `liminf` of the
partial sums). -/
private theorem ae_coord_eq_zero_of_const {F : (ℕ → ℝ) → EReal} {c : EReal}
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hF_meas : Measurable F)
    (hF_shift : ∀ ω, F ω = (ω 0 : EReal) + F (shiftSeq ω))
    (hconst : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => ρ), F ω = c)
    (hc_top : c ≠ ⊤) (hc_bot : c ≠ ⊥) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => ρ), ω 0 = 0 := by
  classical
  set ν : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => ρ) with hν
  have hmeas_shift : Measurable shiftSeq :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (i + 1)
  -- The shifted variable is a.s. equal to the same constant.
  have hF_shift_ae : ∀ᵐ ω ∂ν, F (shiftSeq ω) = c := by
    have hmeas : MeasurableSet {ω | F ω = c} := hF_meas (measurableSet_singleton c)
    have h1 : ν (shiftSeq ⁻¹' {ω | F ω = c}) = 1 := by
      rw [← MeasureTheory.Measure.map_apply hmeas_shift hmeas,
        map_shiftSeq_infinitePi]
      exact measure_eq_one_of_ae_mem hmeas hconst
    exact ae_mem_of_measure_eq_one (MeasurableSet.preimage hmeas hmeas_shift) h1
  obtain ⟨r, hr⟩ : ∃ r : ℝ, c = (r : EReal) :=
    ⟨c.toReal, (EReal.coe_toReal hc_top hc_bot).symm⟩
  filter_upwards [hconst, hF_shift_ae, Filter.Eventually.of_forall hF_shift] with ω h1 h2 h3
  rw [h1, h2, hr] at h3
  have h4 : ω 0 + r = r := by
    have hto := congrArg EReal.toReal h3
    have hto' : r = ω 0 + r := by
      simpa only [← EReal.coe_add, EReal.toReal_coe] using hto
    exact hto'.symm
  linarith

/-- If the `0`-th coordinate vanishes a.s., then every coordinate vanishes a.s.
(they all have the same law). -/
private theorem ae_all_coords_eq_zero_of_ae_coord_zero (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ]
    (h0 : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => ρ), ω 0 = 0) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => ρ), ∀ i, ω i = 0 := by
  rw [ae_all_iff]
  intro i
  have h1 : Measure.infinitePi (fun _ : ℕ => ρ) {ω : ℕ → ℝ | ω i = 0} = ρ {0} :=
    infinitePi_marginal ρ i {0} (measurableSet_singleton 0)
  have h2 : Measure.infinitePi (fun _ : ℕ => ρ) {ω : ℕ → ℝ | ω 0 = 0} = ρ {0} :=
    infinitePi_marginal ρ 0 {0} (measurableSet_singleton 0)
  have h3 : Measure.infinitePi (fun _ : ℕ => ρ) {ω : ℕ → ℝ | ω 0 = 0} = 1 :=
    measure_eq_one_of_ae_mem (measurable_pi_apply 0 (measurableSet_singleton 0)) h0
  exact ae_mem_of_measure_eq_one (measurable_pi_apply i (measurableSet_singleton 0))
    (h1.trans (h2.symm.trans h3))

/-- **Random-walk dichotomy on sequence space.** Let $\rho$ be a probability measure on
$\mathbb{R}$, let $\nu = \rho^{\otimes \mathbb{N}}$ be the product measure on
$\mathbb{R}^{\mathbb{N}}$, and let $S_n(\omega) = \sum_{i < n} \omega_i$ be the partial sums of
the coordinates. Then one of the following holds: $\nu$-almost surely $S_n = 0$ for every $n$;
$\nu$-almost surely $S_n \to +\infty$; $\nu$-almost surely $S_n \to -\infty$; or $\nu$-almost
surely $\limsup_n S_n = +\infty$ and $\liminf_n S_n = -\infty$. -/
theorem dichotomy_product_zero (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    ZeroWalk (Measure.infinitePi (fun _ : ℕ => ρ)) coordSeq ∨
    DriftsToTop (Measure.infinitePi (fun _ : ℕ => ρ)) coordSeq ∨
    DriftsToBot (Measure.infinitePi (fun _ : ℕ => ρ)) coordSeq ∨
    Oscillates (Measure.infinitePi (fun _ : ℕ => ρ)) coordSeq := by
  classical
  set ν : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => ρ) with hν
  have hU_meas : Measurable (randomWalkLimsup coordSeq) :=
    measurable_randomWalkLimsup coordSeq (fun i => measurable_pi_apply i)
  have hL_meas : Measurable (randomWalkLiminf coordSeq) :=
    measurable_randomWalkLiminf coordSeq (fun i => measurable_pi_apply i)
  have hmeas_shift : Measurable shiftSeq :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (i + 1)
  -- 0–1 laws for the level sets, from Hewitt–Savage.
  have h01 : ∀ (F : (ℕ → ℝ) → EReal) (hF : Measurable F),
      (∀ σ : Equiv.Perm ℕ, Set.Finite {n : ℕ | σ n ≠ n} →
        ∀ ω, F (ω ∘ ⇑σ) = F ω) →
      ∀ a : ℝ, ν {ω | F ω ≤ (a : EReal)} = 0 ∨ ν {ω | F ω ≤ (a : EReal)} = 1 := by
    intro F hF hFperm a
    apply MathlibExt.Probability.HewittSavageWanted.hewitt_savage_zero_one ρ
      {ω | F ω ≤ (a : EReal)} (hF measurableSet_Iic)
    intro σ hσ
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [hFperm σ hσ]
  have h01U : ∀ a : ℝ, ν {ω | randomWalkLimsup coordSeq ω ≤ (a : EReal)} = 0 ∨
      ν {ω | randomWalkLimsup coordSeq ω ≤ (a : EReal)} = 1 :=
    h01 _ hU_meas (fun σ hσ ω => limsup_comp_perm hσ ω)
  have h01L : ∀ a : ℝ, ν {ω | randomWalkLiminf coordSeq ω ≤ (a : EReal)} = 0 ∨
      ν {ω | randomWalkLiminf coordSeq ω ≤ (a : EReal)} = 1 :=
    h01 _ hL_meas (fun σ hσ ω => liminf_comp_perm hσ ω)
  have h01_top : ν {ω | randomWalkLimsup coordSeq ω < ⊤} = 0 ∨
      ν {ω | randomWalkLimsup coordSeq ω < ⊤} = 1 := by
    refine MathlibExt.Probability.HewittSavageWanted.hewitt_savage_zero_one ρ
      {ω | randomWalkLimsup coordSeq ω < ⊤} (hU_meas measurableSet_Iio) ?_
    intro σ hσ
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [limsup_comp_perm hσ ω]
  have h01_bot : ν {ω | randomWalkLiminf coordSeq ω > ⊥} = 0 ∨
      ν {ω | randomWalkLiminf coordSeq ω > ⊥} = 1 := by
    refine MathlibExt.Probability.HewittSavageWanted.hewitt_savage_zero_one ρ
      {ω | randomWalkLiminf coordSeq ω > ⊥} (hL_meas measurableSet_Ioi) ?_
    intro σ hσ
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [liminf_comp_perm hσ ω]
  -- The 0–1 law for `{limsup Sₙ < +∞}` and `{liminf Sₙ > -∞}`.
  rcases h01_top with htop0 | htop1 <;> rcases h01_bot with hbot0 | hbot1
  · -- Both `0`: the walk oscillates.
    right; right; right
    have hU : ∀ᵐ ω ∂ν, randomWalkLimsup coordSeq ω = ⊤ := by
      have hae := ae_not_mem_of_measure_eq_zero htop0
      filter_upwards [hae] with ω hω
      exact le_antisymm le_top (le_of_not_gt hω)
    have hL : ∀ᵐ ω ∂ν, randomWalkLiminf coordSeq ω = ⊥ := by
      have hae := ae_not_mem_of_measure_eq_zero hbot0
      filter_upwards [hae] with ω hω
      exact le_antisymm (le_of_not_gt hω) bot_le
    filter_upwards [hU, hL] with ω hUω hLω
    exact ⟨hUω, hLω⟩
  · -- `limsup < +∞` fails, `liminf > -∞` holds: drift to `+∞`.
    right; left
    -- `U = ⊤` a.s.
    have hU : ∀ᵐ ω ∂ν, randomWalkLimsup coordSeq ω = ⊤ := by
      have hae := ae_not_mem_of_measure_eq_zero htop0
      filter_upwards [hae] with ω hω
      exact le_antisymm le_top (le_of_not_gt hω)
    -- `L > ⊥` a.s.
    have hLgt : ∀ᵐ ω ∂ν, randomWalkLiminf coordSeq ω > ⊥ :=
      ae_mem_of_measure_eq_one (hL_meas measurableSet_Ioi) hbot1
    -- `L` is a.s. a constant `l > ⊥`.
    obtain ⟨l, hl⟩ := exists_ae_eq_const_of_forall_le_zero_or_one hL_meas h01L
    have hl_gt : l > ⊥ := by
      by_contra hcon
      push Not at hcon
      obtain ⟨ω, h1, h2⟩ := (hl.and hLgt).exists
      rw [h1] at h2
      exact absurd h2 (not_lt_of_ge hcon)
    by_cases hl_top : l = ⊤
    · -- `L = ⊤` a.s.: drift to `+∞`.
      filter_upwards [hl] with ω hω
      rw [hl_top] at hω
      exact tendsto_atTop_of_liminf_eq_top hω
    · -- `l` is finite: then `X₀ = 0` a.s., so `U = 0` a.s., contradiction.
      exfalso
      have h0 : ∀ᵐ ω ∂ν, ω 0 = 0 :=
        ae_coord_eq_zero_of_const ρ hL_meas liminf_shift hl
          (by exact hl_top) (by exact (ne_of_gt hl_gt))
      have hall : ∀ᵐ ω ∂ν, ∀ i, ω i = 0 :=
        ae_all_coords_eq_zero_of_ae_coord_zero ρ h0
      have hU0 : ∀ᵐ ω ∂ν, randomWalkLimsup coordSeq ω = 0 := by
        filter_upwards [hall] with ω hω
        have hsum : ∀ n, randomWalkPartialSum coordSeq n ω = 0 := by
          intro n
          simp only [randomWalkPartialSum, coordSeq]
          exact Finset.sum_eq_zero fun i _ => hω i
        have : (fun n => ((randomWalkPartialSum coordSeq n ω : ℝ) : EReal)) =
            fun _ => (0 : EReal) := by
          funext n
          rw [hsum n]
          simp
        rw [randomWalkLimsup, this]
        exact Filter.limsup_const (0 : EReal)
      obtain ⟨ω, h1, h2⟩ := (hU0.and hU).exists
      rw [h1] at h2
      exact absurd h2 (by simp)
  · -- `limsup < +∞` holds, `liminf > -∞` fails: drift to `-∞`.
    right; right; left
    -- `L = ⊥` a.s.
    have hL : ∀ᵐ ω ∂ν, randomWalkLiminf coordSeq ω = ⊥ := by
      have hae := ae_not_mem_of_measure_eq_zero hbot0
      filter_upwards [hae] with ω hω
      exact le_antisymm (le_of_not_gt hω) bot_le
    -- `U < ⊤` a.s.
    have hUlt : ∀ᵐ ω ∂ν, randomWalkLimsup coordSeq ω < ⊤ :=
      ae_mem_of_measure_eq_one (hU_meas measurableSet_Iio) htop1
    -- `U` is a.s. a constant `u < ⊤`.
    obtain ⟨u, hu⟩ := exists_ae_eq_const_of_forall_le_zero_or_one hU_meas h01U
    have hu_lt : u < ⊤ := by
      by_contra hcon
      push Not at hcon
      obtain ⟨ω, h1, h2⟩ := (hu.and hUlt).exists
      rw [h1] at h2
      exact absurd h2 (not_lt_of_ge hcon)
    by_cases hu_bot : u = ⊥
    · -- `U = ⊥` a.s.: drift to `-∞`.
      filter_upwards [hu] with ω hω
      rw [hu_bot] at hω
      exact tendsto_atBot_of_limsup_eq_bot hω
    · -- `u` is finite: then `X₀ = 0` a.s., so `L = 0` a.s., contradiction.
      exfalso
      have h0 : ∀ᵐ ω ∂ν, ω 0 = 0 :=
        ae_coord_eq_zero_of_const ρ hU_meas limsup_shift hu (ne_of_lt hu_lt) hu_bot
      have hall : ∀ᵐ ω ∂ν, ∀ i, ω i = 0 :=
        ae_all_coords_eq_zero_of_ae_coord_zero ρ h0
      have hL0 : ∀ᵐ ω ∂ν, randomWalkLiminf coordSeq ω = 0 := by
        filter_upwards [hall] with ω hω
        have hsum : ∀ n, randomWalkPartialSum coordSeq n ω = 0 := by
          intro n
          simp only [randomWalkPartialSum, coordSeq]
          exact Finset.sum_eq_zero fun i _ => hω i
        have : (fun n => ((randomWalkPartialSum coordSeq n ω : ℝ) : EReal)) =
            fun _ => (0 : EReal) := by
          funext n
          rw [hsum n]
          simp
        rw [randomWalkLiminf, this]
        exact Filter.liminf_const (0 : EReal)
      obtain ⟨ω, h1, h2⟩ := (hL0.and hL).exists
      rw [h1] at h2
      exact absurd h2 (by simp)
  · -- Both `1`: the walk is a.s. bounded, hence a.s. constant finite
    -- `limsup`, hence `X₀ = 0` a.s., hence the walk is zero at every time.
    left
    -- `U < ⊤` a.s. and `L > ⊥` a.s.
    have hUlt : ∀ᵐ ω ∂ν, randomWalkLimsup coordSeq ω < ⊤ :=
      ae_mem_of_measure_eq_one (hU_meas measurableSet_Iio) htop1
    have hLgt : ∀ᵐ ω ∂ν, randomWalkLiminf coordSeq ω > ⊥ :=
      ae_mem_of_measure_eq_one (hL_meas measurableSet_Ioi) hbot1
    -- `U` is a.s. a finite constant `u`.
    obtain ⟨u, hu⟩ := exists_ae_eq_const_of_forall_le_zero_or_one hU_meas h01U
    have hu_lt : u < ⊤ := by
      by_contra hcon
      push Not at hcon
      obtain ⟨ω, h1, h2⟩ := (hu.and hUlt).exists
      rw [h1] at h2
      exact absurd h2 (not_lt_of_ge hcon)
    have hu_gt : u > ⊥ := by
      obtain ⟨ω, h1, h2⟩ := (hu.and hLgt).exists
      rw [← h1]
      exact lt_of_lt_of_le h2 (Filter.liminf_le_limsup)
    have h0 : ∀ᵐ ω ∂ν, ω 0 = 0 :=
      ae_coord_eq_zero_of_const ρ hU_meas limsup_shift hu (ne_of_lt hu_lt)
        (ne_of_gt hu_gt)
    have hall : ∀ᵐ ω ∂ν, ∀ i, ω i = 0 :=
      ae_all_coords_eq_zero_of_ae_coord_zero ρ h0
    exact zeroWalk_iff_ae_forall_eq_zero.mpr hall

/-- **Random-walk dichotomy on sequence space, finite-limit form.** Let $\rho$ be a probability
measure on $\mathbb{R}$, let $\nu = \rho^{\otimes \mathbb{N}}$ be the product measure on
$\mathbb{R}^{\mathbb{N}}$, and let $S_n(\omega) = \sum_{i < n} \omega_i$ be the partial sums of
the coordinates. Then one of the following holds: $\nu$-almost surely $S_n$ converges to a
finite limit (which may depend on $\omega$); $\nu$-almost surely $S_n \to +\infty$;
$\nu$-almost surely $S_n \to -\infty$; or $\nu$-almost surely $\limsup_n S_n = +\infty$ and
$\liminf_n S_n = -\infty$. -/
theorem dichotomy_product (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    ConvergesFinite (Measure.infinitePi (fun _ : ℕ => ρ)) coordSeq ∨
    DriftsToTop (Measure.infinitePi (fun _ : ℕ => ρ)) coordSeq ∨
    DriftsToBot (Measure.infinitePi (fun _ : ℕ => ρ)) coordSeq ∨
    Oscillates (Measure.infinitePi (fun _ : ℕ => ρ)) coordSeq :=
  Or.imp_left ZeroWalk.convergesFinite (dichotomy_product_zero ρ)

/-- **Random-walk dichotomy.** Let $X_0, X_1, \dots$ be independent, identically distributed
real random variables on a probability space and $S_n = \sum_{i < n} X_i$. Then one of the
following events has probability one: $S_n = 0$ for every $n$; $S_n \to +\infty$;
$S_n \to -\infty$; or $\limsup_n S_n = +\infty$ and $\liminf_n S_n = -\infty$. -/
theorem random_walk_dichotomy_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ZeroWalk μ X ∨ DriftsToTop μ X ∨ DriftsToBot μ X ∨ Oscillates μ X := by
  have hXae : ∀ i, AEMeasurable (X i) μ := fun i => (hident i).aemeasurable_fst
  set Φ : Ω → (ℕ → ℝ) := fun ω i => X i ω with hΦ
  have hΦae : AEMeasurable Φ μ := aemeasurable_pi_iff.mpr hXae
  have hmap : μ.map Φ = Measure.infinitePi (fun _ : ℕ => μ.map (X 0)) := by
    have h1 := iIndepFun.map_fun_eq_infinitePi_map₀' hXae hindep
    rw [h1]
    congr 1
    funext i
    exact (hident i).map_eq
  -- Transfer each disjunct along the sequence map `Φ`.
  have htransfer : ∀ {E : Set (ℕ → ℝ)} (hE : MeasurableSet E),
      (∀ᵐ ω' ∂Measure.infinitePi (fun _ : ℕ => μ.map (X 0)), ω' ∈ E) →
      ∀ᵐ ω ∂μ, Φ ω ∈ E := by
    intro E hE h
    have h' : ∀ᵐ ω' ∂μ.map Φ, ω' ∈ E := by
      rwa [← hmap] at h
    exact (ae_map_iff hΦae hE).mp h'
  rcases dichotomy_product_zero (μ.map (X 0)) with h | h | h | h
  · left
    have hE := htransfer measurableSet_coord_forall_eq_zero
      (zeroWalk_iff_ae_forall_eq_zero.mp h)
    exact zeroWalk_iff_ae_forall_eq_zero.mpr hE
  · right; left
    have hE := htransfer measurableSet_coord_driftsToTop h
    filter_upwards [hE] with ω hω
    exact hω
  · right; right; left
    have hE := htransfer measurableSet_coord_driftsToBot h
    filter_upwards [hE] with ω hω
    exact hω
  · right; right; right
    have hE := htransfer
      (MeasurableSet.inter
        ((measurable_randomWalkLimsup coordSeq (fun i => measurable_pi_apply i))
          (measurableSet_singleton ⊤))
        ((measurable_randomWalkLiminf coordSeq (fun i => measurable_pi_apply i))
          (measurableSet_singleton ⊥))) h
    filter_upwards [hE] with ω hω
    exact hω

/-- **Random-walk dichotomy, finite-limit form.** Let $X_0, X_1, \dots$ be independent,
identically distributed real random variables on a probability space and
$S_n = \sum_{i < n} X_i$. Then one of the following events has probability one: $S_n$
converges to a finite limit (which may depend on the outcome); $S_n \to +\infty$;
$S_n \to -\infty$; or $\limsup_n S_n = +\infty$ and $\liminf_n S_n = -\infty$. -/
theorem random_walk_dichotomy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ConvergesFinite μ X ∨ DriftsToTop μ X ∨ DriftsToBot μ X ∨ Oscillates μ X :=
  Or.imp_left ZeroWalk.convergesFinite (random_walk_dichotomy_zero μ X hindep hident)

end MathlibExt.Probability.RandomWalkDichotomy
