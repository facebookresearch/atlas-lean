/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Renewal.ScoreLadder
public import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Independence.Integration

/-!
# The ladder Cramér identity for an i.i.d. integer score walk

Let `X` be i.i.d. integer scores with walk `S n = X 0 + ⋯ + X (n - 1)`, first strict ascending
ladder epoch `τ₊`, and (defective) ladder-height law `g j = P(τ₊ < ∞, S_{τ₊} = j)`
(`ladderLaw`). If `θ > 0` is a root of the moment generating function equation
`𝔼 e^{θ X} = 1` and `X` is not almost surely `0`, then

`∑ j, g j e^{θ j} = 1`  (`hasSum_ladderLaw_mul_exp`).

This is the identity that `tendsto_exp_mul_maxTail_scoreWalk` (in `ScoreLadder`) takes as its
hypothesis `hcramer`; `tendsto_exp_mul_maxTail_scoreWalk_of_mgf` discharges it, so the
Cramér–Lundberg / Karlin–Dembo tail limit follows from the root `θ` of `𝔼 e^{θ X} = 1`.
`hasSum_ladderLaw_mul_exp_of_integral_neg` states the identity under the usual negative-drift
hypothesis `𝔼 X < 0`, which implies nondegeneracy.

## Proof

This is optional stopping of the martingale `e^{θ S_n}` at `τ₊ ∧ n`, carried out by hand:

* (Stopped identity, `stopped_identity`.) With `B n = {S_m ≤ 0 for all m ≤ n} = {τ₊ > n}`,
  `∑_{m ≤ n} 𝔼[e^{θ S_m}; τ₊ = m] + 𝔼[e^{θ S_n}; B n] = 1` for every `n`. The induction step
  uses only fixed-time independence: `1_{B n} e^{θ S_n}` depends on `X 0, …, X (n - 1)` and
  `𝔼 e^{θ X n} = 1`, so `𝔼[e^{θ S_{n+1}}; B n] = 𝔼[e^{θ S_n}; B n]`; then `B n` splits into
  `B (n + 1)` and the events `{τ₊ = n + 1, S_{n+1} = j}`, on which `e^{θ S_{n+1}} = e^{θ j}`.
* (The remainder vanishes.) On `B n`, `S_n ≤ 0`, so `e^{θ S_n} ≤ e^{(θ/2) S_n}` and
  `𝔼[e^{θ S_n}; B n] ≤ (𝔼 e^{(θ/2) X})^n`. By Cauchy–Schwarz in the form
  `𝔼 (e^{θ X / 2} - 1)^2 = 2 - 2 𝔼 e^{θ X / 2}`, nondegeneracy gives `𝔼 e^{θ X / 2} < 1`.
  No law of large numbers is needed.
* Letting `n → ∞` in the stopped identity gives `∑_j g j e^{θ j} = 1`.

## Relation to Mathlib and Atlas

The walk, the ladder events and the ladder law are `scoreWalk`, `ladderEvent` and `ladderLaw`
from `MathlibExt.Probability.Renewal.ScoreLadder`; the root is stated with Mathlib's
`ProbabilityTheory.mgf`. Mathlib's optional stopping
(`MeasureTheory.Submartingale.expected_stoppedValue_mono`) covers bounded stopping times such
as `τ₊ ∧ n`, but using it needs the natural filtration of the scores, the martingale property
of `e^{θ S_n}` and `τ₊ ∧ n` as a stopping time; the stopped identity is proved directly instead,
from fixed-time independence (`ProbabilityTheory.indep_iSup_of_disjoint` and
`lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace`). The passage
`n → ∞` (an unbounded stopping time) is not covered by Mathlib. The private σ-algebra
`walkPast` and the disjointness of ladder events are adapted from the private helpers `past`
and `ladderEvent_disjoint` of `ScoreLadder`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II, 2nd ed.,
  Chapter XII (ladder variables, the associated defective ladder law and Cramér's estimate).
* S. Karlin, A. Dembo, *Limit distributions of maximal segmental score among Markov-dependent
  partial sums*, Adv. Appl. Probab. 24 (1992), 113–140.
-/

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MathlibExt.Probability.Renewal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The event `{τ₊ > n}` that the score walk has not become strictly positive by time `n`:
`S m ≤ 0` for every `m ≤ n`. -/
private def notAscended (X : ℕ → Ω → ℤ) (n : ℕ) : Set Ω :=
  {ω | ∀ m ≤ n, scoreWalk X m ω ≤ 0}

/-- The σ-algebra of the scores before time `n`. -/
private noncomputable abbrev walkPast (X : ℕ → Ω → ℤ) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ i ∈ Set.Iio n, MeasurableSpace.comap (X i) (inferInstance : MeasurableSpace ℤ)

private lemma walkPast_le {X : ℕ → Ω → ℤ} (hmeas : ∀ i, Measurable (X i)) (n : ℕ) :
    walkPast X n ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun i _ => (hmeas i).comap_le

omit [MeasurableSpace Ω] in
private lemma measurable_scoreWalk_walkPast (X : ℕ → Ω → ℤ) {m n : ℕ} (hmn : m ≤ n) :
    Measurable[walkPast X n] (scoreWalk X m) := by
  refine Finset.measurable_sum _ fun i hi => ?_
  have hi' : i ∈ Set.Iio n := by
    rw [Finset.mem_range] at hi
    exact Set.mem_Iio.2 (by omega)
  exact (comap_measurable (X i)).mono
    (le_biSup (fun i => MeasurableSpace.comap (X i) (inferInstance : MeasurableSpace ℤ)) hi')
    le_rfl

omit [MeasurableSpace Ω] in
private lemma measurableSet_notAscended_walkPast (X : ℕ → Ω → ℤ) (n : ℕ) :
    MeasurableSet[walkPast X n] (notAscended X n) := by
  have h : notAscended X n = ⋂ m, ⋂ (_ : m ≤ n), scoreWalk X m ⁻¹' {z | z ≤ 0} := by
    ext ω
    simp [notAscended]
  rw [h]
  exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun hm =>
    measurable_scoreWalk_walkPast X hm (MeasurableSet.of_discrete (s := {z : ℤ | z ≤ 0}))

private lemma measurable_scoreWalk {X : ℕ → Ω → ℤ} (hmeas : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (scoreWalk X n) :=
  (measurable_scoreWalk_walkPast X le_rfl).mono (walkPast_le hmeas n) le_rfl

private lemma measurableSet_ladderEvent {X : ℕ → Ω → ℤ} (hmeas : ∀ i, Measurable (X i))
    (n j : ℕ) : MeasurableSet (ladderEvent X n j) := by
  have h : ladderEvent X n j = scoreWalk X n ⁻¹' {z | 0 < z} ∩ scoreWalk X n ⁻¹' {z | z = j} ∩
      ⋂ m, ⋂ (_ : m < n), scoreWalk X m ⁻¹' {z | z ≤ 0} := by
    ext ω
    simp [ladderEvent, and_assoc]
  rw [h]
  exact ((measurable_scoreWalk hmeas n (MeasurableSet.of_discrete)).inter
    (measurable_scoreWalk hmeas n (MeasurableSet.of_discrete))).inter
    (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
      measurable_scoreWalk hmeas m (MeasurableSet.of_discrete))

omit [MeasurableSpace Ω] in
private lemma ladderEvent_disjoint_of_ne (X : ℕ → Ω → ℤ) {p q : ℕ × ℕ} (hpq : p ≠ q) :
    Disjoint (ladderEvent X p.1 p.2) (ladderEvent X q.1 q.2) := by
  rw [Set.disjoint_left]
  rintro ω ⟨hp1, hp2, hp3⟩ ⟨hq1, hq2, hq3⟩
  rcases lt_trichotomy p.1 q.1 with h | h | h
  · have := hq3 _ h
    omega
  · apply hpq
    refine Prod.ext h ?_
    rw [h] at hp2
    omega
  · have := hp3 _ h
    omega

/-- Fixed-time independence: a function of the scores before time `n` and a function of the
score at time `n` integrate as a product; the second factor has the law of `X 0`. -/
private lemma lintegral_mul_score {P : Measure Ω} {X : ℕ → Ω → ℤ}
    (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) (n : ℕ) {f : Ω → ℝ≥0∞}
    (hf : Measurable[walkPast X n] f) (h : ℤ → ℝ≥0∞) :
    ∫⁻ ω, f ω * h (X n ω) ∂P = (∫⁻ ω, f ω ∂P) * ∫⁻ ω, h (X 0 ω) ∂P := by
  have hdisj : Disjoint (Set.Iio n) ({n} : Set ℕ) := by simp
  have hindep := indep_iSup_of_disjoint (fun i => (hmeas i).comap_le) hind hdisj
  have hg : Measurable[⨆ i ∈ ({n} : Set ℕ),
      MeasurableSpace.comap (X i) (inferInstance : MeasurableSpace ℤ)] fun ω => h (X n ω) :=
    (measurable_from_top (f := h)).comp ((comap_measurable (X n)).mono
      (le_biSup (fun i => MeasurableSpace.comap (X i) (inferInstance : MeasurableSpace ℤ))
        (Set.mem_singleton n)) le_rfl)
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (walkPast_le hmeas n) (iSup₂_le fun i _ => (hmeas i).comap_le) hindep hf hg]
  congr 1
  exact ((hid n).comp (measurable_from_top (f := h))).lintegral_eq

omit [MeasurableSpace Ω] in
private lemma scoreWalk_succ (X : ℕ → Ω → ℤ) (n : ℕ) (ω : Ω) :
    scoreWalk X (n + 1) ω = scoreWalk X n ω + X n ω :=
  Finset.sum_range_succ _ n

omit [MeasurableSpace Ω] in
private lemma ofReal_exp_scoreWalk_succ (X : ℕ → Ω → ℤ) (t : ℝ) (n : ℕ) (ω : Ω) :
    ENNReal.ofReal (Real.exp (t * scoreWalk X (n + 1) ω)) =
      ENNReal.ofReal (Real.exp (t * scoreWalk X n ω)) * ENNReal.ofReal (Real.exp (t * X n ω)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, scoreWalk_succ]
  push_cast
  ring_nf

omit [MeasurableSpace Ω] in
private lemma measurable_ofReal_exp_walkPast (X : ℕ → Ω → ℤ) (t : ℝ) (n : ℕ) :
    Measurable[walkPast X n] fun ω => ENNReal.ofReal (Real.exp (t * scoreWalk X n ω)) :=
  (measurable_from_top (f := fun z : ℤ => ENNReal.ofReal (Real.exp (t * z)))).comp
    (measurable_scoreWalk_walkPast X le_rfl)

/-- `𝔼 e^{t S_n} = (𝔼 e^{t X})^n` for the i.i.d. score walk. -/
private lemma lintegral_exp_scoreWalk {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℤ} (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) (t : ℝ) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * scoreWalk X n ω)) ∂P =
      (∫⁻ ω, ENNReal.ofReal (Real.exp (t * X 0 ω)) ∂P) ^ n := by
  induction n with
  | zero => simp [scoreWalk]
  | succ n ih =>
    simp_rw [ofReal_exp_scoreWalk_succ]
    rw [lintegral_mul_score hmeas hind hid n (measurable_ofReal_exp_walkPast X t n)
      (fun z : ℤ => ENNReal.ofReal (Real.exp (t * z))), ih, pow_succ]

/-- The stopped identity `∑_{m ≤ n} 𝔼[e^{θ S_m}; τ₊ = m] + 𝔼[e^{θ S_n}; τ₊ > n] = 1`
(optional stopping of `e^{θ S_n}` at `τ₊ ∧ n`), given `𝔼 e^{θ X} = 1`. -/
private lemma stopped_identity {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℤ}
    (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) {θ : ℝ}
    (h1 : ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X 0 ω)) ∂P = 1) (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1), ∑' j : ℕ,
        P (ladderEvent X m j) * ENNReal.ofReal (Real.exp (θ * j))) +
      ∫⁻ ω in notAscended X n, ENNReal.ofReal (Real.exp (θ * scoreWalk X n ω)) ∂P = 1 := by
  have hB : ∀ n, MeasurableSet (notAscended X n) := fun n =>
    walkPast_le hmeas n _ (measurableSet_notAscended_walkPast X n)
  induction n with
  | zero =>
    have hL : ∀ j, ladderEvent X 0 j = ∅ := fun j => by
      ext ω
      simp [ladderEvent, scoreWalk]
    have hB0 : notAscended X 0 = Set.univ := by
      ext ω
      simp [notAscended, scoreWalk]
    simp [hL, hB0, scoreWalk]
  | succ n ih =>
    set e : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (θ * scoreWalk X (n + 1) ω)) with he
    -- Step 1: `𝔼[e^{θ S_{n+1}}; B n] = 𝔼[e^{θ S_n}; B n]`.
    have hstep : ∫⁻ ω in notAscended X n, e ω ∂P =
        ∫⁻ ω in notAscended X n, ENNReal.ofReal (Real.exp (θ * scoreWalk X n ω)) ∂P := by
      rw [← lintegral_indicator (hB n), ← lintegral_indicator (hB n)]
      have hpt : (notAscended X n).indicator e = fun ω =>
          (notAscended X n).indicator
            (fun ω => ENNReal.ofReal (Real.exp (θ * scoreWalk X n ω))) ω *
            (fun z : ℤ => ENNReal.ofReal (Real.exp (θ * z))) (X n ω) := by
        funext ω
        by_cases hω : ω ∈ notAscended X n
        · simp [Set.indicator_of_mem hω, he, ofReal_exp_scoreWalk_succ]
        · simp [Set.indicator_of_notMem hω]
      rw [hpt]
      exact (lintegral_mul_score hmeas hind hid n
        ((measurable_ofReal_exp_walkPast X θ n).indicator
          (measurableSet_notAscended_walkPast X n))
        (fun z : ℤ => ENNReal.ofReal (Real.exp (θ * z)))).trans (by rw [h1, mul_one])
    -- Step 2: `B n = B (n + 1) ∪ ⋃ j, {τ₊ = n + 1, S_{n+1} = j}`.
    have hsplit : notAscended X n = notAscended X (n + 1) ∪ ⋃ j : ℕ, ladderEvent X (n + 1) j := by
      ext ω
      simp only [notAscended, ladderEvent, Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro hω
        by_cases hpos : scoreWalk X (n + 1) ω ≤ 0
        · left
          intro m hm
          rcases Nat.lt_or_eq_of_le hm with hm | rfl
          · exact hω m (by omega)
          · exact hpos
        · right
          refine ⟨(scoreWalk X (n + 1) ω).toNat, by omega, by omega, fun m hm => hω m (by omega)⟩
      · rintro (hω | ⟨j, -, -, hω⟩)
        · exact fun m hm => hω m (by omega)
        · exact fun m hm => hω m (by omega)
    have hdisj : Disjoint (notAscended X (n + 1)) (⋃ j : ℕ, ladderEvent X (n + 1) j) := by
      refine Set.disjoint_iUnion_right.2 fun j => Set.disjoint_left.2 ?_
      rintro ω hω ⟨hpos, -, -⟩
      have := hω (n + 1) le_rfl
      omega
    have hL : ∫⁻ ω in ⋃ j : ℕ, ladderEvent X (n + 1) j, e ω ∂P =
        ∑' j : ℕ, P (ladderEvent X (n + 1) j) * ENNReal.ofReal (Real.exp (θ * j)) := by
      rw [lintegral_iUnion (fun j => measurableSet_ladderEvent hmeas (n + 1) j)
        (fun a b hab => ladderEvent_disjoint_of_ne X (p := (n + 1, a)) (q := (n + 1, b))
          (by simpa using hab))]
      refine tsum_congr fun j => ?_
      rw [setLIntegral_congr_fun (measurableSet_ladderEvent hmeas (n + 1) j)
        (g := fun _ => ENNReal.ofReal (Real.exp (θ * j))) ?_, setLIntegral_const, mul_comm]
      rintro ω ⟨-, hj, -⟩
      simp [he, hj]
    have hrec : ∫⁻ ω in notAscended X n, e ω ∂P = ∫⁻ ω in notAscended X (n + 1), e ω ∂P +
        ∑' j : ℕ, P (ladderEvent X (n + 1) j) * ENNReal.ofReal (Real.exp (θ * j)) := by
      rw [hsplit, lintegral_union (MeasurableSet.iUnion fun j => measurableSet_ladderEvent hmeas
        (n + 1) j) hdisj, hL]
    calc _ = (∑ m ∈ Finset.range (n + 1), ∑' j : ℕ,
            P (ladderEvent X m j) * ENNReal.ofReal (Real.exp (θ * j))) +
          ∫⁻ ω in notAscended X n, e ω ∂P := by
          rw [Finset.sum_range_succ, hrec]
          ring
      _ = 1 := by rw [hstep, ih]

/-- Cauchy–Schwarz step: if `𝔼 e^{θ Y} = 1` and `Y` is not almost surely `0`, then
`𝔼 e^{(θ/2) Y} < 1`, from `𝔼 (e^{θ Y / 2} - 1)^2 = 2 - 2 𝔼 e^{θ Y / 2} > 0`. -/
private lemma lintegral_exp_half_lt_one {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : Measurable Y) {θ : ℝ} (hθ : 0 < θ)
    (hint : Integrable (fun ω => Real.exp (θ * Y ω)) P)
    (h1 : ∫ ω, Real.exp (θ * Y ω) ∂P = 1) (hY0 : ¬ ∀ᵐ ω ∂P, Y ω = 0) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ / 2 * Y ω)) ∂P < 1 := by
  set Z : Ω → ℝ := fun ω => Real.exp (θ / 2 * Y ω) with hZ
  have hZsq : ∀ ω, Z ω ^ 2 = Real.exp (θ * Y ω) := fun ω => by
    rw [hZ, sq, ← Real.exp_add]
    ring_nf
  have hZm : Measurable Z := (measurable_const.mul hY).exp
  have hZint : Integrable Z P := by
    refine Integrable.mono' ((integrable_const 1).add hint) hZm.aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    have hpos : 0 < Z ω := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_pos hpos, Pi.add_apply, ← hZsq]
    nlinarith [sq_nonneg (Z ω - 1)]
  set W : Ω → ℝ := fun ω => (Z ω - 1) ^ 2 with hW
  have hWeq : W = fun ω => Real.exp (θ * Y ω) - 2 * Z ω + 1 := by
    funext ω
    rw [← hZsq ω]
    ring
  have hint2 : Integrable (fun ω => Real.exp (θ * Y ω) - 2 * Z ω) P :=
    hint.sub (hZint.const_mul 2)
  have hWint : Integrable W P := by
    rw [hWeq]
    exact hint2.add (integrable_const 1)
  have hWpos : 0 < ∫ ω, W ω ∂P := by
    rw [integral_pos_iff_support_of_nonneg (fun ω => sq_nonneg _) hWint]
    have hsupp : Function.support W = {ω | ¬ Y ω = 0} := by
      ext ω
      simp [hW, hZ, sub_eq_zero, hθ.ne']
    rw [hsupp, pos_iff_ne_zero]
    exact fun h => hY0 (ae_iff.2 h)
  have hWval : ∫ ω, W ω ∂P = 2 - 2 * ∫ ω, Z ω ∂P := by
    rw [hWeq, integral_add hint2 (integrable_const 1), integral_sub hint (hZint.const_mul 2),
      integral_const_mul, h1]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    ring
  have hZlt : ∫ ω, Z ω ∂P < 1 := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hZint (ae_of_all _ fun ω => (Real.exp_pos _).le)]
  exact ENNReal.ofReal_lt_one.2 hZlt

/-- **Ladder Cramér identity.** Let `X` be i.i.d. integer scores with walk `S`, first strict
ascending ladder epoch `τ₊` and defective ladder-height law
`g j = P(τ₊ < ∞, S_{τ₊} = j)` (`ladderLaw`). If `θ > 0` solves `𝔼 e^{θ X} = 1` (stated with
Mathlib's `mgf`) and `X` is not almost surely `0`, then `∑ j, g j e^{θ j} = 1`.

Proof: optional stopping of the martingale `e^{θ S_n}` at `τ₊ ∧ n` (`stopped_identity`, by
fixed-time independence), with the remainder `𝔼[e^{θ S_n}; τ₊ > n] ≤ (𝔼 e^{θ X / 2})^n → 0`.
This discharges the hypothesis `hcramer` of `tendsto_exp_mul_maxTail_scoreWalk`. -/
theorem hasSum_ladderLaw_mul_exp {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℤ}
    (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) {θ : ℝ} (hθ : 0 < θ)
    (hmgf : mgf (fun ω => (X 0 ω : ℝ)) P θ = 1) (hX : ¬ ∀ᵐ ω ∂P, X 0 ω = 0) :
    HasSum (fun k : ℕ => ladderLaw P X k * Real.exp (θ * k)) 1 := by
  have hY : Measurable fun ω => (X 0 ω : ℝ) :=
    (measurable_from_top (f := fun z : ℤ => (z : ℝ))).comp (hmeas 0)
  have hint : Integrable (fun ω => Real.exp (θ * X 0 ω)) P := by
    by_contra h
    rw [mgf, integral_undef h] at hmgf
    exact zero_ne_one hmgf
  have h1r : ∫ ω, Real.exp (θ * X 0 ω) ∂P = 1 := hmgf
  have h1 : ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X 0 ω)) ∂P = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => (Real.exp_pos _).le),
      h1r, ENNReal.ofReal_one]
  have hX' : ¬ ∀ᵐ ω ∂P, (X 0 ω : ℝ) = 0 := by
    simpa only [Int.cast_eq_zero] using hX
  have hρ := lintegral_exp_half_lt_one hY hθ hint h1r hX'
  -- The remainder `𝔼[e^{θ S_n}; τ₊ > n]` tends to `0`.
  set a : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ ω in notAscended X n, ENNReal.ofReal (Real.exp (θ * scoreWalk X n ω)) ∂P with ha
  have ha0 : Tendsto a atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρ) (fun _ => zero_le) fun n => ?_
    simp only [ha]
    rw [← lintegral_exp_scoreWalk hmeas hind hid (θ / 2) n]
    refine (setLIntegral_mono ((measurable_ofReal_exp_walkPast X (θ / 2) n).mono
      (walkPast_le hmeas n) le_rfl) fun ω hω => ?_).trans (setLIntegral_le_lintegral _ _)
    have hS : (scoreWalk X n ω : ℝ) ≤ 0 := by exact_mod_cast hω n le_rfl
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith))
  -- The partial sums of `∑_m 𝔼[e^{θ S_m}; τ₊ = m]` tend to `1`.
  set c : ℕ → ℝ≥0∞ := fun m =>
    ∑' j : ℕ, P (ladderEvent X m j) * ENNReal.ofReal (Real.exp (θ * j)) with hc
  have hpart : Tendsto (fun n => ∑ m ∈ Finset.range (n + 1), c m) atTop (𝓝 1) := by
    have heq : ∀ n, ∑ m ∈ Finset.range (n + 1), c m = 1 - a n := fun n =>
      ENNReal.eq_sub_of_add_eq
        (ne_top_of_le_ne_top ENNReal.one_ne_top
          (le_add_self.trans_eq (stopped_identity hmeas hind hid h1 n)))
        (stopped_identity hmeas hind hid h1 n)
    simp_rw [heq]
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds ha0 (Or.inl ENNReal.one_ne_top)
  have htsum : ∑' m, c m = 1 :=
    tendsto_nhds_unique ((ENNReal.tendsto_nat_tsum c).comp (tendsto_add_atTop_nat 1)) hpart
  have hT : ∑' j : ℕ, P (⋃ n, ladderEvent X n j) * ENNReal.ofReal (Real.exp (θ * j)) = 1 := by
    rw [← htsum, hc, ENNReal.tsum_comm]
    refine tsum_congr fun j => ?_
    rw [measure_iUnion (fun a b hab => ladderEvent_disjoint_of_ne X (p := (a, j)) (q := (b, j))
      (by simpa using hab)) (fun n => measurableSet_ladderEvent hmeas n j),
      ENNReal.tsum_mul_right]
  -- Back to real numbers.
  have hfin : ∀ j : ℕ, P (⋃ n, ladderEvent X n j) * ENNReal.ofReal (Real.exp (θ * j)) ≠ ⊤ :=
    fun j => ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hsum := (ENNReal.summable_toReal (hT ▸ ENNReal.one_ne_top)).hasSum
  rw [← ENNReal.tsum_toReal_eq hfin, hT, ENNReal.toReal_one] at hsum
  convert hsum using 2 with k
  rw [ladderLaw, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- **Ladder Cramér identity under negative drift.** If `θ > 0` solves `𝔼 e^{θ X} = 1` and
`𝔼 X < 0`, then `∑ j, g j e^{θ j} = 1`; negative drift rules out `X = 0` almost surely. -/
theorem hasSum_ladderLaw_mul_exp_of_integral_neg {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℤ} (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) {θ : ℝ} (hθ : 0 < θ)
    (hmgf : mgf (fun ω => (X 0 ω : ℝ)) P θ = 1) (hdrift : ∫ ω, (X 0 ω : ℝ) ∂P < 0) :
    HasSum (fun k : ℕ => ladderLaw P X k * Real.exp (θ * k)) 1 := by
  refine hasSum_ladderLaw_mul_exp hmeas hind hid hθ hmgf fun h => hdrift.ne ?_
  rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (h.mono fun ω hω => by simp [hω])]
  simp

/-- **Ladder-height limit from the Cramér root** (Cramér–Lundberg / Karlin–Dembo). For i.i.d.
integer scores `X` that are not almost surely `0`, if `θ > 0` solves `𝔼 e^{θ X} = 1`, the
ladder support is aperiodic and the tilted ladder mean `μ = ∑ j g j e^{θ j}` is finite, then
`e^{θ k} P(M > k) → (1 - P(M > 0)) / ((e^θ - 1) μ)`. This is
`tendsto_exp_mul_maxTail_scoreWalk` with its Cramér hypothesis discharged by
`hasSum_ladderLaw_mul_exp`. -/
theorem tendsto_exp_mul_maxTail_scoreWalk_of_mgf {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℤ} (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) {θ μ : ℝ} (hθ : 0 < θ)
    (hmgf : mgf (fun ω => (X 0 ω : ℝ)) P θ = 1) (hX : ¬ ∀ᵐ ω ∂P, X 0 ω = 0)
    (haper : Nat.setGcd {k | 0 < ladderLaw P X k} = 1)
    (hmean : HasSum (fun k : ℕ => (k : ℝ) * (ladderLaw P X k * Real.exp (θ * k))) μ) :
    Tendsto (fun k : ℕ => Real.exp (θ * k) * maxTail P X k) atTop
      (𝓝 ((1 - maxTail P X 0) / ((Real.exp θ - 1) * μ))) :=
  tendsto_exp_mul_maxTail_scoreWalk hmeas hind hid hθ
    (hasSum_ladderLaw_mul_exp hmeas hind hid hθ hmgf hX) haper hmean

end MathlibExt.Probability.Renewal
