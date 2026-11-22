/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Lévy's downward theorem and backwards martingale convergence

For a decreasing sequence of sub-σ-algebras `m 0 ⊇ m 1 ⊇ ⋯` of `m0`, the
conditional expectations `μ[g | m n]` converge almost everywhere (and in
`L¹`) to the conditional expectation `μ[g | ⨅ n, m n]` given the
intersection σ-algebra. This is Lévy's downward theorem, the decreasing
counterpart of Mathlib's Lévy upward theorem
(`MeasureTheory.Integrable.tendsto_ae_condExp`). A *backwards martingale*
`M n =ᵐ μ[M 0 | m n]` therefore converges almost everywhere (and in `L¹`)
to `μ[M 0 | ⨅ n, m n]`.

## Source

This formalizes the theorem "Theorem (Backwards martingales)" (Lecture 29)
of `v1/Atlas/TheoryOfProbability/targets.yaml` and
`v1/Atlas/TheoryOfProbability/code/BackwardsMartingales.lean`, where the
key step `condExp_antitone_ae_tendsto` (existence of an almost everywhere
limit for conditional expectations along a decreasing sequence of
σ-algebras) was left unproved. The proof here is new: the a.e.
convergence is proved with Doob's upcrossing estimate applied to the
reversed, frozen martingale `k ↦ μ[g | m (N - k)]`.

## Proof outline

Fix `a < b`. If the process `f n = μ[g | m n]` visited below `a` and above
`b` frequently, it would contain arbitrarily many strict downcrossing
pairs `i < j` with `f i > b` and `f j < a`. Reversing such pairs gives
upcrossing pairs for the reversed martingale `k ↦ f (N - k)`, so Doob's
upcrossing estimate (whose right-hand side is independent of the horizon
`N`, because it is bounded by `∫ |g| + |a|`) forces the set of points with
infinitely many oscillations to have measure zero, for every rational pair
`a < b`. Together with the `L¹` bound `‖f n‖₁ ≤ ‖g‖₁`, this gives a.e.
convergence of `f n` to a limit `h`; the limit is `⨅ n, m n`-measurable
because every tail of the sequence is measurable with respect to each
`m k`, and it is identified with `μ[g | ⨅ n, m n]` by checking integrals
over `⨅ n, m n`-measurable sets.
-/

@[expose] public section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Shifting a real sequence by a fixed amount does not change its
`limUnder`. -/
private theorem limUnder_add_atTop (u : ℕ → ℝ) (k : ℕ) :
    limUnder atTop (fun n => u (n + k)) = limUnder atTop u := by
  by_cases h : ∃ c, Tendsto u atTop (𝓝 c)
  · obtain ⟨c, hc⟩ := h
    rw [hc.limUnder_eq]
    exact ((tendsto_add_atTop_iff_nat k).mpr hc).limUnder_eq
  · have h' : ¬∃ c, Tendsto (fun n => u (n + k)) atTop (𝓝 c) :=
      fun ⟨c, hc⟩ => h ⟨c, (tendsto_add_atTop_iff_nat k).mp hc⟩
    rw [limUnder_of_not_tendsto h, limUnder_of_not_tendsto h']

/-- The filtration obtained by running a decreasing sequence `m` of
σ-algebras backwards from time `N` and then freezing it:
`m N, m (N - 1), …, m 0, m 0, …`. This is a filtration because `m` is
antitone. -/
private def reversedDecreasingFiltration (m : ℕ → MeasurableSpace Ω) (hm : Antitone m)
    (hm0 : ∀ n, m n ≤ m0) (N : ℕ) : Filtration ℕ m0 where
  seq k := m (N - k)
  mono' := by
    intro i j hij
    exact hm (Nat.sub_le_sub_left hij N)
  le' k := hm0 (N - k)

/-- The `k`-th level of the reversed filtration is `m (N - k)`. -/
private theorem reversedDecreasingFiltration_apply (m : ℕ → MeasurableSpace Ω)
    (hm : Antitone m) (hm0 : ∀ n, m n ≤ m0) (N k : ℕ) :
    (reversedDecreasingFiltration m hm hm0 N) k = m (N - k) :=
  rfl

/-- The reversed, frozen conditional expectations form a martingale with
respect to the reversed filtration, by the tower property. -/
private theorem martingale_reversedCondExp {g : Ω → ℝ} (m : ℕ → MeasurableSpace Ω)
    (hm : Antitone m) (hm0 : ∀ n, m n ≤ m0) (N : ℕ) :
    Martingale (fun k => μ[g | m (N - k)]) (reversedDecreasingFiltration m hm hm0 N) μ := by
  refine ⟨fun k => stronglyMeasurable_condExp, fun i j hij => ?_⟩
  have hle : m (N - i) ≤ m (N - j) := hm (Nat.sub_le_sub_left hij N)
  have hle0 : m (N - j) ≤ m0 := hm0 (N - j)
  have hSF : SigmaFinite (μ.trim hle0) := inferInstance
  exact condExp_condExp_of_le hle hle0

/-- Doob's upcrossing estimate for the reversed martingale, with a bound
independent of the horizon `N`: the right-hand side is controlled by the
`L¹` norm of `g` and `|a|`. -/
private theorem ofReal_sub_mul_lintegral_upcrossings_reversed_le {g : Ω → ℝ}
    (m : ℕ → MeasurableSpace Ω) (hm : Antitone m) (hm0 : ∀ n, m n ≤ m0)
    {a b : ℝ} (N : ℕ) :
    ENNReal.ofReal (b - a) *
        ∫⁻ ω, upcrossings a b (fun k => μ[g | m (N - k)]) ω ∂μ
      ≤ eLpNorm g 1 μ + ENNReal.ofReal |a| := by
  set F := fun k => μ[g | m (N - k)] with hF
  have hsub : Submartingale F (reversedDecreasingFiltration m hm hm0 N) μ :=
    (martingale_reversedCondExp m hm hm0 N).submartingale
  have h1 := hsub.mul_lintegral_upcrossings_le_lintegral_pos_part a b
  refine h1.trans (iSup_le fun K => ?_)
  have hFK : eLpNorm (F K) 1 μ ≤ eLpNorm g 1 μ := eLpNorm_condExp_le_eLpNorm g le_rfl
  have hmeas : AEStronglyMeasurable (F K - fun _ => a) μ := by
    apply AEStronglyMeasurable.sub _ aestronglyMeasurable_const
    show AEStronglyMeasurable (μ[g | m (N - K)]) μ
    exact (stronglyMeasurable_condExp (f := g) (m := m (N - K))).aestronglyMeasurable.mono
      (hm0 (N - K))
  have hμ0 : μ ≠ 0 := by
    intro h
    have h1 := measure_univ (μ := μ)
    rw [h] at h1
    simp at h1
  have hconst : eLpNorm (fun _ : Ω => a) 1 μ ≤ ENNReal.ofReal |a| := by
    rw [eLpNorm_const a one_ne_zero hμ0, measure_univ, ENNReal.one_rpow, mul_one,
      Real.enorm_eq_ofReal_abs]
  calc ∫⁻ ω, ENNReal.ofReal ((F K ω - a)⁺) ∂μ
      ≤ ∫⁻ ω, ‖F K ω - a‖ₑ ∂μ := by
        apply lintegral_mono
        intro ω
        show ENNReal.ofReal ((F K ω - a)⁺) ≤ ‖F K ω - a‖ₑ
        rw [Real.enorm_eq_ofReal_abs]
        apply ENNReal.ofReal_le_ofReal
        by_cases h : 0 ≤ F K ω - a
        · rw [posPart_eq_self.2 h, abs_of_nonneg h]
        · rw [posPart_eq_zero.2 (le_of_not_ge h), abs_of_neg (lt_of_not_ge h)]
          exact neg_nonneg.mpr (le_of_not_ge h)
    _ = eLpNorm (F K - fun _ => a) 1 μ := by
        rw [eLpNorm_one_eq_lintegral_enorm hmeas]
        rfl
    _ ≤ eLpNorm (F K) 1 μ + eLpNorm (fun _ => a) 1 μ :=
        eLpNorm_sub_le le_rfl
    _ ≤ eLpNorm g 1 μ + ENNReal.ofReal |a| := add_le_add hFK hconst

/-- If a process has `K + 1` strict upcrossing pairs, then it has at least
`K + 1` upcrossings before the last pair is completed. Proved by induction
on `K`, boosting the upcrossing count by one pair at a time with
`upcrossingsBefore_lt_of_exists_upcrossing`. -/
private theorem le_upcrossingsBefore_of_upcrossing_pairs {h : ℕ → Ω → ℝ} (ω : Ω)
    {a b : ℝ} (hab : a < b) :
    ∀ (K : ℕ) (p q : ℕ → ℕ),
      (∀ t, t ≤ K → p t < q t) → (∀ t, t < K → q t < p (t + 1)) →
      (∀ t, t ≤ K → h (p t) ω < a) → (∀ t, t ≤ K → b < h (q t) ω) →
      K + 1 ≤ upcrossingsBefore a b h (q K + 1) ω := by
  intro K
  induction K with
  | zero =>
    intro p q hpq hq hpa hqb
    have hlt := upcrossingsBefore_lt_of_exists_upcrossing (f := h) (ω := ω) (N := 0)
      hab (N₁ := p 0) (N₂ := q 0) (Nat.zero_le _) (hpa 0 (le_refl 0))
      (Nat.le_of_lt (hpq 0 (le_refl 0))) (hqb 0 (le_refl 0))
    rw [upcrossingsBefore_zero] at hlt
    omega
  | succ K ih =>
    intro p q hpq hq hpa hqb
    have hIH := ih p q (fun t ht => hpq t (Nat.le_succ_of_le ht))
      (fun t ht => hq t (Nat.lt_succ_of_lt ht)) (fun t ht => hpa t (Nat.le_succ_of_le ht))
      (fun t ht => hqb t (Nat.le_succ_of_le ht))
    have hlt := upcrossingsBefore_lt_of_exists_upcrossing (f := h) (ω := ω)
      (N := q K + 1) hab (N₁ := p (K + 1)) (N₂ := q (K + 1))
      (Nat.succ_le_of_lt (hq K (Nat.lt_succ_self K))) (hpa (K + 1) (le_refl _))
      (Nat.le_of_lt (hpq (K + 1) (le_refl _))) (hqb (K + 1) (le_refl _))
    omega

/-- From frequently visiting below `a` and above `b`, extract `K + 1`
strict downcrossing pairs (high then low), in increasing order. -/
private theorem exists_downcrossing_pairs_of_frequently {f : ℕ → Ω → ℝ} (ω : Ω)
    {a b : ℝ} (hab : a < b) (hhigh : ∃ᶠ n in atTop, b < f n ω)
    (hlow : ∃ᶠ n in atTop, f n ω < a) :
    ∀ K : ℕ, ∃ i j : ℕ → ℕ,
      (∀ t, t ≤ K → i t < j t) ∧ (∀ t, t < K → j t < i (t + 1)) ∧
      (∀ t, t ≤ K → b < f (i t) ω) ∧ (∀ t, t ≤ K → f (j t) ω < a) ∧
      (∀ t, t ≤ K → j t ≤ j K) := by
  rw [frequently_atTop] at hhigh hlow
  intro K
  induction K with
  | zero =>
    obtain ⟨i0, -, hi0⟩ := hhigh 0
    obtain ⟨j0, hj0a, hj0⟩ := hlow i0
    have hij : i0 < j0 := by
      rcases hj0a.eq_or_lt with h | h
      · exfalso
        rw [← h] at hj0
        exact absurd (lt_trans hi0 hj0) (not_lt_of_ge hab.le)
      · exact h
    refine ⟨fun _ => i0, fun _ => j0, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      rw [Nat.le_zero] at ht
      rw [ht]
      exact hij
    · intro t ht
      omega
    · intro t ht
      rw [Nat.le_zero] at ht
      rw [ht]
      exact hi0
    · intro t ht
      rw [Nat.le_zero] at ht
      rw [ht]
      exact hj0
    · intro t ht
      exact le_rfl
  | succ K ih =>
    obtain ⟨i, j, hij, hji, hi, hj, hjmono⟩ := ih
    obtain ⟨i', hi'a, hi'⟩ := hhigh (j K + 1)
    obtain ⟨j', hj'a, hj'⟩ := hlow i'
    have hij' : i' < j' := by
      rcases hj'a.eq_or_lt with h | h
      · exfalso
        rw [← h] at hj'
        exact absurd (lt_trans hi' hj') (not_lt_of_ge hab.le)
      · exact h
    refine ⟨Function.update i (K + 1) i', Function.update j (K + 1) j', ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      by_cases h : t = K + 1
      · subst h
        rw [Function.update_self, Function.update_self]
        exact hij'
      · have hK : t ≤ K := Nat.le_of_lt_succ (lt_of_le_of_ne ht (by omega))
        rw [Function.update_of_ne (by omega : t ≠ K + 1),
          Function.update_of_ne (by omega : t ≠ K + 1)]
        exact hij t hK
    · intro t ht
      by_cases h : t = K
      · rw [h]
        rw [Function.update_of_ne (by omega : K ≠ K + 1)]
        show j K < Function.update i (K + 1) i' (K + 1)
        rw [Function.update_self]
        omega
      · have hK : t < K := lt_of_le_of_ne (Nat.le_of_lt_succ ht) h
        have hK1 : t + 1 ≤ K := Nat.succ_le_of_lt hK
        rw [Function.update_of_ne (by omega : t ≠ K + 1),
          Function.update_of_ne (by omega : t + 1 ≠ K + 1)]
        exact hji t hK
    · intro t ht
      by_cases h : t = K + 1
      · subst h
        rw [Function.update_self]
        exact hi'
      · have hK : t ≤ K := Nat.le_of_lt_succ (lt_of_le_of_ne ht (by omega))
        rw [Function.update_of_ne (by omega : t ≠ K + 1)]
        exact hi t hK
    · intro t ht
      by_cases h : t = K + 1
      · subst h
        rw [Function.update_self]
        exact hj'
      · have hK : t ≤ K := Nat.le_of_lt_succ (lt_of_le_of_ne ht (by omega))
        rw [Function.update_of_ne (by omega : t ≠ K + 1)]
        exact hj t hK
    · intro t ht
      by_cases h : t = K + 1
      · subst h
        rw [Function.update_self]
      · have hK : t ≤ K := Nat.le_of_lt_succ (lt_of_le_of_ne ht (by omega))
        rw [Function.update_of_ne (by omega : t ≠ K + 1),
          Function.update_self]
        exact le_trans (hjmono t hK) (le_trans (Nat.le_of_lt (by omega : j K < i'))
          (Nat.le_of_lt hij'))

/-- Reversing `K + 1` downcrossing pairs of `f` inside `[0, N]` gives
`K + 1` upcrossing pairs of the reversed process `k ↦ f (N - k)`, so the
reversed process has at least `K + 1` upcrossings. -/
private theorem le_upcrossings_reversed_of_downcrossing_pairs {f : ℕ → Ω → ℝ}
    (ω : Ω) {a b : ℝ} (hab : a < b) {K : ℕ} {i j : ℕ → ℕ} {N : ℕ}
    (hN : j K ≤ N)
    (hij : ∀ t, t ≤ K → i t < j t) (hji : ∀ t, t < K → j t < i (t + 1))
    (hi : ∀ t, t ≤ K → b < f (i t) ω) (hj : ∀ t, t ≤ K → f (j t) ω < a)
    (hjmono : ∀ t, t ≤ K → j t ≤ j K) :
    ((K + 1 : ℕ) : ℝ≥0∞) ≤ upcrossings a b (fun k => f (N - k)) ω := by
  classical
  set p : ℕ → ℕ := fun s => N - j (K - s) with hp
  set q : ℕ → ℕ := fun s => N - i (K - s) with hq
  have hle_j : ∀ s, s ≤ K → j (K - s) ≤ N := fun s hs =>
    le_trans (hjmono (K - s) (by omega)) hN
  have hle_i : ∀ s, s ≤ K → i (K - s) ≤ N := fun s hs =>
    le_trans (Nat.le_of_lt (hij (K - s) (by omega))) (hle_j s hs)
  have hpq : ∀ s, s ≤ K → p s < q s := by
    intro s hs
    have h1 := hij (K - s) (by omega)
    have h2 := hle_j s hs
    have h3 := hle_i s hs
    simp only [hp, hq]
    omega
  have hqp : ∀ s, s < K → q s < p (s + 1) := by
    intro s hs
    have h5 : K - s - 1 + 1 = K - s := by omega
    have h1 := hji (K - s - 1) (by omega)
    rw [h5] at h1
    have h2 := hle_j s (by omega)
    have h3 := hle_i s (by omega)
    have h6 : j (K - s - 1) ≤ N := le_trans (Nat.le_of_lt h1) h3
    have h4 : K - (s + 1) = K - s - 1 := by omega
    simp only [hp, hq, h4]
    omega
  have hpa : ∀ s, s ≤ K → (fun k => f (N - k)) (p s) ω < a := by
    intro s hs
    have h2 := hle_j s hs
    have h3 := hj (K - s) (by omega)
    simp only [hp]
    show f (N - (N - j (K - s))) ω < a
    have : N - (N - j (K - s)) = j (K - s) := Nat.sub_sub_self h2
    rw [this]
    exact h3
  have hqb : ∀ s, s ≤ K → b < (fun k => f (N - k)) (q s) ω := by
    intro s hs
    have h2 := hle_i s hs
    have h3 := hi (K - s) (by omega)
    simp only [hq]
    show b < f (N - (N - i (K - s))) ω
    have : N - (N - i (K - s)) = i (K - s) := Nat.sub_sub_self h2
    rw [this]
    exact h3
  have hbefore := le_upcrossingsBefore_of_upcrossing_pairs (h := fun k => f (N - k)) ω
    hab K p q hpq hqp hpa hqb
  have hcast : ((K + 1 : ℕ) : ℝ≥0∞) ≤
      ((upcrossingsBefore a b (fun k => f (N - k)) (q K + 1) ω : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hbefore
  refine hcast.trans ?_
  show ((upcrossingsBefore a b (fun k => f (N - k)) (q K + 1) ω : ℕ) : ℝ≥0∞) ≤
    ⨆ X, ((upcrossingsBefore a b (fun k => f (N - k)) X ω : ℕ) : ℝ≥0∞)
  exact le_iSup (fun X : ℕ => ((upcrossingsBefore a b (fun k => f (N - k)) X ω : ℕ) : ℝ≥0∞))
    (q K + 1)

set_option linter.unusedSectionVars false in
/-- If a process has a uniformly bounded reversed-upcrossing estimate, then
the set where it visits below `a` and above `b` frequently has measure
zero. The key step: on that set there are arbitrarily many downcrossing
pairs inside some finite segment `[0, N]`, and reversing them gives
arbitrarily many upcrossings of a reversed process, contradicting the
uniform bound via Markov's inequality. -/
private theorem measure_setOf_frequently_lt_and_frequently_gt_eq_zero
    {f : ℕ → Ω → ℝ} {a b : ℝ} (hab : a < b) {S : ℝ≥0∞} (hS : S ≠ ∞)
    (hbound : ∀ N : ℕ, ENNReal.ofReal (b - a) *
        ∫⁻ ω, upcrossings a b (fun k => f (N - k)) ω ∂μ ≤ S)
    (hmeas : ∀ N : ℕ, AEMeasurable (upcrossings a b (fun k => f (N - k))) μ) :
    μ {ω | (∃ᶠ n in atTop, f n ω < a) ∧ (∃ᶠ n in atTop, b < f n ω)} = 0 := by
  have hba : ENNReal.ofReal (b - a) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (sub_pos.2 hab)
  have hCfin : S / ENNReal.ofReal (b - a) ≠ ∞ := ENNReal.div_ne_top hS hba
  have hboundM : ∀ M : ℕ,
      μ {ω | (∃ᶠ n in atTop, f n ω < a) ∧ (∃ᶠ n in atTop, b < f n ω)}
        ≤ (S / ENNReal.ofReal (b - a)) / ((M + 1 : ℕ) : ℝ≥0∞) := by
    intro M
    set A : ℕ → Set Ω := fun N => {ω | ∃ i j : ℕ → ℕ,
      (∀ t, t ≤ M → i t < j t) ∧ (∀ t, t < M → j t < i (t + 1)) ∧
      (∀ t, t ≤ M → b < f (i t) ω) ∧ (∀ t, t ≤ M → f (j t) ω < a) ∧
      (∀ t, t ≤ M → j t ≤ j M) ∧ j M ≤ N} with hA
    have hAmono : Monotone A := by
      intro N N' hNN ω hω
      obtain ⟨i, j, hij, hji, hi, hj, hmono, hle⟩ := hω
      exact ⟨i, j, hij, hji, hi, hj, hmono, le_trans hle hNN⟩
    have hsub : {ω | (∃ᶠ n in atTop, f n ω < a) ∧ (∃ᶠ n in atTop, b < f n ω)}
        ⊆ ⋃ N, A N := by
      intro ω hω
      obtain ⟨h1, h2⟩ := hω
      obtain ⟨i, j, hij, hji, hi, hj, hmono⟩ :=
        exists_downcrossing_pairs_of_frequently ω hab h2 h1 M
      exact Set.mem_iUnion.2 ⟨j M, i, j, hij, hji, hi, hj, hmono, le_refl _⟩
    have hAN : ∀ N : ℕ,
        μ (A N) ≤ (S / ENNReal.ofReal (b - a)) / ((M + 1 : ℕ) : ℝ≥0∞) := by
      intro N
      have hsubset : A N ⊆
          {ω | ((M + 1 : ℕ) : ℝ≥0∞) ≤ upcrossings a b (fun k => f (N - k)) ω} := by
        intro ω hω
        obtain ⟨i, j, hij, hji, hi, hj, hmono, hle⟩ := hω
        exact le_upcrossings_reversed_of_downcrossing_pairs ω hab hle hij hji hi hj hmono
      have hmarkov := mul_meas_ge_le_lintegral₀ (hmeas N) ((M + 1 : ℕ) : ℝ≥0∞)
      have hInt : ∫⁻ ω, upcrossings a b (fun k => f (N - k)) ω ∂μ
          ≤ S / ENNReal.ofReal (b - a) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hba) (Or.inl ENNReal.ofReal_ne_top),
          mul_comm]
        exact hbound N
      have hge : μ {ω | ((M + 1 : ℕ) : ℝ≥0∞) ≤ upcrossings a b (fun k => f (N - k)) ω}
          ≤ (∫⁻ ω, upcrossings a b (fun k => f (N - k)) ω ∂μ) / ((M + 1 : ℕ) : ℝ≥0∞) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero M))) (Or.inl (ENNReal.natCast_ne_top _)), mul_comm]
        exact hmarkov
      exact (measure_mono hsubset).trans
        (hge.trans (ENNReal.div_le_div_right hInt ((M + 1 : ℕ) : ℝ≥0∞)))
    refine (measure_mono hsub).trans ?_
    rw [hAmono.measure_iUnion]
    exact iSup_le hAN
  have hC0 : Tendsto
      (fun M : ℕ => (S / ENNReal.ofReal (b - a)) / ((M + 1 : ℕ) : ℝ≥0∞)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (S / ENNReal.ofReal (b - a)) / (n : ℝ≥0∞)) atTop
        (𝓝 ((S / ENNReal.ofReal (b - a)) / ⊤)) :=
      ENNReal.Tendsto.const_div ENNReal.tendsto_nat_nhds_top (Or.inr hCfin)
    rw [ENNReal.div_top] at h1
    exact h1.comp (tendsto_add_atTop_nat 1)
  have hle0 : μ {ω | (∃ᶠ n in atTop, f n ω < a) ∧ (∃ᶠ n in atTop, b < f n ω)} ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hC0 (Filter.Eventually.of_forall hboundM)
  exact le_antisymm hle0 (by positivity)

/-- Identification of an a.e. limit of conditional expectations along a
decreasing sequence of σ-algebras: if `μ[g | m n] → h` a.e., `h` is
integrable and `⨅ n, m n`-strongly measurable, then `h =ᵐ μ[g | ⨅ n, m n]`. -/
private theorem condExp_antitone_limit_eq {g h : Ω → ℝ} (m : ℕ → MeasurableSpace Ω)
    (hm_le : ∀ n, m n ≤ m0) (hg : Integrable g μ)
    (hh_ae : ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[g | m n]) ω) atTop (𝓝 (h ω)))
    (hh_int : Integrable h μ) (hh_meas : StronglyMeasurable[⨅ n, m n] h) :
    h =ᵐ[μ] μ[g | ⨅ n, m n] := by
  have hm_inf_le : ⨅ n, m n ≤ m0 := le_trans (iInf_le _ 0) (hm_le 0)
  refine ae_eq_condExp_of_forall_setIntegral_eq hm_inf_le hg
    (fun s _ _ => hh_int.integrableOn) ?_ hh_meas.aestronglyMeasurable
  intro s hs hμs
  have hs_n : ∀ n, MeasurableSet[m n] s := fun n => (iInf_le m n) s hs
  have hint_eq : ∀ n, ∫ x in s, (μ[g | m n]) x ∂μ = ∫ x in s, g x ∂μ :=
    fun n => setIntegral_condExp (hm_le n) hg (hs_n n)
  have hui : UniformIntegrable (fun n => (μ[g | m n] : Ω → ℝ)) 1 μ :=
    hg.uniformIntegrable_condExp hm_le
  have haem : ∀ n, AEStronglyMeasurable (μ[g | m n]) μ := fun n => by
    show AEStronglyMeasurable (μ[g | m n]) μ
    exact (stronglyMeasurable_condExp (f := g) (m := m n)).aestronglyMeasurable.mono
      (hm_le n)
  have hL1 : Tendsto (fun n => eLpNorm ((μ[g | m n]) - h) 1 μ) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top haem
      (memLp_one_iff_integrable.mpr hh_int) hui.1
      (tendstoInMeasure_of_tendsto_ae haem hh_ae)
  have hL1' : Tendsto (fun n => ∫⁻ x, ‖(μ[g | m n]) x - h x‖ₑ ∂μ) atTop (𝓝 0) := by
    have hcongr : ∀ n, ∫⁻ x, ‖(μ[g | m n]) x - h x‖ₑ ∂μ
        = eLpNorm ((μ[g | m n]) - h) 1 μ := by
      intro n
      exact (eLpNorm_one_eq_lintegral_enorm
        (((stronglyMeasurable_condExp (f := g) (m := m n)).aestronglyMeasurable.mono
          (hm_le n)).sub
          (hh_meas.mono (le_trans (iInf_le _ 0) (hm_le 0))).aestronglyMeasurable)).symm
    simp_rw [hcongr]
    exact hL1
  have hsetint := tendsto_setIntegral_of_L1 h hh_int.aestronglyMeasurable
    (Filter.Eventually.of_forall fun n => integrable_condExp) hL1' s
  exact tendsto_nhds_unique (hsetint.congr hint_eq) tendsto_const_nhds

set_option linter.style.haveILetI false in
/-- Existence of an almost everywhere limit for conditional expectations
along a decreasing sequence of σ-algebras, together with its
`⨅ n, m n`-strong measurability and integrability. -/
private theorem condExp_antitone_ae_tendsto {g : Ω → ℝ} (m : ℕ → MeasurableSpace Ω)
    (hm : Antitone m) (hm0 : ∀ n, m n ≤ m0) (hg : Integrable g μ) :
    ∃ h : Ω → ℝ, StronglyMeasurable[⨅ n, m n] h ∧ Integrable h μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[g | m n]) ω) atTop (𝓝 (h ω)) := by
  set f : ℕ → Ω → ℝ := fun n => μ[g | m n] with hf
  have hgLp : eLpNorm g 1 μ ≠ ∞ :=
    (memLp_one_iff_integrable.mpr hg).eLpNorm_lt_top.ne
  have hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ ↑(eLpNorm g 1 μ).toNNReal := fun n => by
    rw [ENNReal.coe_toNNReal hgLp]
    exact eLpNorm_condExp_le_eLpNorm g le_rfl
  have hfreq : ∀ᵐ ω ∂μ, ∀ a b : ℚ, (a : ℝ) < (b : ℝ) →
      ¬((∃ᶠ n in atTop, f n ω < (a : ℝ)) ∧ (∃ᶠ n in atTop, (b : ℝ) < f n ω)) := by
    rw [ae_all_iff]
    intro a
    rw [ae_all_iff]
    intro b
    by_cases hab : (a : ℝ) < (b : ℝ)
    · have hS : eLpNorm g 1 μ + ENNReal.ofReal |(a : ℝ)| ≠ ∞ :=
        ENNReal.add_ne_top.mpr ⟨hgLp, ENNReal.ofReal_ne_top⟩
      have hbound : ∀ N : ℕ, ENNReal.ofReal ((b : ℝ) - (a : ℝ)) *
          ∫⁻ ω, upcrossings (a : ℝ) (b : ℝ) (fun k => f (N - k)) ω ∂μ
            ≤ eLpNorm g 1 μ + ENNReal.ofReal |(a : ℝ)| := by
        intro N
        exact ofReal_sub_mul_lintegral_upcrossings_reversed_le (m := m) (hm := hm)
          (hm0 := hm0) N
      have hmeas : ∀ N : ℕ, AEMeasurable (upcrossings (a : ℝ) (b : ℝ)
          (fun k => f (N - k))) μ := by
        intro N
        exact ((martingale_reversedCondExp (m := m) (hm := hm) (hm0 := hm0) (g := g) N).1
          |>.measurable_upcrossings hab).aemeasurable
      have h0 := measure_setOf_frequently_lt_and_frequently_gt_eq_zero (f := f) hab hS
        hbound hmeas
      have hQ : ∀ᵐ ω ∂μ, ¬((∃ᶠ n in atTop, f n ω < (a : ℝ)) ∧
          (∃ᶠ n in atTop, (b : ℝ) < f n ω)) := by
        rw [ae_iff]
        exact measure_mono_null (fun ω hω => not_not.mp hω) h0
      filter_upwards [hQ] with ω hω _
      exact hω
    · exact ae_of_all μ fun _ hlt => absurd hlt hab
  have hlim : ∀ᵐ ω ∂μ, liminf (fun n => ‖f n ω‖ₑ) atTop < ⊤ :=
    ae_bdd_liminf_atTop_of_eLpNorm_bdd one_ne_zero hbdd
  have hconv : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
    filter_upwards [hlim, hfreq] with ω hlim hfreq
    have hlim' : liminf (fun n => (Real.nnabs (f n ω) : ℝ≥0∞)) atTop ≠ ⊤ := by
      have heq : (fun n => (Real.nnabs (f n ω) : ℝ≥0∞)) = (fun n => ‖f n ω‖ₑ) := by
        funext n
        rw [Real.enorm_eq_ofReal_abs]
        exact (ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)).symm
      rw [heq]
      exact (lt_top_iff_ne_top.mp hlim)
    have hbdd_abs : IsBoundedUnder (· ≤ ·) atTop (fun n => |f n ω|) := by
      by_contra hbdd
      obtain ⟨a, b, hab, h1, h2⟩ :=
        ENNReal.exists_upcrossings_of_not_bounded_under hlim' hbdd
      exact hfreq a b (Rat.cast_lt.2 hab) ⟨h1, h2⟩
    obtain ⟨hbd_le, hbd_ge⟩ := isBoundedUnder_le_abs.mp hbdd_abs
    refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ hbd_le hbd_ge
    intro a ha b hb hab
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    rw [← ha', ← hb'] at hab ⊢
    exact hfreq a' b' hab
  -- The pointwise limit, and its measurability at every level.
  have hmeas_all : ∀ k, StronglyMeasurable[m k] (fun ω => limUnder atTop (fun n => f n ω)) := by
    intro k
    have hshift : (fun ω => limUnder atTop (fun n => f n ω))
        = fun ω => limUnder atTop (fun n => f (n + k) ω) := by
      funext ω
      exact (limUnder_add_atTop (fun n => f n ω) k).symm
    rw [hshift]
    have hstep : ∀ n, StronglyMeasurable[m k] (fun ω => f (n + k) ω) := by
      intro n
      show StronglyMeasurable[m k] (μ[g | m (n + k)])
      exact stronglyMeasurable_condExp.mono (hm (Nat.le_add_left k n))
    letI : MeasurableSpace Ω := m k
    exact StronglyMeasurable.limUnder (l := atTop)
      (f := fun n ω => f (n + k) ω) hstep
  have hmeas_inf : StronglyMeasurable[⨅ n, m n] (fun ω => limUnder atTop (fun n => f n ω)) :=
    (show Measurable[⨅ n, m n] (fun ω => limUnder atTop (fun n => f n ω)) from
      fun s hs => (MeasurableSpace.measurableSet_iInf.2 fun k =>
        (hmeas_all k).measurable hs)).stronglyMeasurable
  have hconvL : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop
      (𝓝 ((fun ω => limUnder atTop (fun n => f n ω)) ω)) := by
    filter_upwards [hconv] with ω hω
    obtain ⟨c, hc⟩ := hω
    rw [hc.limUnder_eq]
    exact hc
  refine ⟨fun ω => limUnder atTop (fun n => f n ω), hmeas_inf, ?_, hconvL⟩
  -- Integrability by Fatou's lemma applied to the `L¹` bound.
  have hbound : eLpNorm (fun ω => limUnder atTop (fun n => f n ω)) 1 μ ≤ eLpNorm g 1 μ := by
    have hmeas0 : AEStronglyMeasurable (fun ω => limUnder atTop (fun n => f n ω)) μ :=
      hmeas_inf.mono (le_trans (iInf_le _ 0) (hm0 0)) |>.aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm hmeas0]
    have h1 : ∫⁻ ω, ‖limUnder atTop (fun n => f n ω)‖ₑ ∂μ
        ≤ ∫⁻ ω, liminf (fun n => ‖f n ω‖ₑ) atTop ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hconv] with ω hω
      obtain ⟨c, hc⟩ := hω
      rw [hc.limUnder_eq]
      have hc2 : Tendsto (fun n => ‖f n ω‖ₑ) atTop (𝓝 ‖c‖ₑ) :=
        (continuous_enorm.tendsto c).comp hc
      exact le_of_eq (hc2.liminf_eq.symm)
    refine h1.trans ?_
    refine (lintegral_liminf_le' ?_).trans ?_
    · intro n
      exact ((stronglyMeasurable_condExp (f := g) (m := m n)).aestronglyMeasurable.mono
        (hm0 n)).enorm
    · rw [Filter.liminf_eq_iSup_iInf_of_nat]
      refine iSup_le fun n => ?_
      refine (iInf₂_le n le_rfl).trans ?_
      show (∫⁻ ω, ‖f n ω‖ₑ ∂μ) ≤ eLpNorm g 1 μ
      have hae : AEStronglyMeasurable (μ[g | m n]) μ :=
        (stronglyMeasurable_condExp (f := g) (m := m n)).aestronglyMeasurable.mono
          (hm0 n)
      rw [← eLpNorm_one_eq_lintegral_enorm hae]
      exact eLpNorm_condExp_le_eLpNorm g le_rfl
  exact memLp_one_iff_integrable.mp (lt_of_le_of_lt hbound (lt_top_iff_ne_top.mpr hgLp))

/-- **Lévy's downward theorem, almost sure convergence.** Let $(\Omega, \mathcal F, \mu)$ be a
probability space, let $\mathcal F_0 \supseteq \mathcal F_1 \supseteq \cdots$ be a decreasing
sequence of sub-σ-algebras of $\mathcal F$, and let $\mathcal F_\infty = \bigcap_n \mathcal F_n$.
For every function $g : \Omega \to \mathbb R$, the conditional expectations
$\mathbb E[g \mid \mathcal F_n]$ converge to $\mathbb E[g \mid \mathcal F_\infty]$ as
$n \to \infty$, $\mu$-almost everywhere.

No integrability hypothesis is needed: for a non-integrable $g$ every conditional expectation is
$0$ by convention, and the statement is trivial. -/
theorem levy_downward_ae {g : Ω → ℝ} (m : ℕ → MeasurableSpace Ω)
    (hm : Antitone m) (hm0 : ∀ n, m n ≤ m0) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[g | m n]) ω) atTop (𝓝 ((μ[g | ⨅ n, m n]) ω)) := by
  by_cases hg : Integrable g μ
  · obtain ⟨h, hh_meas, hh_int, hh_ae⟩ := condExp_antitone_ae_tendsto m hm hm0 hg
    have hid := condExp_antitone_limit_eq m hm0 hg hh_ae hh_int hh_meas
    filter_upwards [hh_ae, hid] with ω hω_conv hω_eq
    rwa [← hω_eq]
  · have h0 : ∀ n, (μ[g | m n] : Ω → ℝ) = 0 := fun n => condExp_of_not_integrable hg
    have h0' : (μ[g | ⨅ n, m n] : Ω → ℝ) = 0 := condExp_of_not_integrable hg
    simp only [h0, h0', Pi.zero_apply]
    exact ae_of_all μ fun _ => tendsto_const_nhds

/-- **Lévy's downward theorem in L¹.** Let $(\Omega, \mathcal F, \mu)$ be a probability space,
let $\mathcal F_0 \supseteq \mathcal F_1 \supseteq \cdots$ be a decreasing sequence of
sub-σ-algebras of $\mathcal F$, and let $\mathcal F_\infty = \bigcap_n \mathcal F_n$. For every
integrable function $g : \Omega \to \mathbb R$, the $L^1(\mu)$ norm
$\lVert \mathbb E[g \mid \mathcal F_n] - \mathbb E[g \mid \mathcal F_\infty] \rVert_1$ tends to $0$
as $n \to \infty$. -/
theorem levy_downward_tendsto_eLpNorm_one {g : Ω → ℝ} (m : ℕ → MeasurableSpace Ω)
    (hm : Antitone m) (hm0 : ∀ n, m n ≤ m0) (hg : Integrable g μ) :
    Tendsto (fun n => eLpNorm ((μ[g | m n]) - μ[g | ⨅ n, m n]) 1 μ) atTop (𝓝 0) := by
  have hconv := levy_downward_ae (μ := μ) (g := g) m hm hm0
  have haem : ∀ n, AEStronglyMeasurable (μ[g | m n]) μ :=
    fun n => (stronglyMeasurable_condExp (f := g) (m := m n)).aestronglyMeasurable.mono
      (hm0 n)
  have hui : UniformIntegrable (fun n => (μ[g | m n] : Ω → ℝ)) 1 μ :=
    hg.uniformIntegrable_condExp hm0
  exact tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top haem
    (memLp_one_iff_integrable.mpr integrable_condExp) hui.1
    (tendstoInMeasure_of_tendsto_ae haem hconv)

/-- **Backwards martingale.** Let $\mu$ be a measure on a measurable space $(\Omega, \mathcal F)$
and let $(\mathcal F_n)_{n \ge 0}$ be a sequence of σ-algebras on $\Omega$. A sequence of
functions $M_n : \Omega \to \mathbb R$ is a backwards martingale with respect to $(\mathcal F_n)$
and $\mu$ if $M_0$ is $\mu$-integrable and, for every $n$, $M_n = \mathbb E[M_0 \mid \mathcal F_n]$
$\mu$-almost everywhere.

Here $\mathbb E[M_0 \mid \mathcal F_n]$ is the conditional expectation with respect to $\mu$ when
$\mathcal F_n \subseteq \mathcal F$ and the restriction of $\mu$ to $\mathcal F_n$ is σ-finite,
and is $0$ by convention otherwise. The definition is used when $(\mathcal F_n)$ is a decreasing
sequence of sub-σ-algebras, but it does not require this. -/
def IsBackwardsMartingale (M : ℕ → Ω → ℝ) (m : ℕ → MeasurableSpace Ω) (μ : Measure Ω) : Prop :=
  Integrable (M 0) μ ∧ ∀ n, M n =ᵐ[μ] μ[M 0 | m n]

/-- **Backwards martingale convergence theorem, almost sure convergence.** Let
$(\Omega, \mathcal F, \mu)$ be a probability space, let
$\mathcal F_0 \supseteq \mathcal F_1 \supseteq \cdots$ be a decreasing sequence of sub-σ-algebras
of $\mathcal F$, and let $\mathcal F_\infty = \bigcap_n \mathcal F_n$. If the real-valued process
$(M_n)_{n \ge 0}$ is a backwards martingale with respect to $(\mathcal F_n)$ and $\mu$, then
$M_n \to \mathbb E[M_0 \mid \mathcal F_\infty]$ as $n \to \infty$, $\mu$-almost everywhere. -/
theorem backwards_martingale_ae_tendsto {M : ℕ → Ω → ℝ} (m : ℕ → MeasurableSpace Ω)
    (hm : Antitone m) (hm0 : ∀ n, m n ≤ m0) (hM : IsBackwardsMartingale M m μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => M n ω) atTop (𝓝 ((μ[M 0 | ⨅ n, m n]) ω)) := by
  have hlevy := levy_downward_ae (μ := μ) (g := M 0) m hm hm0
  have hae : ∀ n, ∀ᵐ ω ∂μ, M n ω = (μ[M 0 | m n]) ω := fun n => hM.2 n
  rw [← ae_all_iff] at hae
  filter_upwards [hlevy, hae] with ω hω_conv hω_eq
  exact hω_conv.congr (fun n => (hω_eq n).symm)

/-- **Backwards martingale convergence theorem in L¹.** Let $(\Omega, \mathcal F, \mu)$ be a
probability space, let $\mathcal F_0 \supseteq \mathcal F_1 \supseteq \cdots$ be a decreasing
sequence of sub-σ-algebras of $\mathcal F$, and let $\mathcal F_\infty = \bigcap_n \mathcal F_n$.
If the real-valued process $(M_n)_{n \ge 0}$ is a backwards martingale with respect to
$(\mathcal F_n)$ and $\mu$, then the $L^1(\mu)$ norm
$\lVert M_n - \mathbb E[M_0 \mid \mathcal F_\infty] \rVert_1$ tends to $0$ as $n \to \infty$. -/
theorem backwards_martingale_tendsto_eLpNorm_one {M : ℕ → Ω → ℝ}
    (m : ℕ → MeasurableSpace Ω) (hm : Antitone m) (hm0 : ∀ n, m n ≤ m0)
    (hM : IsBackwardsMartingale M m μ) :
    Tendsto (fun n => eLpNorm (M n - μ[M 0 | ⨅ n, m n]) 1 μ) atTop (𝓝 0) := by
  have hconv := backwards_martingale_ae_tendsto m hm hm0 hM
  have haem : ∀ n, AEStronglyMeasurable (M n) μ := by
    intro n
    exact ((stronglyMeasurable_condExp (f := M 0) (m := m n)).aestronglyMeasurable.congr
      (hM.2 n).symm).mono (hm0 n)
  have hui : UniformIntegrable M 1 μ := by
    have hui0 : UniformIntegrable (fun n => (μ[M 0 | m n] : Ω → ℝ)) 1 μ :=
      hM.1.uniformIntegrable_condExp hm0
    refine hui0.ae_eq ?_
    intro n
    exact (hM.2 n).symm
  exact tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top haem
    (memLp_one_iff_integrable.mpr integrable_condExp) hui.1
    (tendstoInMeasure_of_tendsto_ae haem hconv)

end MeasureTheory
