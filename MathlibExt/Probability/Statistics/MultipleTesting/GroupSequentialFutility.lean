/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.AlphaSpending

/-!
# Group-sequential futility bounds from a beta-spending budget

A group-sequential trial with `K` planned looks may stop early for **efficacy** (reject the
null) or for **futility** (stop without rejecting because the treatment is unlikely to show
benefit). `MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.AlphaSpending` controls
the efficacy side with an alpha-spending budget. This file adds the futility side, controlled by
a **beta-spending** budget, and proves what the two boundaries jointly guarantee.

## The design

At look `j + 1` (`j < K`) the data give an efficacy p-value `p j` (valid under the null `μ`)
and a *futility p-value* `q j`, valid under a design alternative `ν`: `ν {q j ≤ t} ≤ t`. For a
`Z`-statistic with `Z j ~ N(θ₁ √I j, 1)` under the alternative, `q j = Φ(Z j - θ₁ √I j)` is
uniform under `ν`, and `q j ≤ d` means `Z j ≤ θ₁ √I j + Φ⁻¹(d)`: a small `q j` says the data
look much worse than the alternative predicts. With efficacy cutoffs `c` and futility cutoffs
`d`, each look first checks efficacy (`p j ≤ c j`: reject and stop), then futility
(`q j ≤ d j`: stop for futility), and otherwise continues. The trial ends in exactly one of
three ways (`rejectsWithFutility_or_stopsForFutility_or_continuesBefore` and the disjointness
lemmas): `RejectsWithFutility`, `StopsForFutility`, or `ContinuesBefore c d p q K` (all `K`
looks pass without stopping).

A beta-spending function `g` (`IsBetaSpendingFunction β g`: `g 0 = 0`, monotone on `[0, 1]`,
`g 1 ≤ β`) and information times `τ` give the futility cutoffs
`d = bonferroniLookLevel g τ`, the increments `g (τ (j + 1)) - g (τ j)`, which telescope to at
most `β`.

## Results

* **Non-binding futility keeps the type-I error.** The design rejects only if the
  efficacy-only design does (`RejectsWithFutility.rejectedLooks_nonempty`), so with
  alpha-spending efficacy cutoffs the type-I error is at most `α` for *every* futility rule
  `d`, `q`: ignoring a futility recommendation cannot inflate it
  (`measure_rejectsWithFutility_le`).
* **Beta spending bounds the futility-stop probability.** Under the alternative, the
  probability of stopping for futility is at most `β`, whatever the efficacy cutoffs
  (`measure_stopsForFutility_le`).
* **Power cost.** Every rejection the efficacy-only design makes and the design with futility
  misses is a futility stop (`rejectsWithFutility_or_stopsForFutility_of_nonempty`), so under
  the alternative the power drops by at most `β`
  (`measure_rejectedLooks_nonempty_le_rejectsWithFutility_add`) and the type-II error grows by
  at most `β` (`measure_not_rejectsWithFutility_le_add`).
* **Per-look futility levels can stop for futility with probability up to `K β`.** Testing
  futility at the same level `β` at each look can stop for futility with probability `2 β` over
  two looks (`exists_stopsForFutility_const_eq`): the spending budget, not the per-look level, is
  what bounds the futility-stop probability. This is sharpness for the futility-stop probability
  only: the witness has no efficacy rejections, so neither design has any power to lose.

## Scope

As in the alpha-spending file, the cutoffs are Bonferroni-type: the spending increment is used
directly as the cutoff on the p-value scale and the bound comes from the union bound, using
only the *marginal* validity of each look's futility p-value under `ν`. No joint law of the
looks is assumed. Exact beta-spending boundaries of Pampallona, Tsiatis and Kim, computed
recursively from the joint canonical law so that each increment is the exact first-crossing
probability, are less conservative and are not formalized here; neither is binding futility
(relaxing the efficacy cutoffs because futility stops are enforced).

## References

* S. Pampallona, A. A. Tsiatis, K. Kim, *Interim monitoring of group sequential trials using
  spending functions for the type I and type II error probabilities*, Drug Information Journal
  35 (2001).
* C. Jennison, B. W. Turnbull, *Group Sequential Methods with Applications to Clinical Trials*,
  Chapman & Hall/CRC (2000), Chapter 7.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Beta-spending functions -/

/-- `g` is a *beta-spending function* for type-II budget `β`: it spends nothing at information
time `0`, is monotone on `[0, 1]`, and has spent at most `β` at information time `1`. It has the
same shape as an alpha-spending function; the budget is spent on futility stops under the
alternative instead of rejections under the null.

Source: Pampallona, Tsiatis and Kim (2001). -/
abbrev IsBetaSpendingFunction (β : ℝ) (g : ℝ → ℝ) : Prop :=
  IsAlphaSpendingFunction β g

/-! ### Trial outcomes -/

/-- No look before look `j + 1` crossed either boundary: for every `i < j` the efficacy p-value
is above its cutoff (`c i < p i`) and the futility p-value is above its cutoff (`d i < q i`). -/
def ContinuesBefore (c d p q : ℕ → ℝ) (j : ℕ) : Prop :=
  ∀ i < j, c i < p i ∧ d i < q i

/-- The trial with efficacy cutoffs `c` and futility cutoffs `d` **rejects**: some planned look
`j < K` is reached without an earlier stop and its efficacy p-value is at most `c j`. -/
def RejectsWithFutility (K : ℕ) (c d p q : ℕ → ℝ) : Prop :=
  ∃ j < K, ContinuesBefore c d p q j ∧ p j ≤ c j

/-- The trial **stops for futility**: some planned look `j < K` is reached without an earlier
stop, does not reject (`c j < p j`), and its futility p-value is at most `d j`. -/
def StopsForFutility (K : ℕ) (c d p q : ℕ → ℝ) : Prop :=
  ∃ j < K, ContinuesBefore c d p q j ∧ c j < p j ∧ q j ≤ d j

section Outcomes

variable {K : ℕ} {c d p q : ℕ → ℝ}

/-- A rejection by the design with futility is a rejection by the efficacy-only design. -/
theorem RejectsWithFutility.rejectedLooks_nonempty (h : RejectsWithFutility K c d p q) :
    (rejectedLooks K c p).Nonempty := by
  obtain ⟨j, hj, -, hpj⟩ := h
  exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hpj⟩⟩

/-- A futility stop happens at a planned look whose futility p-value is at most its cutoff. -/
theorem StopsForFutility.rejectedLooks_nonempty (h : StopsForFutility K c d p q) :
    (rejectedLooks K d q).Nonempty := by
  obtain ⟨j, hj, -, -, hqj⟩ := h
  exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hqj⟩⟩

/-- The trial cannot both reject and stop for futility. -/
theorem not_rejectsWithFutility_and_stopsForFutility :
    ¬(RejectsWithFutility K c d p q ∧ StopsForFutility K c d p q) := by
  rintro ⟨⟨j, -, hj, hpj⟩, ⟨i, -, hi, hpi, hqi⟩⟩
  rcases lt_trichotomy j i with h | rfl | h
  · exact (hi j h).1.not_ge hpj
  · exact hpi.not_ge hpj
  · exact (hj i h).2.not_ge hqi

/-- A trial that passes all `K` looks does not reject. -/
theorem ContinuesBefore.not_rejectsWithFutility (h : ContinuesBefore c d p q K) :
    ¬RejectsWithFutility K c d p q := by
  rintro ⟨j, hj, -, hpj⟩
  exact (h j hj).1.not_ge hpj

/-- A trial that passes all `K` looks does not stop for futility. -/
theorem ContinuesBefore.not_stopsForFutility (h : ContinuesBefore c d p q K) :
    ¬StopsForFutility K c d p q := by
  rintro ⟨j, hj, -, -, hqj⟩
  exact (h j hj).2.not_ge hqj

/-- **Every trial ends in one of three ways**: it rejects, stops for futility, or passes all
`K` planned looks. -/
theorem rejectsWithFutility_or_stopsForFutility_or_continuesBefore (K : ℕ) (c d p q : ℕ → ℝ) :
    RejectsWithFutility K c d p q ∨ StopsForFutility K c d p q ∨ ContinuesBefore c d p q K := by
  classical
  by_cases hex : ∃ j, j < K ∧ (p j ≤ c j ∨ q j ≤ d j)
  · have hm := Nat.find_spec hex
    have hbefore : ContinuesBefore c d p q (Nat.find hex) := fun i hi => by
      have h := Nat.find_min hex hi
      push Not at h
      exact h (hi.trans hm.1)
    by_cases hp : p (Nat.find hex) ≤ c (Nat.find hex)
    · exact Or.inl ⟨_, hm.1, hbefore, hp⟩
    · exact Or.inr (Or.inl ⟨_, hm.1, hbefore, lt_of_not_ge hp, hm.2.resolve_left hp⟩)
  · push Not at hex
    exact Or.inr (Or.inr hex)

/-- **Rejections lost to futility are futility stops.** If the efficacy-only design rejects,
the design with futility either rejects or stops for futility. -/
theorem rejectsWithFutility_or_stopsForFutility_of_nonempty (h : (rejectedLooks K c p).Nonempty) :
    RejectsWithFutility K c d p q ∨ StopsForFutility K c d p q := by
  rcases rejectsWithFutility_or_stopsForFutility_or_continuesBefore K c d p q with
    hr | hs | hc
  · exact Or.inl hr
  · exact Or.inr hs
  · obtain ⟨j, hj⟩ := h
    rw [rejectedLooks, Finset.mem_filter, Finset.mem_range] at hj
    exact absurd hj.2 (hc j hj.1).1.not_ge

/-- If no planned look can reject, the trial stops for futility exactly when some look's
futility p-value is at most its cutoff. -/
theorem stopsForFutility_iff_of_forall_lt (h : ∀ k < K, c k < p k) :
    StopsForFutility K c d p q ↔ (rejectedLooks K d q).Nonempty := by
  refine ⟨StopsForFutility.rejectedLooks_nonempty, fun hq => ?_⟩
  obtain ⟨j, hj⟩ := hq
  rw [rejectedLooks, Finset.mem_filter, Finset.mem_range] at hj
  rcases rejectsWithFutility_or_stopsForFutility_or_continuesBefore K c d p q with
    hr | hs | hc
  · obtain ⟨i, hi, -, hpi⟩ := hr
    exact absurd hpi (h i hi).not_ge
  · exact hs
  · exact absurd hj.2 (hc j hj.1).2.not_ge

end Outcomes

/-! ### Error and power guarantees -/

section Control

variable {α β : ℝ} {f g : ℝ → ℝ} {τ : ℕ → ℝ} {K : ℕ}

/-- **Non-binding futility keeps the type-I error at `α`.** With alpha-spending efficacy
cutoffs and efficacy p-values valid under the null `μ`, the design rejects with probability at
most `α` under `μ`, for every futility cutoff `d` and futility p-value `q`.

Source: Jennison and Turnbull (2000), Chapter 7. -/
theorem measure_rejectsWithFutility_le (μ : Measure Ω) (p q : ℕ → Ω → ℝ) (d : ℕ → ℝ)
    (hf : IsAlphaSpendingFunction α f) (hα : α ≤ 1) (hτ0 : τ 0 = 0) (hτ : Monotone τ)
    (hτK : τ K ≤ 1) (hnull : ∀ k < K, IsValidPValue μ (p k)) :
    μ {ω | RejectsWithFutility K (bonferroniLookLevel f τ) d (fun k => p k ω)
        fun k => q k ω} ≤ ENNReal.ofReal α :=
  (measure_mono fun _ hω => RejectsWithFutility.rejectedLooks_nonempty hω).trans
    (measure_rejectedLooks_bonferroniLookLevel_nonempty_le μ p hf hα hτ0 hτ hτK hnull)

/-- **Beta spending bounds the futility-stop probability.** With beta-spending futility cutoffs
and futility p-values valid under the alternative `ν`, the trial stops for futility with
probability at most `β` under `ν`, for every efficacy cutoff `c` and efficacy p-value `p`.

Source: Pampallona, Tsiatis and Kim (2001). -/
theorem measure_stopsForFutility_le (ν : Measure Ω) (p q : ℕ → Ω → ℝ) (c : ℕ → ℝ)
    (hg : IsBetaSpendingFunction β g) (hβ : β ≤ 1) (hτ0 : τ 0 = 0) (hτ : Monotone τ)
    (hτK : τ K ≤ 1) (halt : ∀ k < K, IsValidPValue ν (q k)) :
    ν {ω | StopsForFutility K c (bonferroniLookLevel g τ) (fun k => p k ω)
        fun k => q k ω} ≤ ENNReal.ofReal β :=
  (measure_mono fun _ hω => StopsForFutility.rejectedLooks_nonempty hω).trans
    (measure_rejectedLooks_bonferroniLookLevel_nonempty_le ν q hg hβ hτ0 hτ hτK halt)

/-- **Futility costs at most `β` power.** Under the alternative `ν`, the efficacy-only design
with cutoffs `c` rejects with probability at most that of the design with beta-spending
futility cutoffs, plus `β`. -/
theorem measure_rejectedLooks_nonempty_le_rejectsWithFutility_add (ν : Measure Ω)
    (p q : ℕ → Ω → ℝ) (c : ℕ → ℝ) (hg : IsBetaSpendingFunction β g) (hβ : β ≤ 1)
    (hτ0 : τ 0 = 0) (hτ : Monotone τ) (hτK : τ K ≤ 1)
    (halt : ∀ k < K, IsValidPValue ν (q k)) :
    ν {ω | (rejectedLooks K c fun k => p k ω).Nonempty} ≤
      ν {ω | RejectsWithFutility K c (bonferroniLookLevel g τ) (fun k => p k ω)
          fun k => q k ω} + ENNReal.ofReal β := by
  refine (measure_mono (t :=
      {ω | RejectsWithFutility K c (bonferroniLookLevel g τ) (fun k => p k ω) fun k => q k ω} ∪
      {ω | StopsForFutility K c (bonferroniLookLevel g τ) (fun k => p k ω) fun k => q k ω})
    fun _ hω => rejectsWithFutility_or_stopsForFutility_of_nonempty hω).trans
    ((measure_union_le _ _).trans ?_)
  gcongr
  exact measure_stopsForFutility_le ν p q c hg hβ hτ0 hτ hτK halt

/-- **Futility adds at most `β` type-II error.** Under the alternative `ν`, the design with
beta-spending futility cutoffs fails to reject with probability at most that of the
efficacy-only design, plus `β`. -/
theorem measure_not_rejectsWithFutility_le_add (ν : Measure Ω) (p q : ℕ → Ω → ℝ) (c : ℕ → ℝ)
    (hg : IsBetaSpendingFunction β g) (hβ : β ≤ 1) (hτ0 : τ 0 = 0) (hτ : Monotone τ)
    (hτK : τ K ≤ 1) (halt : ∀ k < K, IsValidPValue ν (q k)) :
    ν {ω | ¬RejectsWithFutility K c (bonferroniLookLevel g τ) (fun k => p k ω)
        fun k => q k ω} ≤
      ν {ω | ¬(rejectedLooks K c fun k => p k ω).Nonempty} + ENNReal.ofReal β := by
  refine (measure_mono (t := {ω | ¬(rejectedLooks K c fun k => p k ω).Nonempty} ∪
      {ω | StopsForFutility K c (bonferroniLookLevel g τ) (fun k => p k ω) fun k => q k ω})
    fun ω hω => ?_).trans ((measure_union_le _ _).trans ?_)
  · by_cases hne : (rejectedLooks K c fun k => p k ω).Nonempty
    · exact Or.inr ((rejectsWithFutility_or_stopsForFutility_of_nonempty hne).resolve_left hω)
    · exact Or.inl hne
  · gcongr
    exact measure_stopsForFutility_le ν p q c hg hβ hτ0 hτ hτK halt

end Control

/-! ### Per-look futility levels -/

/-- **Computed futility-stop example.** On four equally likely outcomes, two looks with futility
p-values valid under `ν`, each tested at the per-look level `1/4` and with no efficacy
rejection possible, stop for futility with probability `2 · 1/4 = 1/2`: twice the per-look
level. A beta-spending budget of `1/4` would cap this at `1/4`. Since no efficacy rejection is
possible, this concerns the futility-stop probability only, not power. -/
theorem exists_stopsForFutility_const_eq :
    ∃ (ν : Measure (Fin 4)) (q : ℕ → Fin 4 → ℝ), IsProbabilityMeasure ν ∧
      (∀ k < 2, IsValidPValue ν (q k)) ∧
      ν {ω | StopsForFutility 2 (fun _ => 0) (fun _ => 1 / 4) (fun _ => 1) fun k => q k ω} =
        ENNReal.ofReal (2 * (1 / 4)) ∧
      ENNReal.ofReal (1 / 4) < ENNReal.ofReal (2 * (1 / 4)) := by
  obtain ⟨ν, q, hν, hq, heq, hlt⟩ := exists_rejectedLooks_const_typeI_eq
  refine ⟨ν, q, hν, hq, ?_, hlt⟩
  have hset : {ω | StopsForFutility 2 (fun _ => 0) (fun _ => 1 / 4) (fun _ => 1)
      fun k => q k ω} = {ω | (rejectedLooks 2 (fun _ => 1 / 4) fun k => q k ω).Nonempty} := by
    ext ω
    exact stopsForFutility_iff_of_forall_lt fun _ _ => zero_lt_one
  rw [hset, heq]

end MathlibExt.Probability.Statistics.MultipleTesting
