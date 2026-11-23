/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.SplitConformal
public import MathlibExt.Probability.Distributions.BetaBinomial
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.Independence.Basic

import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Order.Interval.Finset.Fin

/-!
# The rank of a sample order statistic is beta-binomial

Let `m + 1` labelled *real* scores and `N` labelled *synthetic* scores be independent draws from a
common atomless law `ν` on `ℝ`. Fix `1 ≤ r ≤ m + 1`, let `S₍ᵣ₎` be the `r`-th smallest real score,
`J` the number of synthetic scores strictly below `S₍ᵣ₎` and `K = J + 1`. Then `K - 1` follows the
beta-binomial law with `N` trials and parameters `r` and `m + 2 - r`:

`P(K = k) = BB(N; r, m + 2 - r)(k - 1)
  = C(k + r - 2, r - 1) C(N + m + 2 - k - r, m + 1 - r) / C(N + m + 1, m + 1)`, `k = 1, …, N + 1`,

so `E K = 1 + N r / (m + 2)`, and for the synthetic order statistics `S̃₍ₐ₎` with the sentinels
`S̃₍₀₎ = -∞`, `S̃₍N+1₎ = +∞`, and `0 ≤ a < b ≤ N + 1`,
`P(S̃₍ₐ₎ ≤ S₍ᵣ₎ ≤ S̃₍b₎) = F(b) - F(a)` with `F(t) = P(K ≤ t)`.

The scores are the coordinates of `ω : Fin (m + 1) ⊕ Fin N → ℝ` (`Sum.inl i` real, `Sum.inr s`
synthetic) under the product measure `Measure.pi fun _ => ν`, with the product Borel σ-algebra.
Atomlessness (`NullSingletonClass ν`) is used only to make ties a null event; no density is
assumed. The rank and window event identities hold on the event of distinct scores (almost
surely), not on ties.

The proof first treats any law that is invariant under coordinate permutations and has almost
surely distinct coordinates. Averaging over `Equiv.Perm`, with the shared lemma
`MultipleTesting.measure_eq_card_div_of_ae_card_filter_smul_mem_eq`,
reduces the law of `J` to counting the positions of the real scores among the sorted pooled
scores, a uniform `(m + 1)`-subset of the `m + 1 + N` positions. The `r`-th real score sits at
position `p = r - 1 + J`, which gives the binomial ratio, and the ratio equals the existing
`ProbabilityTheory.betaBinomialPMF`. The i.i.d. law is then shown to be permutation invariant
(`map_comp_perm_pi`) with almost surely distinct coordinates (`ae_injective_pi`).

## Main definitions

* `realOrderStatistic r ω`: `S₍ᵣ₎`, the `r`-th smallest real score (with multiplicity).
* `syntheticOrderStatistic a ω`: `S̃₍ₐ₎`, the `a`-th smallest synthetic score; it is `⊤` for
  `a = N + 1`.
* `sampleRank r ω`: `J`, the number of synthetic scores strictly below `S₍ᵣ₎`.

## Main results

* `sampleRank_eq_card`: the count formula for `J`, valid for every score vector, ties included.
* `choose_mul_choose_div_choose_eq_betaBinomialPMF`: the binomial ratio equals the beta-binomial
  mass.
* `measureReal_sampleRank_eq_of_exchangeable`: the beta-binomial law of `J` for exchangeable
  scores without ties.
* `map_comp_perm_pi`, `ae_injective_pi`: i.i.d. atomless scores are exchangeable and almost surely
  distinct.
* `measureReal_sampleRank_add_one_eq`, `measureReal_sampleRank_add_one_eq_choose`: the law of `K`
  for i.i.d. atomless scores, as a beta-binomial mass and as a binomial ratio.
* `measureReal_sampleRank_add_one_le`: the distribution function `F` of `K`.
* `integral_sampleRank_add_one`: `E K = 1 + N r / (m + 2)`.
* `window_iff_of_injective`, `measureReal_window`: the window event for distinct scores and its
  probability `F(b) - F(a)`.

Atomlessness enters as `NullSingletonClass ν` (every singleton is `ν`-null, i.e. `ν` has no point
masses and a continuous distribution function); `MeasureTheory.IsAtomless.nullSingletonClass`
derives it from `MeasureTheory.IsAtomless`. The total-variation and worst-case statements of the
source setting, Pólya-urn or Dirichlet representations and the variance of `K` are not formalized
here.
-/

@[expose] public section

namespace MathlibExt.Probability.Distributions.BetaBinomialSampleRank

open MeasureTheory Finset ProbabilityTheory MathlibExt.Probability.Statistics.SplitConformal
  MathlibExt.Probability.Statistics.MultipleTesting

section Interleaving

/-! ### Positions of the real scores among the sorted pooled scores -/

variable {M : ℕ}

/-- The number of positions outside `S` that have fewer than `r` elements of `S` at or below
them. When `S` is the set of positions of the real scores among the sorted pooled scores, this is
the number of synthetic scores below the `r`-th real score. -/
private noncomputable def gapCount (r : ℕ) (S : Finset (Fin M)) : ℕ :=
  (univ.filter fun q => q ∉ S ∧ (S.filter (· ≤ q)).card < r).card

private theorem gapCount_add_eq {r : ℕ} (hr : 1 ≤ r) {S : Finset (Fin M)} {p : Fin M}
    (hp : p ∈ S) (hpr : (S.filter (· < p)).card = r - 1) :
    gapCount r S + (r - 1) = p := by
  have hcond : ∀ q, q ∉ S → ((S.filter (· ≤ q)).card < r ↔ q < p) := by
    intro q hq
    constructor
    · intro h
      by_contra hle
      push Not at hle
      have hpq : p < q := lt_of_le_of_ne hle (fun h' => hq (h' ▸ hp))
      have hsub : insert p (S.filter (· < p)) ⊆ S.filter (· ≤ q) := by
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact Finset.mem_filter.2 ⟨hp, hpq.le⟩
        · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hx).1,
            ((Finset.mem_filter.1 hx).2.trans hpq).le⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simp), hpr] at hcard
      omega
    · intro hqp
      have hsub : S.filter (· ≤ q) ⊆ S.filter (· < p) := fun x hx =>
        Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hx).1, (Finset.mem_filter.1 hx).2.trans_lt hqp⟩
      have := Finset.card_le_card hsub
      omega
  have hgap : gapCount r S = ((Finset.Iio p).filter fun q => q ∉ S).card := by
    unfold gapCount
    congr 1
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    constructor
    · rintro ⟨hq, h⟩
      exact ⟨(hcond q hq).1 h, hq⟩
    · rintro ⟨h, hq⟩
      exact ⟨hq, (hcond q hq).2 h⟩
  have hin : (Finset.Iio p).filter (fun q => q ∈ S) = S.filter (· < p) := by
    ext q
    simp [and_comm]
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.Iio p)
    (fun q => q ∈ S)
  rw [hin, hpr, Fin.card_Iio] at hsplit
  rw [hgap]
  omega

/-- Some element of a set of size `m + 1` has exactly `r - 1` elements of the set below it. -/
private theorem exists_card_filter_lt_eq {m r : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m + 1)
    {S : Finset (Fin M)} (hS : S.card = m + 1) :
    ∃ x ∈ S, (S.filter (· < x)).card = r - 1 := by
  have hf : ∀ a ∈ S, (S.filter (· < a)).card ∈ Finset.range (m + 1) := by
    intro a ha
    rw [Finset.mem_range]
    have hsub : S.filter (· < a) ⊆ S.erase a := fun x hx =>
      Finset.mem_erase.2 ⟨(Finset.mem_filter.1 hx).2.ne, (Finset.mem_filter.1 hx).1⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem ha, hS] at this
    omega
  have hinj : ∀ a₁ a₂ (ha₁ : a₁ ∈ S) (ha₂ : a₂ ∈ S),
      (S.filter (· < a₁)).card = (S.filter (· < a₂)).card → a₁ = a₂ := by
    have hlt : ∀ a₁ a₂, a₂ ∈ S → a₂ < a₁ →
        (S.filter (· < a₂)).card < (S.filter (· < a₁)).card := by
      intro a₁ a₂ ha₂ h
      refine Finset.card_lt_card ⟨fun x hx => Finset.mem_filter.2
        ⟨(Finset.mem_filter.1 hx).1, (Finset.mem_filter.1 hx).2.trans h⟩, fun hsub => ?_⟩
      have := (Finset.mem_filter.1 (hsub (Finset.mem_filter.2 ⟨ha₂, h⟩))).2
      exact lt_irrefl _ this
    intro a₁ a₂ ha₁ ha₂ h
    rcases lt_trichotomy a₁ a₂ with h' | h' | h'
    · exact absurd h (hlt a₂ a₁ ha₁ h').ne
    · exact h'
    · exact absurd h (hlt a₁ a₂ ha₂ h').ne'
  obtain ⟨x, hx, hxr⟩ := Finset.surj_on_of_inj_on_of_card_le
    (fun a _ => (S.filter (· < a)).card) hf hinj (by simp [hS]) (r - 1)
    (Finset.mem_range.2 (by omega))
  exact ⟨x, hx, hxr.symm⟩

/-- For a set `S` of `m + 1` positions, the gap count is `j` exactly when position
`p = r - 1 + j` lies in `S` with `r - 1` elements of `S` below it. -/
private theorem gapCount_eq_iff {m r j : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m + 1)
    {S : Finset (Fin M)} (hS : S.card = m + 1) {p : Fin M} (hp : (p : ℕ) = r - 1 + j) :
    gapCount r S = j ↔ p ∈ S ∧ (S.filter (· < p)).card = r - 1 := by
  constructor
  · intro h
    obtain ⟨x, hx, hxr⟩ := exists_card_filter_lt_eq hr hrm hS
    have := gapCount_add_eq hr hx hxr
    have hxp : x = p := Fin.ext (by omega)
    subst hxp
    exact ⟨hx, hxr⟩
  · rintro ⟨hpS, hpr⟩
    have := gapCount_add_eq hr hpS hpr
    omega

/-- The number of `(m + 1)`-subsets of `Fin M` with position `p` in the subset and `r - 1`
elements below it is `C(p, r - 1) C(M - 1 - p, m + 1 - r)`. -/
private theorem card_filter_mem_card_filter_lt_eq {m r : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m + 1)
    (p : Fin M) :
    ((Finset.powersetCard (m + 1) (univ : Finset (Fin M))).filter
        fun S => p ∈ S ∧ (S.filter (· < p)).card = r - 1).card =
      (p : ℕ).choose (r - 1) * (M - 1 - p).choose (m + 1 - r) := by
  rw [← Fin.card_Ioi p, ← Fin.card_Iio p, ← Finset.card_powersetCard, ← Finset.card_powersetCard,
    ← Finset.card_product]
  have hsplit : ∀ S : Finset (Fin M), p ∈ S →
      S.card = (S.filter (· < p)).card + 1 + (S.filter (p < ·)).card := by
    intro S hpS
    have h1 := Finset.card_filter_add_card_filter_not (s := S) (· < p)
    have h2 := Finset.card_filter_add_card_filter_not
      (s := S.filter fun x => ¬ x < p) (· = p)
    have h3 : (S.filter fun x => ¬ x < p).filter (· = p) = {p} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h⟩
        exact h
      · rintro rfl
        exact ⟨⟨hpS, lt_irrefl _⟩, rfl⟩
    have h4 : (S.filter fun x => ¬ x < p).filter (fun x => ¬ x = p) = S.filter (p < ·) := by
      ext x
      simp only [Finset.mem_filter, not_lt]
      constructor
      · rintro ⟨⟨hx, h⟩, h'⟩
        exact ⟨hx, lt_of_le_of_ne h (Ne.symm h')⟩
      · rintro ⟨hx, h⟩
        exact ⟨⟨hx, h.le⟩, h.ne'⟩
    rw [h3, h4, Finset.card_singleton] at h2
    omega
  refine Finset.card_bij' (fun S _ => (S.filter (· < p), S.filter (p < ·)))
    (fun AB _ => insert p (AB.1 ∪ AB.2)) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS
    obtain ⟨⟨-, hcard⟩, hpS, hpr⟩ := hS
    have := hsplit S hpS
    simp only [Finset.mem_product, Finset.mem_powersetCard]
    refine ⟨⟨fun x hx => Finset.mem_Iio.2 (Finset.mem_filter.1 hx).2, hpr⟩,
      ⟨fun x hx => Finset.mem_Ioi.2 (Finset.mem_filter.1 hx).2, by omega⟩⟩
  · intro AB hAB
    simp only [Finset.mem_product, Finset.mem_powersetCard] at hAB
    obtain ⟨⟨hA, hAc⟩, ⟨hB, hBc⟩⟩ := hAB
    have hdisj : Disjoint AB.1 AB.2 := Finset.disjoint_left.2 fun x hx hx' =>
      lt_asymm (Finset.mem_Iio.1 (hA hx)) (Finset.mem_Ioi.1 (hB hx'))
    have hpn : p ∉ AB.1 ∪ AB.2 := by
      intro h
      rcases Finset.mem_union.1 h with h | h
      · exact lt_irrefl _ (Finset.mem_Iio.1 (hA h))
      · exact lt_irrefl _ (Finset.mem_Ioi.1 (hB h))
    have hfilt : (insert p (AB.1 ∪ AB.2)).filter (· < p) = AB.1 := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro ⟨h | h | h, hx⟩
        · exact absurd hx (h ▸ lt_irrefl _)
        · exact h
        · exact absurd hx (lt_asymm (Finset.mem_Ioi.1 (hB h)))
      · intro h
        exact ⟨Or.inr (Or.inl h), Finset.mem_Iio.1 (hA h)⟩
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.mem_insert_self _ _, by rw [hfilt, hAc]⟩
    rw [Finset.card_insert_of_notMem hpn, Finset.card_union_of_disjoint hdisj, hAc, hBc]
    omega
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS
    ext x
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (rfl | ⟨hx, _⟩ | ⟨hx, _⟩)
      · exact hS.2.1
      · exact hx
      · exact hx
    · intro hx
      rcases lt_trichotomy x p with h | h | h
      · exact Or.inr (Or.inl ⟨hx, h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨hx, h⟩)
  · intro AB hAB
    simp only [Finset.mem_product, Finset.mem_powersetCard] at hAB
    obtain ⟨⟨hA, -⟩, ⟨hB, -⟩⟩ := hAB
    ext x
    · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro ⟨h | h | h, hx⟩
        · exact absurd hx (h ▸ lt_irrefl _)
        · exact h
        · exact absurd hx (lt_asymm (Finset.mem_Ioi.1 (hB h)))
      · intro h
        exact ⟨Or.inr (Or.inl h), Finset.mem_Iio.1 (hA h)⟩
    · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro ⟨h | h | h, hx⟩
        · exact absurd hx (h ▸ lt_irrefl _)
        · exact absurd hx (lt_asymm (Finset.mem_Iio.1 (hA h)))
        · exact h
      · intro h
        exact ⟨Or.inr (Or.inr h), Finset.mem_Ioi.1 (hB h)⟩

end Interleaving

section SampleRank

variable {m N : ℕ}

/-- **The `r`-th real order statistic.** `S₍ᵣ₎` is the `r`-th smallest of the real scores
`ω (Sum.inl i)`, counted with multiplicity (`orderStatistic`). It is finite for
`1 ≤ r ≤ m + 1` (`exists_realOrderStatistic_eq`). -/
noncomputable def realOrderStatistic (r : ℕ) (ω : Fin (m + 1) ⊕ Fin N → ℝ) : WithTop ℝ :=
  orderStatistic (fun i => ω (Sum.inl i)) r

/-- **The `a`-th synthetic order statistic.** `S̃₍ₐ₎` is the `a`-th smallest of the synthetic
scores `ω (Sum.inr s)`, counted with multiplicity. For `a = N + 1` it is `⊤`, the `+∞` sentinel
(`syntheticOrderStatistic_succ_eq_top`); the `-∞` sentinel `a = 0` is handled separately in
`measureReal_window`. -/
noncomputable def syntheticOrderStatistic (a : ℕ) (ω : Fin (m + 1) ⊕ Fin N → ℝ) : WithTop ℝ :=
  orderStatistic (fun s => ω (Sum.inr s)) a

/-- **The sample rank.** `J` is the number of synthetic scores strictly below the `r`-th real order
statistic `S₍ᵣ₎`; the rank of `S₍ᵣ₎` among the synthetic scores is `K = J + 1`. -/
noncomputable def sampleRank (r : ℕ) (ω : Fin (m + 1) ⊕ Fin N → ℝ) : ℕ :=
  (univ.filter fun s : Fin N => (ω (Sum.inr s) : WithTop ℝ) < realOrderStatistic r ω).card

/-- **The sample rank is at most `N`.** At most all `N` synthetic scores lie below `S₍ᵣ₎`. -/
theorem sampleRank_le (r : ℕ) (ω : Fin (m + 1) ⊕ Fin N → ℝ) : sampleRank r ω ≤ N :=
  (Finset.card_filter_le _ _).trans (by simp)

/-- **Count formula for the sample rank.** For `1 ≤ r`, a synthetic score lies strictly below
`S₍ᵣ₎` iff fewer than `r` real scores are at most it. This holds for every score vector, ties
included. -/
theorem sampleRank_eq_card {r : ℕ} (hr : 1 ≤ r) (ω : Fin (m + 1) ⊕ Fin N → ℝ) :
    sampleRank r ω = (univ.filter fun s : Fin N =>
      (univ.filter fun i : Fin (m + 1) => ω (Sum.inl i) ≤ ω (Sum.inr s)).card < r).card := by
  unfold sampleRank realOrderStatistic
  refine congrArg Finset.card (Finset.filter_congr fun s _ => ?_)
  rw [← not_le, orderStatistic_le_coe_iff hr, not_le]

/-- **Measurability of the sample rank.** `J` is measurable for the product Borel σ-algebra on the
score space. -/
theorem measurable_sampleRank {r : ℕ} (hr : 1 ≤ r) :
    Measurable (sampleRank r : (Fin (m + 1) ⊕ Fin N → ℝ) → ℕ) := by
  have hfun : (sampleRank r : (Fin (m + 1) ⊕ Fin N → ℝ) → ℕ) = fun ω => ∑ s : Fin N,
      if (∑ i : Fin (m + 1), if ω (Sum.inl i) ≤ ω (Sum.inr s) then 1 else 0) < r then 1 else 0 := by
    funext ω
    rw [sampleRank_eq_card hr, Finset.card_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.card_filter]
  rw [hfun]
  refine Finset.measurable_sum _ fun s _ => ?_
  have hin : Measurable fun ω : Fin (m + 1) ⊕ Fin N → ℝ =>
      ∑ i : Fin (m + 1), if ω (Sum.inl i) ≤ ω (Sum.inr s) then 1 else 0 := by
    refine Finset.measurable_sum _ fun i _ => ?_
    exact Measurable.ite (measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _))
      measurable_const measurable_const
  exact Measurable.ite (hin (MeasurableSet.of_discrete (s := {n : ℕ | n < r})))
    measurable_const measurable_const

/-- A vector of distinct reals is ranked by an equivalence with `Fin n` that preserves order. -/
private theorem exists_rankEquiv {ι : Type*} [Fintype ι] {n : ℕ} (hn : Fintype.card ι = n)
    {ω : ι → ℝ} (hω : Function.Injective ω) :
    ∃ e : ι ≃ Fin n, ∀ a b, ω a ≤ ω b ↔ e a ≤ e b := by
  classical
  have hcard : ∀ a, (univ.filter fun b => ω b < ω a).card < n := by
    intro a
    rw [← hn]
    refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h => ?_⟩
    have := Finset.mem_filter.1 (h (Finset.mem_univ a))
    exact lt_irrefl _ this.2
  let f : ι → Fin n := fun a => ⟨(univ.filter fun b => ω b < ω a).card, hcard a⟩
  have hlt : ∀ a b, ω a < ω b → f a < f b := by
    intro a b hab
    rw [Fin.lt_def]
    refine Finset.card_lt_card ⟨fun c hc => ?_, fun h => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact hc.trans hab
    · have := Finset.mem_filter.1 (h (Finset.mem_filter.2 ⟨Finset.mem_univ a, hab⟩))
      exact lt_irrefl _ this.2
  have hiff : ∀ a b, ω a ≤ ω b ↔ f a ≤ f b := by
    intro a b
    constructor
    · intro h
      rcases h.lt_or_eq with h | h
      · exact (hlt a b h).le
      · rw [hω h]
    · intro h
      by_contra h'
      push Not at h'
      exact absurd h (not_le.2 (hlt b a h'))
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne (hω.ne hne) with h | h
    · exact absurd hab (hlt a b h).ne
    · exact absurd hab (hlt b a h).ne'
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, by simp [hn]⟩
  exact ⟨Equiv.ofBijective f hbij, hiff⟩

/-- The sample rank of a labelling `τ` of the pooled positions by the scores. -/
private noncomputable def rankCount (r : ℕ) (τ : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N)) : ℕ :=
  (univ.filter fun s : Fin N =>
    (univ.filter fun i : Fin (m + 1) => τ (Sum.inl i) ≤ τ (Sum.inr s)).card < r).card

/-- The positions of the real scores under the labelling `τ`. -/
private noncomputable def realPositions (τ : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N)) :
    Finset (Fin (m + 1 + N)) :=
  univ.image fun i => τ (Sum.inl i)

private theorem card_realPositions (τ : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N)) :
    (realPositions τ).card = m + 1 := by
  have hinl : Function.Injective fun i : Fin (m + 1) => τ (Sum.inl i) :=
    τ.injective.comp Sum.inl_injective
  rw [realPositions, Finset.card_image_of_injective _ hinl]
  simp

private theorem rankCount_eq_gapCount (r : ℕ) (τ : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N)) :
    rankCount r τ = gapCount r (realPositions τ) := by
  have hinner : ∀ q, ((realPositions τ).filter (· ≤ q)).card =
      (univ.filter fun i : Fin (m + 1) => τ (Sum.inl i) ≤ q).card := by
    intro q
    have hinl : Function.Injective fun i : Fin (m + 1) => τ (Sum.inl i) :=
      τ.injective.comp Sum.inl_injective
    rw [realPositions, Finset.filter_image, Finset.card_image_of_injective _ hinl]
  have hmem : ∀ q, q ∉ realPositions τ ↔ ∃ s, τ (Sum.inr s) = q := by
    intro q
    constructor
    · intro hq
      rcases h : τ.symm q with i | s
      · exact absurd (Finset.mem_image.2 ⟨i, Finset.mem_univ _, by rw [← h]; simp⟩) hq
      · exact ⟨s, by rw [← h]; simp⟩
    · rintro ⟨s, rfl⟩ hmem
      obtain ⟨i, _, hi⟩ := Finset.mem_image.1 hmem
      exact Sum.inl_ne_inr (τ.injective hi)
  have hset : (univ.filter fun q => q ∉ realPositions τ ∧
      ((realPositions τ).filter (· ≤ q)).card < r) =
      (univ.filter fun s : Fin N =>
        (univ.filter fun i : Fin (m + 1) => τ (Sum.inl i) ≤ τ (Sum.inr s)).card < r).image
          fun s => τ (Sum.inr s) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hinner]
    constructor
    · rintro ⟨hq, hc⟩
      obtain ⟨s, rfl⟩ := (hmem q).1 hq
      exact ⟨s, hc, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨(hmem _).2 ⟨s, rfl⟩, hs⟩
  unfold rankCount gapCount
  have hinr : Function.Injective fun s : Fin N => τ (Sum.inr s) :=
    τ.injective.comp Sum.inr_injective
  rw [hset, Finset.card_image_of_injective _ hinr]

/-- Labellings with a given set of real positions: their number does not depend on the set,
among sets of the same size. -/
private theorem card_fiber_le {S S' : Finset (Fin (m + 1 + N))} (hS : S.card = S'.card) :
    (univ.filter fun τ : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N) => realPositions τ = S).card ≤
      (univ.filter fun τ : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N) =>
        realPositions τ = S').card := by
  classical
  have h1 : Fintype.card {x // x ∈ S} = Fintype.card {x // x ∈ S'} := by simp [hS]
  have h2 : Fintype.card {x // x ∉ S} = Fintype.card {x // x ∉ S'} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]
    simp [hS]
  let ρ : Equiv.Perm (Fin (m + 1 + N)) :=
    Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2)
  have hρ : ∀ x, ρ x ∈ S' ↔ x ∈ S := by
    intro x
    by_cases hx : x ∈ S
    · have : ρ x = (Fintype.equivOfCardEq h1 ⟨x, hx⟩ : Fin (m + 1 + N)) := by
        simp [ρ, Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos hx]
      rw [this]
      exact ⟨fun _ => hx, fun _ => (Fintype.equivOfCardEq h1 ⟨x, hx⟩).2⟩
    · have : ρ x = (Fintype.equivOfCardEq h2 ⟨x, hx⟩ : Fin (m + 1 + N)) := by
        simp [ρ, Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_neg hx]
      rw [this]
      exact ⟨fun h => absurd h (Fintype.equivOfCardEq h2 ⟨x, hx⟩).2, fun h => absurd h hx⟩
  refine Finset.card_le_card_of_injOn (fun τ => τ.trans ρ) (fun τ hτ => ?_) (fun τ _ τ' _ h => ?_)
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hτ ⊢
    have hsub : realPositions (τ.trans ρ) ⊆ S' := by
      intro y hy
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hy
      rw [Equiv.trans_apply, hρ, ← hτ]
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
    exact Finset.eq_of_subset_of_card_le hsub (by rw [card_realPositions, ← hS, ← hτ,
      card_realPositions])
  · ext x
    have := congrArg (fun f : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N) => ρ.symm (f x)) h
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at this
    rw [this]

/-- Every set of `m + 1` positions carries the same number `c₀` of labellings, and
`C(m + 1 + N, m + 1) c₀ = (m + 1 + N)!`. -/
private theorem choose_mul_card_fiber {S₀ : Finset (Fin (m + 1 + N))} (hS₀ : S₀.card = m + 1) :
    (m + 1 + N).choose (m + 1) *
      (univ.filter fun τ : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N) => realPositions τ = S₀).card =
      (m + 1 + N).factorial := by
  have htot := Finset.card_eq_sum_card_fiberwise
    (s := (univ : Finset (Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N))))
    (t := Finset.powersetCard (m + 1) (univ : Finset (Fin (m + 1 + N))))
    (f := realPositions) (fun τ _ => Finset.mem_powersetCard.2
      ⟨Finset.subset_univ _, card_realPositions τ⟩)
  have hconst : ∀ S ∈ Finset.powersetCard (m + 1) (univ : Finset (Fin (m + 1 + N))),
      (univ.filter fun τ : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N) => realPositions τ = S).card =
      (univ.filter fun τ : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N) =>
        realPositions τ = S₀).card := by
    intro S hS
    have hc := (Finset.mem_powersetCard.1 hS).2
    exact le_antisymm (card_fiber_le (hc.trans hS₀.symm)) (card_fiber_le (hS₀.trans hc.symm))
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard, Finset.card_fin,
    smul_eq_mul, Finset.card_univ,
    Fintype.card_equiv (finSumFinEquiv : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N)),
    Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at htot
  exact htot.symm

/-- The number of labellings with sample rank `j` is the number of good position sets times the
common fibre size. -/
private theorem card_rankCount_eq {r j : ℕ} {S₀ : Finset (Fin (m + 1 + N))}
    (hS₀ : S₀.card = m + 1) :
    (univ.filter fun τ : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N) => rankCount r τ = j).card =
      ((Finset.powersetCard (m + 1) (univ : Finset (Fin (m + 1 + N)))).filter
          fun S => gapCount r S = j).card *
        (univ.filter fun τ : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N) =>
          realPositions τ = S₀).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := realPositions)
    (t := Finset.powersetCard (m + 1) (univ : Finset (Fin (m + 1 + N))))
    (fun τ _ => Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, card_realPositions τ⟩)]
  have hterm : ∀ S ∈ Finset.powersetCard (m + 1) (univ : Finset (Fin (m + 1 + N))),
      ((univ.filter fun τ : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N) => rankCount r τ = j).filter
          fun τ => realPositions τ = S).card =
        if gapCount r S = j then
          (univ.filter fun τ : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N) =>
            realPositions τ = S₀).card else 0 := by
    intro S hS
    have hc := (Finset.mem_powersetCard.1 hS).2
    split_ifs with hg
    · rw [← le_antisymm (card_fiber_le (hc.trans hS₀.symm)) (card_fiber_le (hS₀.trans hc.symm))]
      congr 1
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨by rw [rankCount_eq_gapCount, h, hg], h⟩
    · rw [Finset.card_eq_zero]
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_and]
      intro h h'
      exact hg (by rw [← h', ← rankCount_eq_gapCount, h])
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]

open Classical in
/-- For distinct scores, the number of coordinate permutations giving sample rank `j` does not
depend on the scores: it is the number of labellings of the pooled positions with sample
rank `j`. -/
private theorem card_filter_sampleRank_smul_eq {r : ℕ} (hr : 1 ≤ r)
    {ω : Fin (m + 1) ⊕ Fin N → ℝ} (hω : Function.Injective ω) (j : ℕ) :
    (univ.filter fun σ : Equiv.Perm (Fin (m + 1) ⊕ Fin N) =>
        σ • ω ∈ {ω | sampleRank r ω = j}).card =
      (univ.filter fun τ : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N) => rankCount r τ = j).card := by
  obtain ⟨e, he⟩ := exists_rankEquiv (n := m + 1 + N) (by simp) hω
  have hrank : ∀ σ : Equiv.Perm (Fin (m + 1) ⊕ Fin N),
      sampleRank r (σ • ω) = rankCount r ((σ⁻¹ : Equiv.Perm _).trans e) := by
    intro σ
    rw [sampleRank_eq_card hr, rankCount]
    simp only [coordinatePermAction_smul_apply, Equiv.trans_apply, he]
    rfl
  refine Finset.card_bij' (fun σ _ => (σ⁻¹ : Equiv.Perm _).trans e)
    (fun τ _ => ((τ.trans e.symm : Equiv.Perm _))⁻¹) (fun σ hσ => ?_) (fun τ hτ => ?_)
    (fun σ _ => ?_) (fun τ _ => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    rw [← hrank, hσ]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hτ ⊢
    rw [hrank]
    convert hτ using 2
    ext x
    simp
  · ext x
    simp [Equiv.Perm.inv_def]
  · ext x
    simp [Equiv.Perm.inv_def]

end SampleRank

section Law

variable {m N : ℕ}

/-- **The binomial ratio is the beta-binomial mass.** For `1 ≤ r ≤ m + 1` and `j ≤ N`, with
`p = r - 1 + j`, `C(p, r - 1) C(m + N - p, m + 1 - r) / C(m + 1 + N, m + 1) =
BB(N; r, m + 2 - r)(j)`. -/
theorem choose_mul_choose_div_choose_eq_betaBinomialPMF {r j : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m + 1)
    (hj : j ≤ N) :
    ((r - 1 + j).choose (r - 1) * (m + 1 + N - 1 - (r - 1 + j)).choose (m + 1 - r) : ℝ) /
        (m + 1 + N).choose (m + 1) = betaBinomialPMF N r ((m : ℝ) + 2 - r) j := by
  obtain ⟨a, rfl⟩ : ∃ a, r = a + 1 := ⟨r - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, m = a + b := ⟨m - a, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, N = j + t := ⟨N - j, by omega⟩
  have e2 : a + b + 1 + (j + t) - 1 - (a + 1 - 1 + j) = b + t := by omega
  have e3 : a + b + 1 - (a + 1) = b := by omega
  have e4 : a + 1 - 1 = a := by omega
  rw [e2, e3, e4]
  unfold betaBinomialPMF
  rw [show j + t - j = t by omega]
  have hb : ((a + b : ℕ) : ℝ) + 2 - ((a + 1 : ℕ) : ℝ) = ((b + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  have hab : ((a + 1 : ℕ) : ℝ) + ((b + 1 : ℕ) : ℝ) = ((a + b + 1 + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hb, hab, ascPochhammer_nat_eq_natCast_ascFactorial,
    ascPochhammer_nat_eq_natCast_ascFactorial, ascPochhammer_nat_eq_natCast_ascFactorial]
  have g : ∀ n k : ℕ, ((n + 1).ascFactorial k : ℝ) = (n + k).factorial / n.factorial := by
    intro n k
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (by rw [mul_comm]; exact Nat.factorial_mul_ascFactorial n k)
  rw [g a j, g b t, g (a + b + 1) (j + t), Nat.cast_add_choose, Nat.cast_add_choose,
    Nat.cast_add_choose, Nat.cast_add_choose]
  field_simp

/-- **Beta-binomial law of the sample rank for exchangeable scores without ties.** If the law
`μ` of the score vector is a probability measure invariant under every coordinate permutation
and the scores are almost surely distinct, then for `1 ≤ r ≤ m + 1` the number `J` of synthetic
scores below the `r`-th real score has the beta-binomial law `BB(N; r, m + 2 - r)`. -/
theorem measureReal_sampleRank_eq_of_exchangeable {r : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m + 1)
    (μ : Measure (Fin (m + 1) ⊕ Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ σ : Equiv.Perm (Fin (m + 1) ⊕ Fin N), μ.map (fun ω => ω ∘ σ) = μ)
    (hinj : ∀ᵐ ω ∂μ, Function.Injective ω) (j : ℕ) :
    μ.real {ω | sampleRank r ω = j} = betaBinomialPMF N r ((m : ℝ) + 2 - r) j := by
  rcases lt_or_ge N j with hjN | hjN
  · have hempty : {ω : Fin (m + 1) ⊕ Fin N → ℝ | sampleRank r ω = j} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      have := sampleRank_le r ω
      omega
    rw [hempty, measureReal_empty]
    simp [betaBinomialPMF, Nat.choose_eq_zero_of_lt hjN]
  have := smulInvariantMeasure_of_map_comp_eq hμ
  have hA : MeasurableSet {ω : Fin (m + 1) ⊕ Fin N → ℝ | sampleRank r ω = j} :=
    measurable_sampleRank hr (measurableSet_singleton j)
  have hmeas := measure_eq_card_div_of_ae_card_filter_smul_mem_eq μ
    (fun σ : Equiv.Perm (Fin (m + 1) ⊕ Fin N) =>
      Measurable.of_eval fun i => by exact measurable_pi_apply (σ⁻¹ i)) hA
    (c := (univ.filter fun τ : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N) => rankCount r τ = j).card)
    (by
      filter_upwards [hinj] with ω hω
      convert card_filter_sampleRank_smul_eq hr hω j using 2
      ext σ
      simp)
  set S₀ := realPositions (finSumFinEquiv : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N))
  have hS₀ : S₀.card = m + 1 := card_realPositions _
  set c₀ := (univ.filter fun τ : Fin (m + 1) ⊕ Fin N ≃ Fin (m + 1 + N) =>
    realPositions τ = S₀).card
  have hc₀ := choose_mul_card_fiber hS₀
  have hcount := card_rankCount_eq (r := r) (j := j) hS₀
  have hp : r - 1 + j < m + 1 + N := by omega
  have hW : ((Finset.powersetCard (m + 1) (univ : Finset (Fin (m + 1 + N)))).filter
      fun S => gapCount r S = j).card =
      (r - 1 + j).choose (r - 1) * (m + 1 + N - 1 - (r - 1 + j)).choose (m + 1 - r) := by
    rw [← card_filter_mem_card_filter_lt_eq hr hrm (⟨r - 1 + j, hp⟩ : Fin (m + 1 + N))]
    refine congrArg Finset.card (Finset.filter_congr fun S hS => ?_)
    exact gapCount_eq_iff hr hrm (Finset.mem_powersetCard.1 hS).2 rfl
  rw [measureReal_def, hmeas, Fintype.card_perm, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast, hcount,
    hW, ← hc₀, ← choose_mul_choose_div_choose_eq_betaBinomialPMF hr hrm hjN]
  have hc₀pos : (c₀ : ℝ) ≠ 0 := by
    have : 0 < (m + 1 + N).factorial := Nat.factorial_pos _
    rw [← hc₀] at this
    exact_mod_cast (Nat.pos_of_mul_pos_left this).ne'
  have hch : ((m + 1 + N).choose (m + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  push_cast
  field_simp
  exact mul_div_cancel_right₀ _ hc₀pos

/-- **Product measures are exchangeable.** The i.i.d. law `Measure.pi fun _ => ν` on `ι → ℝ` is
invariant under every coordinate permutation. -/
theorem map_comp_perm_pi {ι : Type*} [Fintype ι] (ν : Measure ℝ) [SigmaFinite ν]
    (σ : Equiv.Perm ι) :
    (Measure.pi fun _ : ι => ν).map (fun ω => ω ∘ σ) = Measure.pi fun _ : ι => ν := by
  have h := Measure.pi_map_piCongrLeft (β := fun _ : ι => ℝ) σ.symm (fun _ => ν)
  convert h using 2
  funext ω
  funext i
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

/-- **Atomless i.i.d. scores are almost surely distinct.** Under `Measure.pi fun _ => ν` with
`ν` an atomless probability measure on `ℝ`, the coordinates are almost surely pairwise distinct:
for `a ≠ b` the pair `(ω a, ω b)` has law `ν ⊗ ν`, which gives the diagonal measure
`∫ ν {x} dν(x) = 0`. No density is assumed. -/
theorem ae_injective_pi {ι : Type*} [Fintype ι] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] :
    ∀ᵐ ω ∂(Measure.pi fun _ : ι => ν), Function.Injective ω := by
  have hpair : ∀ a b : ι, a ≠ b → (Measure.pi fun _ : ι => ν) {ω | ω a = ω b} = 0 := by
    intro a b hab
    have hind : iIndepFun (fun i (ω : ι → ℝ) => ω i) (Measure.pi fun _ : ι => ν) :=
      iIndepFun_pi (X := fun _ (x : ℝ) => x) fun _ => aemeasurable_id
    have h2 := (hind.indepFun hab).map_prod_eq_prod_map_map
      (measurable_pi_apply a).aemeasurable (measurable_pi_apply b).aemeasurable
    rw [(measurePreserving_eval (fun _ : ι => ν) a).map_eq,
      (measurePreserving_eval (fun _ : ι => ν) b).map_eq] at h2
    have hD : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} := measurableSet_diagonal
    have hmap : (Measure.pi fun _ : ι => ν) {ω | ω a = ω b} =
        ((Measure.pi fun _ : ι => ν).map fun ω => (ω a, ω b)) {p : ℝ × ℝ | p.1 = p.2} := by
      rw [Measure.map_apply (by fun_prop) hD]
      rfl
    rw [hmap, h2, Measure.prod_apply hD]
    simp
  have hall : ∀ᵐ ω ∂(Measure.pi fun _ : ι => ν), ∀ a b, a ≠ b → ω a ≠ ω b := by
    rw [ae_all_iff]
    intro a
    rw [ae_all_iff]
    intro b
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall fun _ h => absurd hab h
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) (hpair a b hab)
    by_contra h
    exact hω fun _ => h
  filter_upwards [hall] with ω hω a b h
  by_contra hne
  exact hω a b hne h

/-- **Beta-binomial law of the sample rank (i.i.d. atomless scores).** Let the `m + 1` real
and `N` synthetic scores be i.i.d. with an atomless law `ν` on `ℝ`, i.e. the score vector has law
`Measure.pi fun _ => ν`. For `1 ≤ r ≤ m + 1`, the rank `K = J + 1` of the `r`-th real score among
the synthetic scores satisfies `P(K = k) = BB(N; r, m + 2 - r)(k - 1)` for every `k ≥ 1`; this mass
vanishes for `k > N + 1`. -/
theorem measureReal_sampleRank_add_one_eq {r : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m + 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] {k : ℕ} (hk : 1 ≤ k) :
    (Measure.pi fun _ : Fin (m + 1) ⊕ Fin N => ν).real {ω | sampleRank r ω + 1 = k} =
      betaBinomialPMF N r ((m : ℝ) + 2 - r) (k - 1) := by
  have hset : {ω : Fin (m + 1) ⊕ Fin N → ℝ | sampleRank r ω + 1 = k} =
      {ω | sampleRank r ω = k - 1} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    omega
  rw [hset]
  exact measureReal_sampleRank_eq_of_exchangeable hr hrm _ (map_comp_perm_pi ν)
    (ae_injective_pi ν) (k - 1)

/-- **Binomial-ratio form of the sample-rank law.** Under the hypotheses of
`measureReal_sampleRank_add_one_eq`, for `1 ≤ k ≤ N + 1`,
`P(K = k) = C(k + r - 2, r - 1) C(N + m + 2 - k - r, m + 1 - r) / C(N + m + 1, m + 1)`. -/
theorem measureReal_sampleRank_add_one_eq_choose {r : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m + 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] {k : ℕ} (hk : 1 ≤ k)
    (hkN : k ≤ N + 1) :
    (Measure.pi fun _ : Fin (m + 1) ⊕ Fin N => ν).real {ω | sampleRank r ω + 1 = k} =
      ((k + r - 2).choose (r - 1) * (N + m + 2 - k - r).choose (m + 1 - r) : ℝ) /
        (N + m + 1).choose (m + 1) := by
  rw [measureReal_sampleRank_add_one_eq hr hrm ν hk,
    ← choose_mul_choose_div_choose_eq_betaBinomialPMF hr hrm (by omega : k - 1 ≤ N)]
  rw [show r - 1 + (k - 1) = k + r - 2 by omega,
    show m + 1 + N - 1 - (k + r - 2) = N + m + 2 - k - r by omega,
    show m + 1 + N = N + m + 1 by omega]

/-- **Distribution function of the rank for exchangeable scores without ties.** Under the
hypotheses of `measureReal_sampleRank_eq_of_exchangeable`,
`F t = P(K ≤ t) = ∑_{j < t} BB(N; r, m + 2 - r)(j)` for every `t`. -/
theorem measureReal_sampleRank_add_one_le_of_exchangeable {r : ℕ} (hr : 1 ≤ r)
    (hrm : r ≤ m + 1) (μ : Measure (Fin (m + 1) ⊕ Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ σ : Equiv.Perm (Fin (m + 1) ⊕ Fin N), μ.map (fun ω => ω ∘ σ) = μ)
    (hinj : ∀ᵐ ω ∂μ, Function.Injective ω) (t : ℕ) :
    μ.real {ω | sampleRank r ω + 1 ≤ t} =
      ∑ j ∈ Finset.range t, betaBinomialPMF N r ((m : ℝ) + 2 - r) j := by
  have hset : {ω : Fin (m + 1) ⊕ Fin N → ℝ | sampleRank r ω + 1 ≤ t} =
      ⋃ j ∈ Finset.range t, {ω | sampleRank r ω = j} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop,
      exists_eq_right']
    omega
  have hd : Set.PairwiseDisjoint (↑(Finset.range t))
      (fun j => {ω : Fin (m + 1) ⊕ Fin N → ℝ | sampleRank r ω = j}) := by
    intro i _ j _ hij
    exact Set.disjoint_left.2 fun ω hi hj => hij (hi.symm.trans hj)
  rw [hset, measureReal_biUnion_finset hd fun j _ =>
    measurable_sampleRank hr (measurableSet_singleton j)]
  exact Finset.sum_congr rfl fun j _ =>
    measureReal_sampleRank_eq_of_exchangeable hr hrm μ hμ hinj j

/-- **Distribution function of the rank (i.i.d. atomless scores).** For i.i.d. scores with a law
`ν` without atoms and `1 ≤ r ≤ m + 1`, `P(K ≤ t) = ∑_{j < t} BB(N; r, m + 2 - r)(j)`. -/
theorem measureReal_sampleRank_add_one_le {r : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m + 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] (t : ℕ) :
    (Measure.pi fun _ : Fin (m + 1) ⊕ Fin N => ν).real {ω | sampleRank r ω + 1 ≤ t} =
      ∑ j ∈ Finset.range t, betaBinomialPMF N r ((m : ℝ) + 2 - r) j :=
  measureReal_sampleRank_add_one_le_of_exchangeable hr hrm _ (map_comp_perm_pi ν)
    (ae_injective_pi ν) t

/-- **Mean of the sample rank for exchangeable scores without ties.** Under the hypotheses of
`measureReal_sampleRank_eq_of_exchangeable`, `E K = 1 + N r / (m + 2)`. No moment assumption on
the scores is needed: `K` is bounded. -/
theorem integral_sampleRank_add_one_of_exchangeable {r : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m + 1)
    (μ : Measure (Fin (m + 1) ⊕ Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ σ : Equiv.Perm (Fin (m + 1) ⊕ Fin N), μ.map (fun ω => ω ∘ σ) = μ)
    (hinj : ∀ᵐ ω ∂μ, Function.Injective ω) :
    ∫ ω, ((sampleRank r ω : ℝ) + 1) ∂μ = 1 + N * r / (m + 2) := by
  have hmeas : ∀ j, MeasurableSet {ω : Fin (m + 1) ⊕ Fin N → ℝ | sampleRank r ω = j} :=
    fun j => measurable_sampleRank hr (measurableSet_singleton j)
  have hpt : (fun ω : Fin (m + 1) ⊕ Fin N → ℝ => (sampleRank r ω : ℝ) + 1) =
      fun ω => ∑ j ∈ Finset.range (N + 1),
        {ω : Fin (m + 1) ⊕ Fin N → ℝ | sampleRank r ω = j}.indicator
          (fun _ => (j : ℝ) + 1) ω := by
    funext ω
    have hle := sampleRank_le r ω
    rw [Finset.sum_eq_single (sampleRank r ω)]
    · simp
    · intro j _ hj
      simp [Set.indicator_of_notMem, Ne.symm hj]
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  rw [hpt, integral_finsetSum _ fun j _ => (integrable_const _).indicator (hmeas j)]
  simp_rw [integral_indicator_const _ (hmeas _), smul_eq_mul,
    measureReal_sampleRank_eq_of_exchangeable hr hrm μ hμ hinj]
  have hα : (0 : ℝ) < r := by exact_mod_cast hr
  have hβ : (0 : ℝ) < (m : ℝ) + 2 - r := by
    have : (r : ℝ) ≤ m + 1 := by exact_mod_cast hrm
    linarith
  have h1 := sum_betaBinomialPMF N hα hβ
  have h2 := sum_mul_betaBinomialPMF (n := N) hα hβ
  have hsplit : ∑ j ∈ Finset.range (N + 1), betaBinomialPMF N r ((m : ℝ) + 2 - r) j *
      ((j : ℝ) + 1) =
        ∑ j ∈ Finset.range (N + 1), (j : ℝ) * betaBinomialPMF N r ((m : ℝ) + 2 - r) j +
        ∑ j ∈ Finset.range (N + 1), betaBinomialPMF N r ((m : ℝ) + 2 - r) j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit, h1, h2, show (r : ℝ) + ((m : ℝ) + 2 - r) = m + 2 by ring]
  ring

/-- **Mean of the sample rank (i.i.d. atomless scores).** For i.i.d. scores with an atomless law
`ν` and `1 ≤ r ≤ m + 1`, `E K = 1 + N r / (m + 2)`, with no moment assumption on `ν`. -/
theorem integral_sampleRank_add_one {r : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m + 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    ∫ ω, ((sampleRank r ω : ℝ) + 1) ∂(Measure.pi fun _ : Fin (m + 1) ⊕ Fin N => ν) =
      1 + N * r / (m + 2) :=
  integral_sampleRank_add_one_of_exchangeable hr hrm _ (map_comp_perm_pi ν) (ae_injective_pi ν)

end Law

section Window

variable {m N : ℕ}

/-- **The `+∞` sentinel.** The `(N + 1)`-th synthetic order statistic `S̃₍N+1₎` is `⊤`. -/
theorem syntheticOrderStatistic_succ_eq_top (ω : Fin (m + 1) ⊕ Fin N → ℝ) :
    syntheticOrderStatistic (N + 1) ω = ⊤ :=
  (orderStatistic_eq_top_iff _ (by omega)).2 (by simp)

/-- **The real order statistic is a real score.** For `1 ≤ r ≤ m + 1`, `S₍ᵣ₎` is finite and equals
one of the real scores. -/
theorem exists_realOrderStatistic_eq {r : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m + 1)
    (ω : Fin (m + 1) ⊕ Fin N → ℝ) : ∃ i, realOrderStatistic r ω = ω (Sum.inl i) := by
  have hne : realOrderStatistic r ω ≠ ⊤ := by
    rw [realOrderStatistic, Ne, orderStatistic_eq_top_iff _ hr]
    simp only [Fintype.card_fin, not_lt]
    exact hrm
  obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hne
  have hc := (orderStatistic_eq_coe_iff hr x).1 hx.symm
  by_contra hno
  push Not at hno
  have hneq : ∀ i, ω (Sum.inl i) ≠ x := fun i h => hno i (by rw [← hx, h])
  have hfilt : (univ.filter fun i : Fin (m + 1) => ω (Sum.inl i) ≤ x) =
      univ.filter fun i : Fin (m + 1) => ω (Sum.inl i) < x :=
    Finset.filter_congr fun i _ => ⟨fun h => lt_of_le_of_ne h (hneq i), le_of_lt⟩
  rw [hfilt] at hc
  omega

/-- **Window event for distinct scores.** If the scores are pairwise distinct and `a < b`, then
`S̃₍ₐ₎ ≤ S₍ᵣ₎ ≤ S̃₍b₎` (with `a = 0` standing for the `-∞` sentinel) holds exactly when
`a ≤ J < b`, i.e. `a + 1 ≤ K ≤ b`. Distinctness is needed for the lower comparison: with a tie
between `S̃₍ₐ₎` and `S₍ᵣ₎` the event can hold while `J < a`. -/
theorem window_iff_of_injective {r a b : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m + 1) (hab : a < b)
    {ω : Fin (m + 1) ⊕ Fin N → ℝ} (hω : Function.Injective ω) :
    ((a = 0 ∨ syntheticOrderStatistic a ω ≤ realOrderStatistic r ω) ∧
        realOrderStatistic r ω ≤ syntheticOrderStatistic b ω) ↔
      a ≤ sampleRank r ω ∧ sampleRank r ω < b := by
  obtain ⟨i, hi⟩ := exists_realOrderStatistic_eq hr hrm ω
  have hJ : sampleRank r ω = (univ.filter fun s : Fin N => ω (Sum.inr s) < ω (Sum.inl i)).card := by
    unfold sampleRank
    rw [hi]
    exact congrArg Finset.card (Finset.filter_congr fun s _ => WithTop.coe_lt_coe)
  have hle : (univ.filter fun s : Fin N => ω (Sum.inr s) ≤ ω (Sum.inl i)) =
      univ.filter fun s : Fin N => ω (Sum.inr s) < ω (Sum.inl i) :=
    Finset.filter_congr fun s _ => ⟨fun h => lt_of_le_of_ne h (fun h' =>
      Sum.inr_ne_inl (hω h')), le_of_lt⟩
  rw [hi, syntheticOrderStatistic, syntheticOrderStatistic, coe_le_orderStatistic_iff (by omega),
    ← hJ]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · rw [orderStatistic_le_coe_iff ha, hle, ← hJ]
    constructor
    · rintro ⟨h | h, h'⟩
      · omega
      · exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩
      exact ⟨Or.inr h, h'⟩

/-- **Window probability for scores without ties.** If the scores are almost surely pairwise
distinct (no exchangeability is needed for this identity), then with `F t = P(K ≤ t)` and `a < b`,
`P((a = 0 ∨ S̃₍ₐ₎ ≤ S₍ᵣ₎) ∧ S₍ᵣ₎ ≤ S̃₍b₎) = F b - F a`. Here `a = 0` is the `-∞` sentinel and
`b = N + 1` gives `S̃₍N+1₎ = ⊤`, the `+∞` sentinel (`syntheticOrderStatistic_succ_eq_top`). The
event identity behind this holds only almost surely, on the event of distinct scores. -/
theorem measureReal_window_of_ae_injective {r a b : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m + 1)
    (hab : a < b) (μ : Measure (Fin (m + 1) ⊕ Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hinj : ∀ᵐ ω ∂μ, Function.Injective ω) :
    μ.real {ω | (a = 0 ∨ syntheticOrderStatistic a ω ≤ realOrderStatistic r ω) ∧
        realOrderStatistic r ω ≤ syntheticOrderStatistic b ω} =
      μ.real {ω | sampleRank r ω + 1 ≤ b} - μ.real {ω | sampleRank r ω + 1 ≤ a} := by
  have hae : {ω : Fin (m + 1) ⊕ Fin N → ℝ |
      (a = 0 ∨ syntheticOrderStatistic a ω ≤ realOrderStatistic r ω) ∧
        realOrderStatistic r ω ≤ syntheticOrderStatistic b ω} =ᵐ[μ]
      ({ω | sampleRank r ω + 1 ≤ b} \ {ω | sampleRank r ω + 1 ≤ a} : Set _) := by
    filter_upwards [hinj] with ω hω
    apply propext
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_le]
    rw [window_iff_of_injective hr hrm hab hω]
    omega
  have hmeas : MeasurableSet {ω : Fin (m + 1) ⊕ Fin N → ℝ | sampleRank r ω + 1 ≤ a} :=
    (measurable_sampleRank hr) (MeasurableSet.of_discrete (s := {n : ℕ | n + 1 ≤ a}))
  have hsub : {ω : Fin (m + 1) ⊕ Fin N → ℝ | sampleRank r ω + 1 ≤ a} ⊆
      {ω | sampleRank r ω + 1 ≤ b} := fun ω (h : sampleRank r ω + 1 ≤ a) =>
    (show sampleRank r ω + 1 ≤ b by omega)
  rw [measureReal_congr hae, measureReal_sdiff hsub hmeas]

/-- **Window probability (i.i.d. atomless scores).** For i.i.d. scores with a law `ν` without
atoms, `1 ≤ r ≤ m + 1` and `a < b`, `P((a = 0 ∨ S̃₍ₐ₎ ≤ S₍ᵣ₎) ∧ S₍ᵣ₎ ≤ S̃₍b₎) = F b - F a` with
`F t = P(K ≤ t)`. The window of the source setting is `0 ≤ a < b ≤ N + 1`. -/
theorem measureReal_window {r a b : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m + 1) (hab : a < b)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    (Measure.pi fun _ : Fin (m + 1) ⊕ Fin N => ν).real
        {ω | (a = 0 ∨ syntheticOrderStatistic a ω ≤ realOrderStatistic r ω) ∧
          realOrderStatistic r ω ≤ syntheticOrderStatistic b ω} =
      (Measure.pi fun _ : Fin (m + 1) ⊕ Fin N => ν).real {ω | sampleRank r ω + 1 ≤ b} -
        (Measure.pi fun _ : Fin (m + 1) ⊕ Fin N => ν).real {ω | sampleRank r ω + 1 ≤ a} :=
  measureReal_window_of_ae_injective hr hrm hab _ (ae_injective_pi ν)

end Window

end MathlibExt.Probability.Distributions.BetaBinomialSampleRank
