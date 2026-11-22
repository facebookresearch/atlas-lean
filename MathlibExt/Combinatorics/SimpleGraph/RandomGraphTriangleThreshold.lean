/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.RamseyErdosLowerBound
public import MathlibExt.Probability.Combinatorics.SecondMomentMethod
public import Mathlib.Combinatorics.SimpleGraph.Clique

import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The threshold for triangles in `G(n, p)`

In the binomial random graph `G(n, p)` (every pair of the `n` vertices an edge independently
with probability `p`), let `X` be the number of triangles, so `E X = C(n, 3) p³`.

* First moment: `P(G(n, p) contains a triangle) ≤ C(n, 3) p³`
  (`measureReal_not_cliqueFree_three_le`).
* Second moment: `P(G(n, p) is triangle-free) ≤ (1 + 3 n p²) / (C(n, 3) p³)` for `p > 0`
  (`measureReal_cliqueFree_three_le`). Two triangles are dependent only when they share an edge,
  in which case they span five edges, and a triangle shares an edge with at most `3n` others, so
  `Δ ≤ 3 n p² · E X` and the counting form of the second moment method applies.

Hence `1/n` is a threshold for containing a triangle: if `n pₙ → 0` the first bound tends to
`0`, and if `n pₙ → ∞` (with `pₙ ≤ 1`) the second bound tends to `0`.

`G(n, p)` is modelled as `pairGraph ω` for the random set `ω` of pairs of
`MathlibExt.Probability.Combinatorics.RandomSubset.randomSubsetLaw` with constant probability
`p`.

Reference: Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes,
Spring 2019, Proposition 4.11 and its proof (https://yufeizhao.com/pm/sp19/pmnotes.pdf).
-/

@[expose] public section

open MeasureTheory SimpleGraph Finset unitInterval
  MathlibExt.Probability.Combinatorics.RandomSubset
  MathlibExt.Probability.Combinatorics.SecondMomentMethod
  MathlibExt.Combinatorics.RamseyErdosLowerBound

namespace MathlibExt.Combinatorics.RandomGraphTriangleThreshold

variable {n : ℕ}

/-- **Vertex triples.** The three-element subsets of `Fin n`, the possible triangles of a graph
on `Fin n`. -/
abbrev Triple (n : ℕ) := {T : Finset (Fin n) // T.card = 3}

lemma mem_containsEvent_iff_isNClique (ω : Pair n → Bool) (T : Finset (Fin n))
    (hT : T.card = 3) :
    ω ∈ containsEvent (pairsIn T) ↔ (pairGraph ω).IsNClique 3 T := by
  constructor
  · intro h
    refine ⟨fun x hx y hy hxy => ⟨hxy, h ⟨{x, y}, Finset.card_pair hxy⟩ ?_⟩, hT⟩
    simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and]
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hx
    · rw [Finset.mem_singleton.1 hz]; exact hy
  · intro h s hs
    simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨a, b, hab, hsab⟩ := Finset.card_eq_two.1 s.2
    have ha : a ∈ T := hs (by rw [hsab]; simp)
    have hb : b ∈ T := hs (by rw [hsab]; simp)
    obtain ⟨_, hω⟩ := h.1 ha hb hab
    have : s = ⟨{a, b}, Finset.card_pair hab⟩ := Subtype.ext hsab
    rw [this]
    exact hω

lemma not_cliqueFree_three_iff (ω : Pair n → Bool) :
    ¬ (pairGraph ω).CliqueFree 3 ↔ ∃ T : Triple n, ω ∈ containsEvent (pairsIn T.1) := by
  simp only [CliqueFree, not_forall, not_not]
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨⟨T, hT.2⟩, (mem_containsEvent_iff_isNClique ω T hT.2).2 hT⟩
  · rintro ⟨T, hT⟩
    exact ⟨T.1, (mem_containsEvent_iff_isNClique ω T.1 T.2).1 hT⟩

lemma card_pairsIn_triple (T : Triple n) : (pairsIn T.1).card = 3 := by
  rw [card_pairsIn, T.2]; rfl

lemma pairsIn_inter (R S : Finset (Fin n)) : pairsIn R ∩ pairsIn S = pairsIn (R ∩ S) := by
  ext s
  simp [pairsIn, Finset.subset_inter_iff]

/-- **First moment bound for triangles in `G(n, p)`.** The probability that `G(n, p)` contains a
triangle is at most `C(n, 3) p³`, the expected number of triangles (Y. Zhao, *The Probabilistic
Method in Combinatorics*, MIT 18.218 notes, 2019, proof of Proposition 4.11). -/
theorem measureReal_not_cliqueFree_three_le (p : I) :
    (randomSubsetLaw (fun _ : Pair n => p)).real {ω | ¬ (pairGraph ω).CliqueFree 3} ≤
      (n.choose 3 : ℝ) * (p : ℝ) ^ 3 := by
  classical
  set μ := randomSubsetLaw (fun _ : Pair n => p)
  have hsub : {ω | ¬ (pairGraph ω).CliqueFree 3} ⊆
      ⋃ T ∈ (Finset.univ : Finset (Triple n)), containsEvent (pairsIn T.1) := by
    intro ω hω
    obtain ⟨T, hT⟩ := (not_cliqueFree_three_iff ω).1 hω
    exact Set.mem_biUnion (Finset.mem_univ T) hT
  calc μ.real {ω | ¬ (pairGraph ω).CliqueFree 3}
      ≤ μ.real (⋃ T ∈ (Finset.univ : Finset (Triple n)), containsEvent (pairsIn T.1)) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ T : Triple n, μ.real (containsEvent (pairsIn T.1)) :=
        measureReal_biUnion_finset_le _ _
    _ = (n.choose 3 : ℝ) * (p : ℝ) ^ 3 := by
        simp only [μ, randomSubsetLaw_real_containsEvent, Finset.prod_const, card_pairsIn_triple,
          Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin,
          nsmul_eq_mul]

/-- **Dependency graph of the triangle events.** Two distinct vertex triples are adjacent when
they share a pair, that is, when the corresponding triangles of `K_n` share an edge; triangles
without a common edge depend on disjoint sets of edges and are independent (Y. Zhao, *The
Probabilistic Method in Combinatorics*, MIT 18.218 notes, 2019, Section 4.2). -/
def shareEdge (n : ℕ) : SimpleGraph (Triple n) where
  Adj T T' := T ≠ T' ∧ ¬ Disjoint (pairsIn T.1) (pairsIn T'.1)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hd => h.2 hd.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma card_inter_le_two {T T' : Triple n} (h : T ≠ T') : (T.1 ∩ T'.1).card ≤ 2 := by
  by_contra hc
  push Not at hc
  have h3 : (T.1 ∩ T'.1).card = 3 :=
    le_antisymm ((Finset.card_le_card Finset.inter_subset_left).trans T.2.le) hc
  have e1 : T.1 ∩ T'.1 = T.1 :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h3, T.2])
  have e2 : T.1 ∩ T'.1 = T'.1 :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [h3, T'.2])
  exact h (Subtype.ext (e1.symm.trans e2))

/-- **Two triangles sharing an edge span five edges.** Distinct triples meet in at most two
vertices, so their pair sets share at most one pair and together contain at least `5` pairs. -/
lemma five_le_card_union {T T' : Triple n} (h : T ≠ T') :
    5 ≤ (pairsIn T.1 ∪ pairsIn T'.1).card := by
  have hu := Finset.card_union_add_card_inter (pairsIn T.1) (pairsIn T'.1)
  rw [card_pairsIn_triple, card_pairsIn_triple, pairsIn_inter, card_pairsIn] at hu
  have hi : (T.1 ∩ T'.1).card.choose 2 ≤ 1 := by
    have := card_inter_le_two h
    interval_cases (T.1 ∩ T'.1).card <;> simp
  omega

/-- **A triangle shares an edge with at most `3n` others.** A triple sharing a pair with `T` is
that pair plus one more vertex, so there are at most `3 · n` of them; the exact count
`3 (n - 3)` is implicit in the variance term
`C(n, 2) (n - 2) (n - 3) (p⁵ - p⁶) = C(n, 3) · 3 (n - 3) · (p⁵ - p⁶)` of Y. Zhao, *The
Probabilistic Method in Combinatorics*, MIT 18.218 notes, 2019, Example 4.5. -/
lemma card_shareEdge_le (T : Triple n) [DecidableRel (shareEdge n).Adj] :
    (Finset.univ.filter fun T' => (shareEdge n).Adj T T').card ≤ 3 * n := by
  classical
  let f : Pair n × Fin n → Finset (Fin n) := fun x => x.1.1 ∪ {x.2}
  have hsub : (Finset.univ.filter fun T' => (shareEdge n).Adj T T').map
      ⟨Subtype.val, Subtype.val_injective⟩ ⊆ ((pairsIn T.1) ×ˢ Finset.univ).image f := by
    intro U hU
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk] at hU
    obtain ⟨T', ⟨-, hnd⟩, rfl⟩ := hU
    obtain ⟨s, hsT, hsT'⟩ := Finset.not_disjoint_iff.1 hnd
    simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at hsT hsT'
    have hcard : (T'.1 \ s.1).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsT', T'.2, s.2]
    obtain ⟨c, hc⟩ := Finset.card_eq_one.1 hcard
    refine Finset.mem_image.2 ⟨(s, c), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_univ, and_true, pairsIn, Finset.mem_filter,
        true_and]
      exact hsT
    · simp only [f]
      rw [← hc, Finset.union_sdiff_of_subset hsT']
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_map] at h1
  refine h1.trans ((Finset.card_image_le).trans ?_)
  rw [Finset.card_product, card_pairsIn, T.2, Finset.card_univ, Fintype.card_fin]
  rfl

/-- **Second moment bound for triangles in `G(n, p)`.** For `0 < p ≤ 1`, the probability that
`G(n, p)` is triangle-free is at most `(1 + 3 n p²) / (C(n, 3) p³)`. With `μ = C(n, 3) p³` the
expected number of triangles, this is `1/μ + 3 n p² / μ`, which tends to `0` when `n p → ∞`
(Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 notes, 2019, proof of
Proposition 4.11, via Lemma 4.8 and Corollary 4.13; a triangle shares an edge with at most
`3 (n - 3) ≤ 3 n` others, and two such triangles span five edges). -/
theorem measureReal_cliqueFree_three_le (p : I) (hp : 0 < (p : ℝ)) (hn : 3 ≤ n) :
    (randomSubsetLaw (fun _ : Pair n => p)).real {ω | (pairGraph ω).CliqueFree 3} ≤
      (1 + 3 * n * (p : ℝ) ^ 2) / ((n.choose 3 : ℝ) * (p : ℝ) ^ 3) := by
  classical
  set μ := randomSubsetLaw (fun _ : Pair n => p)
  set A : Triple n → Set (Pair n → Bool) := fun T => containsEvent (pairsIn T.1)
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hAμ : ∀ T, μ.real (A T) = (p : ℝ) ^ 3 := by
    intro T
    simp only [A, μ, randomSubsetLaw_real_containsEvent, Finset.prod_const, card_pairsIn_triple]
  have hmean : expectedCount μ A = (n.choose 3 : ℝ) * (p : ℝ) ^ 3 := by
    simp only [expectedCount, hAμ, Finset.sum_const, Finset.card_univ, Fintype.card_finset_len,
      Fintype.card_fin, nsmul_eq_mul]
  have hchoose : (0 : ℝ) < n.choose 3 := by exact_mod_cast Nat.choose_pos hn
  have hμpos : 0 < expectedCount μ A := by rw [hmean]; positivity
  -- independence of triangles without a common edge
  have hind : ∀ T T', T ≠ T' → ¬ (shareEdge n).Adj T T' →
      μ.real (A T ∩ A T') = μ.real (A T) * μ.real (A T') := by
    intro T T' hne hadj
    have hdisj : Disjoint (pairsIn T.1) (pairsIn T'.1) := by
      by_contra hd; exact hadj ⟨hne, hd⟩
    simp only [A, μ, containsEvent_inter, randomSubsetLaw_real_containsEvent,
      Finset.prod_union hdisj]
  -- dependent pairs span at least five edges
  have hpair : ∀ T T', (shareEdge n).Adj T T' → μ.real (A T ∩ A T') ≤ (p : ℝ) ^ 5 := by
    intro T T' hadj
    simp only [A, μ, containsEvent_inter, randomSubsetLaw_real_containsEvent, Finset.prod_const]
    exact pow_le_pow_of_le_one p.2.1 hp1 (five_le_card_union hadj.1)
  have hdelta : dependentPairSum μ A (shareEdge n) ≤
      (n.choose 3 : ℝ) * (3 * n * (p : ℝ) ^ 5) := by
    unfold dependentPairSum
    calc ∑ T, ∑ T', (if (shareEdge n).Adj T T' then μ.real (A T ∩ A T') else 0)
        ≤ ∑ T : Triple n, ∑ T', (if (shareEdge n).Adj T T' then (p : ℝ) ^ 5 else 0) := by
          gcongr with T _ T' _
          split_ifs with h
          · exact hpair T T' h
          · exact le_rfl
      _ = ∑ T : Triple n,
            ((Finset.univ.filter fun T' => (shareEdge n).Adj T T').card : ℝ) * (p : ℝ) ^ 5 := by
          refine Finset.sum_congr rfl (fun T _ => ?_)
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ _T : Triple n, (3 * n : ℝ) * (p : ℝ) ^ 5 := by
          gcongr with T _
          exact_mod_cast card_shareEdge_le T
      _ = (n.choose 3 : ℝ) * (3 * n * (p : ℝ) ^ 5) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin,
            nsmul_eq_mul]
  have hset : {ω | (pairGraph ω).CliqueFree 3} = {ω | ∀ T, ω ∉ A T} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h T hT
      exact (not_cliqueFree_three_iff ω).2 ⟨T, hT⟩ h
    · intro h
      by_contra hc
      obtain ⟨T, hT⟩ := (not_cliqueFree_three_iff ω).1 hc
      exact h T hT
  rw [hset]
  calc μ.real {ω | ∀ T, ω ∉ A T}
      ≤ (expectedCount μ A + dependentPairSum μ A (shareEdge n)) / expectedCount μ A ^ 2 :=
        measureReal_forall_not_mem_le A (fun T => measurableSet_containsEvent _) (shareEdge n)
          hind hμpos
    _ ≤ ((n.choose 3 : ℝ) * (p : ℝ) ^ 3 + (n.choose 3 : ℝ) * (3 * n * (p : ℝ) ^ 5)) /
          ((n.choose 3 : ℝ) * (p : ℝ) ^ 3) ^ 2 := by
        rw [hmean]
        gcongr
    _ = (1 + 3 * n * (p : ℝ) ^ 2) / ((n.choose 3 : ℝ) * (p : ℝ) ^ 3) := by
        field_simp

/-- **Triangles are absent below the threshold `1/n`.** If `n pₙ → 0`, then the probability that
`G(n, pₙ)` contains a triangle tends to `0` (Y. Zhao, *The Probabilistic Method in
Combinatorics*, MIT 18.218 notes, 2019, Proposition 4.11, first half). -/
theorem tendsto_measureReal_not_cliqueFree_three_of_tendsto_zero (p : ℕ → I)
    (hp : Filter.Tendsto (fun n : ℕ => (n : ℝ) * p n) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ => (randomSubsetLaw (fun _ : Pair n => p n)).real
      {ω | ¬ (pairGraph ω).CliqueFree 3}) Filter.atTop (nhds 0) := by
  have hcube : Filter.Tendsto (fun n : ℕ => ((n : ℝ) * p n) ^ 3) Filter.atTop (nhds 0) := by
    simpa using hp.pow 3
  refine squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_) hcube
  refine (measureReal_not_cliqueFree_three_le (p n)).trans ?_
  have hc : (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 := by exact_mod_cast Nat.choose_le_pow n 3
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right hc (pow_nonneg (p n).2.1 3)

/-- **Triangles appear above the threshold `1/n`.** If `n pₙ → ∞`, then the probability that
`G(n, pₙ)` contains a triangle tends to `1` (Y. Zhao, *The Probabilistic Method in
Combinatorics*, MIT 18.218 notes, 2019, Proposition 4.11, second half, by the second moment
method). -/
theorem tendsto_measureReal_not_cliqueFree_three_of_tendsto_atTop (p : ℕ → I)
    (hp : Filter.Tendsto (fun n : ℕ => (n : ℝ) * p n) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n : ℕ => (randomSubsetLaw (fun _ : Pair n => p n)).real
      {ω | ¬ (pairGraph ω).CliqueFree 3}) Filter.atTop (nhds 1) := by
  -- the probability of being triangle-free tends to `0`
  have hinv : Filter.Tendsto (fun n : ℕ => ((n : ℝ) * p n)⁻¹) Filter.atTop (nhds 0) :=
    hp.inv_tendsto_atTop
  have hg : Filter.Tendsto (fun n : ℕ => 162 * ((n : ℝ) * p n)⁻¹ ^ 3 + 486 * ((n : ℝ) * p n)⁻¹)
      Filter.atTop (nhds 0) := by
    simpa using ((hinv.pow 3).const_mul 162).add (hinv.const_mul 486)
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (randomSubsetLaw (fun _ : Pair n => p n)).real
      {ω | (pairGraph ω).CliqueFree 3} ≤
        162 * ((n : ℝ) * p n)⁻¹ ^ 3 + 486 * ((n : ℝ) * p n)⁻¹ := by
    filter_upwards [Filter.eventually_ge_atTop 3, hp.eventually_gt_atTop 0] with n hn hnp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hp0 : (0 : ℝ) < p n := pos_of_mul_pos_right hnp hn0.le
    have hp1 : (p n : ℝ) ≤ 1 := (p n).2.2
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hC : (n : ℝ) ^ 3 / 162 ≤ n.choose 3 := by
      have h := Nat.pow_le_choose (α := ℝ) 3 n
      have hsub : ((n + 1 - 3 : ℕ) : ℝ) = (n : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hsub] at h
      have h3 : (n : ℝ) / 3 ≤ (n : ℝ) - 2 := by linarith
      have hpow : ((n : ℝ) / 3) ^ 3 ≤ ((n : ℝ) - 2) ^ 3 :=
        pow_le_pow_left₀ (by positivity) h3 3
      have hfact : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
      rw [hfact] at h
      nlinarith
    refine (measureReal_cliqueFree_three_le (p n) hp0 hn).trans ?_
    have hden : (n : ℝ) ^ 3 / 162 * (p n : ℝ) ^ 3 ≤ (n.choose 3 : ℝ) * (p n : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    calc (1 + 3 * n * (p n : ℝ) ^ 2) / ((n.choose 3 : ℝ) * (p n : ℝ) ^ 3)
        ≤ (1 + 3 * n * (p n : ℝ) ^ 2) / ((n : ℝ) ^ 3 / 162 * (p n : ℝ) ^ 3) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 162 * ((n : ℝ) * p n)⁻¹ ^ 3 + 486 * ((n : ℝ) ^ 2 * p n)⁻¹ := by
          field_simp
          ring
      _ ≤ 162 * ((n : ℝ) * p n)⁻¹ ^ 3 + 486 * ((n : ℝ) * p n)⁻¹ := by
          gcongr
          nlinarith
  have hfree : Filter.Tendsto (fun n : ℕ => (randomSubsetLaw (fun _ : Pair n => p n)).real
      {ω | (pairGraph ω).CliqueFree 3}) Filter.atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun n => measureReal_nonneg) hev hg
  -- complement
  have hlow : ∀ n : ℕ, 1 - (randomSubsetLaw (fun _ : Pair n => p n)).real
      {ω | (pairGraph ω).CliqueFree 3} ≤ (randomSubsetLaw (fun _ : Pair n => p n)).real
      {ω | ¬ (pairGraph ω).CliqueFree 3} := by
    intro n
    have hu := measureReal_union_le (μ := randomSubsetLaw (fun _ : Pair n => p n))
      {ω | (pairGraph ω).CliqueFree 3} {ω | ¬ (pairGraph ω).CliqueFree 3}
    have : {ω | (pairGraph ω).CliqueFree 3} ∪ {ω | ¬ (pairGraph ω).CliqueFree 3} =
        (Set.univ : Set (Pair n → Bool)) := by
      ext ω; simp [em]
    rw [this, probReal_univ] at hu
    linarith
  have hlim : Filter.Tendsto (fun n : ℕ => 1 - (randomSubsetLaw (fun _ : Pair n => p n)).real
      {ω | (pairGraph ω).CliqueFree 3}) Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hfree
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlow
    (fun n => measureReal_le_one)

end MathlibExt.Combinatorics.RandomGraphTriangleThreshold
