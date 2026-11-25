/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.RamseyErdosLowerBound
public import MathlibExt.Probability.Combinatorics.RandomSubset
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

import MathlibExt.Probability.Combinatorics.JansonInequality
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The chromatic number of dense random graphs

Bollobás (1988) determined the chromatic number of `G(n, p)` for constant `p` asymptotically:
`χ(G(n, p)) ~ n / (2 log_b n)` with high probability, where `b = 1/(1 - p)`; for `p = 1/2` this is
`n / (2 log₂ n)`. The lower bound follows from the independence number `α(G(n, p)) ~ 2 log_b n`;
the upper bound needs that every set of `n/(log_b n)²` vertices contains an independent set of
size close to `2 log_b n`, which Bollobás proved with a martingale concentration inequality for
the maximum number of edge-disjoint independent sets of that size.

References: B. Bollobás, "The chromatic number of random graphs", *Combinatorica* 8 (1988)
49–55; A. Frieze and M. Karoński, *Introduction to Random Graphs*, Cambridge University Press 2016,
Theorem 7.7 and the remarks after its proof.

`G(n, p)` is `pairGraph ω` for `ω` drawn from `randomSubsetLaw` with constant probability `p`.

The proof of `tendsto_measureReal_chromaticNumber_near` applies Janson's inequality to the
complement graph. Inside a fixed vertex set, two candidate independent sets share a pair exactly
when they share at least two vertices. Grouping Janson's correlation sum by this overlap gives a
failure probability small enough to sum over all vertex sets of the chosen size.
-/

public section

open Filter Topology MeasureTheory unitInterval Finset
  MathlibExt.Probability.Combinatorics.RandomSubset
  MathlibExt.Combinatorics.RamseyErdosLowerBound
  MathlibExt.Probability.JansonInequalityWanted

namespace MathlibExt.Combinatorics.SimpleGraph.RandomGraphChromaticNumberWanted

private lemma independent_iff {n : ℕ} (R : Finset (Fin n)) (ω : Pair n → Bool) :
    (pairGraph ω).IsIndepSet (R : Set (Fin n)) ↔ ω ∈ avoidEvent (pairsIn R) := by
  constructor
  · intro h e he
    obtain ⟨a, b, hab, heab⟩ := Finset.card_eq_two.mp e.2
    have hs : e.1 ⊆ R := (mem_filter.mp he).2
    have ha := hs (show a ∈ e.1 by simp [heab])
    have hb := hs (show b ∈ e.1 by simp [heab])
    have he' : e = ⟨{a, b}, card_pair hab⟩ := Subtype.ext heab
    cases hω : ω e with
    | false => rfl
    | true => exact (h ha hb hab ⟨hab, he' ▸ hω⟩).elim
  · rintro h a ha b hb hab ⟨_, ht⟩
    have hz := h ⟨{a, b}, card_pair hab⟩
      (mem_filter.mpr ⟨mem_univ _, insert_subset ha (singleton_subset_iff.mpr hb)⟩)
    simp_all

-- A union bound over the k-sets controls the lower tail of the chromatic number.
private lemma measure_large_independent_set_le {n : ℕ} (p : I) (k : ℕ) :
    (randomSubsetLaw (fun _ : Pair n => p)).real
      {ω | ∃ R : Finset (Fin n), R.card = k ∧ (pairGraph ω).IsIndepSet R} ≤
      n.choose k * (1 - (p : ℝ)) ^ (k.choose 2) := by
  classical
  let sets := (univ : Finset (Fin n)).powersetCard k
  have hs : {ω | ∃ R : Finset (Fin n), R.card = k ∧ (pairGraph ω).IsIndepSet R} ⊆
      ⋃ R ∈ sets, avoidEvent (pairsIn R) := by
    rintro ω ⟨R, hk, hi⟩
    exact Set.mem_iUnion₂.mpr ⟨R, mem_powersetCard.mpr ⟨subset_univ _, hk⟩,
      (independent_iff R ω).mp hi⟩
  let μ := randomSubsetLaw (fun _ : Pair n => p)
  refine (measureReal_mono (μ := μ) hs (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ?_)
  apply le_of_eq
  calc
    _ = ∑ _ ∈ sets, (1 - (p : ℝ)) ^ (k.choose 2) := by
      refine sum_congr rfl fun R hR => ?_
      rw [randomSubsetLaw_real_avoidEvent, prod_const, card_pairsIn,
        (mem_powersetCard.mp hR).2]
    _ = _ := by simp [sets]

private lemma joint_mass {n k : ℕ} (p : I) (R S : Finset (Fin n))
    (hR : R.card = k) (hS : S.card = k) :
    (randomSubsetLaw (fun _ : Pair n => p)).real
      (containsEvent (pairsIn R) ∩ containsEvent (pairsIn S)) =
      (p : ℝ) ^ (2 * k.choose 2 - (R ∩ S).card.choose 2) := by
  have hI : pairsIn (R ∩ S) = pairsIn R ∩ pairsIn S := by
    ext e
    simp [pairsIn, Finset.subset_inter_iff]
  have hc := Finset.card_union_add_card_inter (pairsIn R) (pairsIn S)
  rw [← hI, card_pairsIn, card_pairsIn, card_pairsIn, hR, hS] at hc
  rw [containsEvent_inter, randomSubsetLaw_real_containsEvent, prod_const]
  congr 1
  omega

-- Every candidate S with overlap j contains one of the j-subsets of R.
private lemma card_overlap_le {n k j : ℕ} (V R : Finset (Fin n)) (hR : R ⊆ V)
    (hk : R.card = k) (hj : j ≤ k) :
    ((V.powersetCard k).filter (fun S => (R ∩ S).card = j)).card ≤
      k.choose j * (V.card - j).choose (k - j) := by
  let fam (T : Finset (Fin n)) := (V.powersetCard k).filter (T ⊆ ·)
  have hs : (V.powersetCard k).filter (fun S => (R ∩ S).card = j) ⊆
      (R.powersetCard j).biUnion fam := by
    intro S hS
    obtain ⟨hmem, hc⟩ := mem_filter.mp hS
    exact mem_biUnion.mpr ⟨R ∩ S, mem_powersetCard.mpr ⟨inter_subset_left, hc⟩,
      mem_filter.mpr ⟨hmem, inter_subset_right⟩⟩
  refine (card_le_card hs).trans (card_biUnion_le.trans ?_)
  have he : ∀ T ∈ R.powersetCard j, (fam T).card = (V.card - j).choose (k - j) := by
    intro T hT
    obtain ⟨ht, hc⟩ := mem_powersetCard.mp hT
    dsimp [fam]
    rw [card_filter_powersetCard_subset T V k (ht.trans hR) (hc ▸ hj), hc]
  simp [sum_congr rfl he, hk]

private lemma choose_overlap_bound {s k j : ℕ} (hj : j ≤ k) :
    k.choose j * (s - j).choose (k - j) * (s - k) ^ j ≤ s.choose k * (k ^ 2) ^ j := by
  have hdec : (s - k) ^ j ≤ s.descFactorial j :=
    (Nat.pow_le_pow_left (by omega : s - k ≤ s + 1 - j) _).trans (Nat.pow_sub_le_descFactorial _ _)
  have hu : (s - j).choose (k - j) * (s - k) ^ j ≤ s.choose k * k ^ j := calc
    _ ≤ (s - j).choose (k - j) * s.descFactorial j := Nat.mul_le_mul_left _ hdec
    _ = s.choose k * k.descFactorial j := by
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
        ← mul_assoc (s.choose k), mul_right_comm _ (j.factorial), Nat.choose_mul hj]
      ac_rfl
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)
  calc
    _ = k.choose j * ((s - j).choose (k - j) * (s - k) ^ j) := by ring
    _ ≤ k ^ j * (s.choose k * k ^ j) := Nat.mul_le_mul (Nat.choose_le_pow _ _) hu
    _ = _ := by ring

-- For 2 ≤ j ≤ k, choose(j, 2) ≤ 1 + L(j - 2). Since x ≤ q^L, each further vertex
-- contributes a factor at most one after accounting for the extra shared pairs.
private lemma overlap_term_le {k j L : ℕ} (hj : 2 ≤ j) (hjk : j ≤ k) (hk : k + 1 ≤ 2 * L)
    {x q : ℝ} (hx : 0 ≤ x) (hq : 0 < q) (hq' : q ≤ 1) (h : x ≤ q ^ L) :
    x ^ j / q ^ (j.choose 2) ≤ x ^ 2 / q := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hexp : (2 + t).choose 2 ≤ 1 + L * t := by
    rw [Nat.choose_two_right]
    have hsub : 2 + t - 1 = 1 + t := by omega
    rw [hsub, Nat.div_le_iff_le_mul_add_pred (by decide)]
    nlinarith [Nat.mul_le_mul_right t (show 2 + t + 1 ≤ 2 * L by omega)]
  have hpow := pow_le_pow_of_le_one hq.le hq' hexp
  rw [div_le_div_iff₀ (pow_pos hq _) hq, pow_add]
  calc
    x ^ 2 * x ^ t * q ≤ x ^ 2 * (q ^ L) ^ t * q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hx h t) (sq_nonneg x)) hq.le
    _ = x ^ 2 * q ^ (1 + L * t) := by rw [pow_add, pow_one, pow_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (sq_nonneg _)

private lemma joint_mass_div {n k : ℕ} (p : I) (hp : 0 < (p : ℝ)) (R S : Finset (Fin n))
    (hR : R.card = k) (hS : S.card = k) :
    (randomSubsetLaw (fun _ : Pair n => p)).real
      (containsEvent (pairsIn R) ∩ containsEvent (pairsIn S)) =
      ((p : ℝ) ^ (k.choose 2)) ^ 2 / (p : ℝ) ^ ((R ∩ S).card.choose 2) := by
  rw [joint_mass p R S hR hS]
  have hc : (R ∩ S).card ≤ k := hR ▸ card_le_card inter_subset_left
  have he := Nat.choose_le_choose 2 hc
  rw [pow_sub₀ _ hp.ne' (by omega), pow_mul (p : ℝ) 2, ← pow_mul, mul_comm 2, pow_mul,
    div_eq_mul_inv]

-- Sum over the overlap with one fixed candidate. Two or more common vertices are
-- necessary for dependence, so the sum starts at overlap two.
private lemma correlation_row_le {n k L : ℕ} (V R : Finset (Fin n)) (hR : R ∈ V.powersetCard k)
    (hk : k + 1 ≤ 2 * L) (hm : k < V.card) (p : I) (hp : 0 < (p : ℝ))
    (hsmall : (k : ℝ) ^ 2 / (V.card - k : ℕ) ≤ (p : ℝ) ^ L) :
    (∑ S ∈ V.powersetCard k, if 2 ≤ (R ∩ S).card then
      (randomSubsetLaw (fun _ : Pair n => p)).real
        (containsEvent (pairsIn R) ∩ containsEvent (pairsIn S)) else 0) ≤
      (k + 1 : ℕ) * (V.card.choose k : ℝ) * ((p : ℝ) ^ (k.choose 2)) ^ 2 *
        (((k : ℝ) ^ 2 / (V.card - k : ℕ)) ^ 2 / p) := by
  classical
  let F := V.powersetCard k
  let m (S : Finset (Fin n)) := (R ∩ S).card
  let x := (k : ℝ) ^ 2 / (V.card - k : ℕ)
  let w (j : ℕ) := if 2 ≤ j then ((p : ℝ) ^ (k.choose 2)) ^ 2 / (p : ℝ) ^ (j.choose 2) else 0
  let N : ℝ := V.card.choose k
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hR
  have hsum : (∑ S ∈ F, w (m S)) =
      ∑ j ∈ range (k + 1), ((F.filter (fun S => m S = j)).card : ℝ) * w j := by
    rw [← sum_fiberwise_of_maps_to (g := m) (t := range (k + 1))
      (fun S (_ : S ∈ F) => mem_range.mpr (Nat.lt_succ_of_le (hcard ▸
        card_le_card (inter_subset_left : R ∩ S ⊆ R)))) (fun S => w (m S))]
    apply sum_congr rfl
    intro j hj
    trans ∑ _ ∈ F.filter (fun S => m S = j), w j
    · exact sum_congr rfl (fun S hS => congrArg w (mem_filter.mp hS).2)
    · simp
  have hpos : (0 : ℝ) < (V.card - k : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hm
  have hx : 0 ≤ x := div_nonneg (sq_nonneg _) hpos.le
  have hb (j : ℕ) (hj : j ∈ range (k + 1)) :
      ((F.filter (fun S => m S = j)).card : ℝ) * w j ≤
        N * ((p : ℝ) ^ (k.choose 2)) ^ 2 * (x ^ 2 / p) := by
    have hjk := Nat.le_of_lt_succ (mem_range.mp hj)
    have hc : ((F.filter (fun S => m S = j)).card : ℝ) ≤ N * x ^ j := by
      dsimp [N, x]
      rw [div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hpos j)]
      exact_mod_cast (Nat.mul_le_mul_right _ (card_overlap_le V R hsub hcard hjk)).trans
        (choose_overlap_bound hjk)
    by_cases hj' : 2 ≤ j
    · dsimp [w]
      rw [ite_eq_left hj']
      calc
        _ ≤ (N * x ^ j) * (((p : ℝ) ^ (k.choose 2)) ^ 2 / (p : ℝ) ^ (j.choose 2)) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
        _ = (N * ((p : ℝ) ^ (k.choose 2)) ^ 2) * (x ^ j / (p : ℝ) ^ (j.choose 2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (overlap_term_le hj' hjk hk hx hp p.2.2 hsmall)
          (by dsimp [N]; positivity)
    · simp only [w, ite_eq_right hj', mul_zero]
      dsimp [N]; positivity
  calc
    _ = ∑ S ∈ F, w (m S) := by
      apply sum_congr rfl
      intro S hS
      simp [m, w, joint_mass_div p hp R S hcard (mem_powersetCard.mp hS).2]
    _ ≤ ∑ _ ∈ range (k + 1), N * ((p : ℝ) ^ (k.choose 2)) ^ 2 * (x ^ 2 / p) := by
      rw [hsum]
      exact sum_le_sum hb
    _ = _ := by simp [N, x]; ring

-- Index each candidate twice. Its second copy contributes its own mass to the
-- correlation sum, ensuring the hypothesis μ ≤ Δ of the second Janson inequality.
private lemma fixed_set_miss_le {n k L : ℕ} (V : Finset (Fin n))
    (hk0 : 2 ≤ k) (hk : k + 1 ≤ 2 * L) (hm : k < V.card) (q : I) (hq : 0 < (q : ℝ))
    (hsmall : (k : ℝ) ^ 2 / (V.card - k : ℕ) ≤ (q : ℝ) ^ L) :
    (randomSubsetLaw (fun _ : Pair n => q)).real
      {ω | ∀ R ∈ V.powersetCard k, ω ∉ containsEvent (pairsIn R)} ≤
      Real.exp (-1 / (2 * (k + 1 : ℕ) * (((k : ℝ) ^ 2 / (V.card - k : ℕ)) ^ 2 / q))) := by
  classical
  let F := V.powersetCard k
  let P := fun _ : Pair n => q
  let S (i : Bool × F) := pairsIn i.2.1
  let x := (k : ℝ) ^ 2 / (V.card - k : ℕ)
  let a := (q : ℝ) ^ (k.choose 2)
  let N : ℝ := V.card.choose k
  let B := (k + 1 : ℕ) * (x ^ 2 / q)
  have hm' : (0 : ℝ) < (V.card - k : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hm
  have hk' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hx : 0 < x := by dsimp [x]; positivity
  have ha : 0 < a := pow_pos hq _
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Nat.choose_pos hm.le
  have hB : 0 < B := by dsimp [B]; positivity
  have hs (i : Bool × F) : (S i).card = k.choose 2 := by
    dsimp [S]
    rw [card_pairsIn, (mem_powersetCard.mp i.2.2).2]
  have hcount : Fintype.card (Bool × F) = 2 * V.card.choose k := by
    rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_coe, card_powersetCard]
  have hμ : jansonMu P S = 2 * N * a := by
    simp only [jansonMu, P, randomSubsetLaw_real_containsEvent, prod_const, hs, sum_const,
      card_univ, hcount, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, N, a]
  have hμ' : 0 < jansonMu P S := by rw [hμ]; positivity
  have hle : jansonMu P S ≤ jansonDelta P S := by
    apply sum_le_sum
    intro i _
    let j : Bool × F := (!i.1, i.2)
    have hij : i ≠ j := by
      intro h
      have he : i.1 = !i.1 := congrArg Prod.fst h
      cases hbit : i.1 <;> simp [hbit] at he
    have hnon : (S i).Nonempty := card_pos.mp ((hs i) ▸ Nat.choose_pos hk0)
    have hcond : i ≠ j ∧ ¬ Disjoint (S i) (S j) := ⟨hij, by
      change ¬ Disjoint (S i) (S i)
      simpa using hnon.ne_empty⟩
    refine le_trans ?_
      (single_le_sum (fun _ _ => ite_nonneg measureReal_nonneg le_rfl) (mem_univ j))
    simp only [ite_eq_left hcond]
    change _ ≤ (randomSubsetLaw P).real (containsEvent (S i) ∩ containsEvent (S i))
    simp
  have hD : jansonDelta P S ≤ (jansonMu P S) ^ 2 * B := by
    let mass (R T : Finset (Fin n)) := if 2 ≤ (R ∩ T).card then
      (randomSubsetLaw P).real (containsEvent (pairsIn R) ∩ containsEvent (pairsIn T)) else 0
    have hrow : ∀ i : Bool × F, (∑ j : Bool × F, if i ≠ j ∧ ¬ Disjoint (S i) (S j) then
        (randomSubsetLaw P).real (containsEvent (S i) ∩ containsEvent (S j)) else 0) ≤
        2 * ((k + 1 : ℕ) * N * a ^ 2 * (x ^ 2 / q)) := by
      intro i
      calc
        _ ≤ ∑ j : Bool × F, mass i.2.1 j.2.1 := by
          apply sum_le_sum
          intro j _
          by_cases h : i ≠ j ∧ ¬ Disjoint (S i) (S j)
          · obtain ⟨e, hi, hj⟩ := Finset.not_disjoint_iff.mp h.2
            have he : e.1 ⊆ i.2.1 ∩ j.2.1 := subset_inter (mem_filter.mp hi).2 (mem_filter.mp hj).2
            have hc := card_le_card he
            rw [e.2] at hc
            simp only [ite_eq_left h, mass, ite_eq_left hc, S]
            exact le_rfl
          · simp only [ite_eq_right h, mass]
            split <;> positivity
        _ = 2 * ∑ T ∈ F, mass i.2.1 T := by
          rw [Fintype.sum_prod_type, Fintype.sum_bool, sum_coe_sort, two_mul]
        _ ≤ _ := by gcongr; exact correlation_row_le V i.2.1 i.2.2 hk hm q hq hsmall
    calc
      _ ≤ ∑ _ : Bool × F, 2 * ((k + 1 : ℕ) * N * a ^ 2 * (x ^ 2 / q)) :=
        sum_le_sum fun i _ => hrow i
      _ = _ := by
        simp only [sum_const, card_univ, hcount, nsmul_eq_mul, Nat.cast_mul,
          Nat.cast_ofNat, hμ, B, N]
        ring
  have hJ := janson_inequality_of_le P S hle
  have hE : {ω | ∀ R ∈ F, ω ∉ containsEvent (pairsIn R)} =
      {ω | ∀ i, ω ∉ containsEvent (S i)} := by
    ext ω
    exact ⟨fun h i => h _ i.2.2, fun h R hR => h (false, ⟨R, hR⟩)⟩
  rw [← hE] at hJ
  refine hJ.trans (Real.exp_le_exp.mpr ?_)
  rw [mul_assoc (2 : ℝ), neg_div]
  apply neg_le_neg
  exact (div_le_div_iff₀ (by positivity : 0 < 2 * B) (by linarith : 0 < 2 * jansonDelta P S)).mpr
    (by nlinarith)

private lemma measure_complement_graph {n : ℕ} (p : I) (E : Set (Pair n → Bool)) :
    (randomSubsetLaw (fun _ : Pair n => σ p)).real E =
      (randomSubsetLaw (fun _ : Pair n => p)).real ((fun ω i => !(ω i)) ⁻¹' E) := by
  open ProbabilityTheory in
  have hf : MeasurePreserving (fun (ω : Pair n → Bool) i => !(ω i))
      (randomSubsetLaw (fun _ => p)) (randomSubsetLaw (fun _ => σ p)) := by
    apply measurePreserving_pi
    intro i
    exact ⟨measurable_of_finite _, by
      rw [map_bernoulliMeasure]
      simp [bernoulliMeasure_def, add_comm]⟩
  rw [← hf.map_eq, map_measureReal_apply hf.measurable (Set.toFinite E).measurableSet]

private lemma measure_exists_missed_set_le {n k L m : ℕ} (hk0 : 2 ≤ k) (hk : k + 1 ≤ 2 * L)
    (hm : k < m) (p : I) (hq : 0 < 1 - (p : ℝ))
    (hsmall : (k : ℝ) ^ 2 / (m - k : ℕ) ≤ (1 - (p : ℝ)) ^ L) :
    (randomSubsetLaw (fun _ : Pair n => p)).real
      {ω | ∃ V : Finset (Fin n), V.card = m ∧
        ∀ R ∈ V.powersetCard k, ¬ (pairGraph ω).IsIndepSet R} ≤
      (2 : ℝ) ^ n *
        Real.exp (-1 / (2 * (k + 1 : ℕ) * (((k : ℝ) ^ 2 / (m - k : ℕ)) ^ 2 / (1 - p)))) := by
  classical
  let sets := (univ : Finset (Fin n)).powersetCard m
  let D (V : Finset (Fin n)) : Set (Pair n → Bool) :=
    {ω | ∀ R ∈ V.powersetCard k, ¬ (pairGraph ω).IsIndepSet R}
  let μ := randomSubsetLaw (fun _ : Pair n => p)
  let e := Real.exp (-1 / (2 * (k + 1 : ℕ) * (((k : ℝ) ^ 2 / (m - k : ℕ)) ^ 2 / (1 - p))))
  have hs : {ω | ∃ V : Finset (Fin n), V.card = m ∧
      ∀ R ∈ V.powersetCard k, ¬ (pairGraph ω).IsIndepSet R} ⊆ ⋃ V ∈ sets, D V := by
    rintro ω ⟨V, hV, h⟩
    exact Set.mem_iUnion₂.mpr ⟨V, mem_powersetCard.mpr ⟨subset_univ _, hV⟩, h⟩
  have hD (V : Finset (Fin n)) (hV : V ∈ sets) : μ.real (D V) ≤ e := by
    have hc := (mem_powersetCard.mp hV).2
    let E := {ω | ∀ R ∈ V.powersetCard k, ω ∉ containsEvent (pairsIn R)}
    have he : D V = (fun (ω : Pair n → Bool) i => !(ω i)) ⁻¹' E := by
      ext ω
      simp [D, E, independent_iff, avoidEvent, containsEvent]
    rw [he, ← measure_complement_graph]
    simpa only [hc, unitInterval.coe_symm_eq, E, e] using
      fixed_set_miss_le V hk0 hk (hc ▸ hm) (σ p) hq (hc ▸ hsmall)
  refine (measureReal_mono (μ := μ) hs (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ((sum_le_sum hD).trans ?_))
  simp only [sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  exact_mod_cast (show sets.card ≤ 2 ^ n from calc
    _ ≤ (univ : Finset (Fin n)).powerset.card := card_le_card fun R hR =>
      mem_powerset.mpr (mem_powersetCard.mp hR).1
    _ = _ := by simp)

-- Remove an independent k-set and use one fresh colour. Once fewer than m
-- vertices remain, give each its own colour.
private lemma chromatic_number_le_of_large_sets {n k m : ℕ} (G : _root_.SimpleGraph (Fin n))
    (hk : 0 < k)
    (h : ∀ V : Finset (Fin n), V.card = m →
      ∃ R ∈ V.powersetCard k, G.IsIndepSet R) :
    G.chromaticNumber.toNat ≤ n / k + m := by
  classical
  have hcol (U : Finset (Fin n)) : (G.induce (U : Set (Fin n))).Colorable (U.card / k + m) := by
    induction U using Finset.strongInductionOn
    rename_i U ih
    by_cases hU : U.card < m
    · apply _root_.SimpleGraph.Colorable.mono _ (G.induce (U : Set (Fin n))).colorable_of_fintype
      simpa using hU.le.trans (Nat.le_add_left m (U.card / k))
    · obtain ⟨V, hVU, hc⟩ := exists_subset_card_eq (s := U) (le_of_not_gt hU)
      obtain ⟨R, hR, hI⟩ := h V hc
      obtain ⟨hRV, hcard⟩ := mem_powersetCard.mp hR
      have hsub := hRV.trans hVU
      have hleft : (U \ R).card = U.card - k := by rw [card_sdiff_of_subset hsub, hcard]
      have hlt : U \ R ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset, fun he => by
        have := congrArg Finset.card he; have := card_le_card hsub; omega⟩
      obtain ⟨C⟩ := ih (U \ R) hlt
      let f (v : U) : Fin ((U \ R).card / k + m + 1) := if hv : v.1 ∈ R then 0 else
        (C ⟨v.1, mem_sdiff.mpr ⟨v.2, hv⟩⟩).succ
      have hf : ∀ {v w : U}, G.Adj v.1 w.1 → f v ≠ f w := by
        rintro v w hvw
        by_cases hv : v.1 ∈ R <;> by_cases hw : w.1 ∈ R
        · exact (hI hv hw (G.ne_of_adj hvw) hvw).elim
        · simp [f, hv, hw, eq_comm (a := (0 : Fin _))]
        · simp [f, hv, hw]
        · simp only [f, dite_eq_right hv, dite_eq_right hw, ne_eq, Fin.succ_inj]
          exact C.valid (show G.Adj v.1 w.1 from hvw)
      have hc' : (U \ R).card / k + 1 = U.card / k := by
        have he : (U \ R).card + k = U.card := by have := card_le_card hsub; omega
        rw [← he, Nat.add_div_right _ hk]
      apply _root_.SimpleGraph.Colorable.mono (by omega :
        (U \ R).card / k + m + 1 ≤ U.card / k + m)
      exact ⟨_root_.SimpleGraph.Coloring.mk f hf⟩
  have hc : G.Colorable (n / k + m) := by
    let g : G →g (G.induce ((univ : Finset (Fin n)) : Set (Fin n))) :=
      ⟨fun v => ⟨v, mem_univ v⟩, fun {_ _} h => h⟩
    simpa using (hcol univ).of_hom g
  have hfinite := G.chromaticNumber_ne_top_iff_exists.mpr ⟨_, hc⟩
  exact_mod_cast (show (G.chromaticNumber.toNat : ℕ∞) ≤ ↑(n / k + m) by
    rw [ENat.natCast_toNat hfinite]; exact hc.chromaticNumber_le)

private lemma card_le_chromatic_number_mul {n K : ℕ} (G : _root_.SimpleGraph (Fin n))
    (h : ¬ ∃ R : Finset (Fin n), R.card = K + 1 ∧ G.IsIndepSet R) :
    n ≤ G.chromaticNumber.toNat * K := by
  classical
  let C := G.colorable_chromaticNumber_of_fintype.some
  have hf (c : Fin G.chromaticNumber.toNat) : (univ.filter (fun v => C v = c)).card ≤ K := by
    by_contra! hlarge
    obtain ⟨R, hR, hcard⟩ := exists_subset_card_eq hlarge
    apply h ⟨R, hcard, ?_⟩
    intro v hv w hw _ hadj
    exact C.valid hadj (((mem_filter.mp (hR hv)).2).trans (mem_filter.mp (hR hw)).2.symm)
  calc
    n = ∑ c, (univ.filter (fun v => C v = c)).card := by
      rw [sum_card_fiberwise_eq_card_filter]; simp
    _ ≤ ∑ _ : Fin G.chromaticNumber.toNat, K := sum_le_sum fun i _ => hf i
    _ = _ := by simp

private lemma measure_near_of_bounds {n k m K : ℕ} (p : I) {t ε u v : ℝ}
    (hn : 0 < (n : ℝ)) (hk : 0 < k) (hK : 0 < (K : ℝ)) (ht : 0 < t)
    (hl : 1 - ε ≤ 2 * t / K) (hu : (n / (k : ℝ) + m) / (n / (2 * t)) ≤ 1 + ε)
    (hlarge : (randomSubsetLaw (fun _ : Pair n => p)).real
      {ω | ∃ R : Finset (Fin n), R.card = K + 1 ∧ (pairGraph ω).IsIndepSet R} ≤ u)
    (hmiss : (randomSubsetLaw (fun _ : Pair n => p)).real
      {ω | ∃ V : Finset (Fin n), V.card = m ∧
        ∀ R ∈ V.powersetCard k, ¬ (pairGraph ω).IsIndepSet R} ≤ v) :
    1 - (u + v) ≤ (randomSubsetLaw (fun _ : Pair n => p)).real
      {ω | |((pairGraph ω).chromaticNumber.toNat : ℝ) / (n / (2 * t)) - 1| ≤ ε} := by
  classical
  let A : Set (Pair n → Bool) := {ω | ∃ R : Finset (Fin n), R.card = K + 1 ∧
    (pairGraph ω).IsIndepSet R}
  let D : Set (Pair n → Bool) := {ω | ∃ V : Finset (Fin n), V.card = m ∧
    ∀ R ∈ V.powersetCard k, ¬ (pairGraph ω).IsIndepSet R}
  let μ := randomSubsetLaw (fun _ : Pair n => p)
  have hprob : μ.real (A ∪ D) ≤ u + v := (measureReal_union_le _ _).trans (add_le_add hlarge hmiss)
  have hsub : (A ∪ D)ᶜ ⊆
      {ω | |((pairGraph ω).chromaticNumber.toNat : ℝ) / (n / (2 * t)) - 1| ≤ ε} := by
    intro ω hω
    have ha : ω ∉ A := fun h => hω (Or.inl h)
    have hd : ω ∉ D := fun h => hω (Or.inr h)
    have hnext : ∀ V : Finset (Fin n), V.card = m →
        ∃ R ∈ V.powersetCard k, (pairGraph ω).IsIndepSet R := by
      intro V hc
      by_contra! h
      exact hd ⟨V, hc, h⟩
    have hc : ((pairGraph ω).chromaticNumber.toNat : ℝ) ≤ (n / (k : ℝ)) + m := by
      have := chromatic_number_le_of_large_sets _ hk hnext
      exact (show ((pairGraph ω).chromaticNumber.toNat : ℝ) ≤ (↑(n / k : ℕ):ℝ) + m by
        exact_mod_cast this).trans (add_le_add_left Nat.cast_div_le _)
    have hd' : 0 < (n : ℝ) / (2 * t) := by positivity
    have h1 : 2 * t / K ≤ ((pairGraph ω).chromaticNumber.toNat : ℝ) / (n / (2 * t)) := by
      rw [div_le_div_iff₀ hK hd', mul_div_cancel₀ _ (by positivity : 2 * t ≠ 0)]
      exact_mod_cast card_le_chromatic_number_mul (pairGraph ω) ha
    change |((pairGraph ω).chromaticNumber.toNat : ℝ) / (n / (2 * t)) - 1| ≤ ε
    rw [abs_le]
    constructor
    · linarith only [hl.trans h1]
    · linarith only [(div_le_div_of_nonneg_right hc hd'.le).trans hu]
  have hs := measureReal_mono (μ := μ) hsub (measure_ne_top _ _)
  rw [measureReal_compl (Set.toFinite _).measurableSet, probReal_univ] at hs
  linarith

private lemma eventually_polylog {b d : ℝ} (hb : 1 < b) (hd : 0 < d) (C : ℝ) (hC : 0 ≤ C)
    (j : ℕ) : ∀ᶠ n : ℕ in atTop, C * (Real.logb b n) ^ j ≤ (n : ℝ) ^ d := by
  have h := ((isLittleO_log_rpow_rpow_atTop (j : ℝ) hd).const_mul_left
    (C / (Real.log b) ^ j)).eventuallyLE
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h, eventually_ge_atTop 1] with n hn hn1
  have hl := Real.log_nonneg (show 1 ≤ (n : ℝ) by exact_mod_cast hn1)
  have hb' := Real.log_pos hb
  simp only [Real.rpow_natCast, Real.norm_eq_abs] at hn
  rw [abs_of_nonneg (mul_nonneg (div_nonneg hC (pow_nonneg hb'.le _)) (pow_nonneg hl _)),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at hn
  simpa [Real.logb, div_pow, div_mul_eq_mul_div, mul_div_assoc] using hn

-- The choices m ≥ n/t² and k + 1 ≤ 2t give x ≤ 8t⁴/n. The ninth power of t
-- absorbs the factor k + 1 and the square of x in the Janson bound.
private lemma miss_exponent_le {n k m : ℕ} {t q : ℝ} (ht : 1 ≤ t) (hq : 0 < q)
    (hq' : q ≤ 1) (hn : 0 < (n : ℝ)) (hk : 0 < k) (hk' : (k : ℝ) + 1 ≤ 2 * t)
    (hm : (n : ℝ) / t ^ 2 ≤ m) (hbig : 1000 * t ^ 9 ≤ q * n) :
    k < m ∧ (k : ℝ) ^ 2 / (m - k : ℕ) ≤ 8 * t ^ 4 / n ∧
      -1 / (2 * (k + 1 : ℕ) * (((k : ℝ) ^ 2 / (m - k : ℕ)) ^ 2 / q)) ≤ (n : ℝ) * (-2) := by
  have ht' : 0 < t := by linarith
  have ht39 : t ^ 3 ≤ t ^ 9 := pow_le_pow_right₀ ht (by decide)
  have hmass : 4 * t ^ 3 ≤ n := by
    nlinarith [mul_le_mul_of_nonneg_right hq' hn.le, pow_nonneg ht'.le 9]
  have hklarge : (k : ℝ) < (n : ℝ) / t ^ 2 := by
    rw [lt_div_iff₀ (sq_pos_of_pos ht')]
    nlinarith [mul_le_mul_of_nonneg_right hk' (sq_nonneg t)]
  have hkm : k < m := by exact_mod_cast hklarge.trans_le hm
  have hdiff : (0 : ℝ) < (m - k : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hkm
  have h1 : (n : ℝ) ≤ 2 * t ^ 2 * (m - k : ℕ) := by
    rw [Nat.cast_sub hkm.le]
    have hm' := (div_le_iff₀ (sq_pos_of_pos ht')).mp hm
    nlinarith [mul_le_mul_of_nonneg_right hk' (sq_nonneg t)]
  have hk2 : (k : ℝ) ^ 2 ≤ (2 * t) ^ 2 := by gcongr; linarith
  let x := (k : ℝ) ^ 2 / (m - k : ℕ)
  have hx : x ≤ 8 * t ^ 4 / n := by
    dsimp [x]
    rw [div_le_div_iff₀ hdiff hn]
    calc
      _ ≤ (2 * t) ^ 2 * (2 * t ^ 2 * (m - k : ℕ)) := mul_le_mul hk2 h1 hn.le (sq_nonneg _)
      _ = _ := by ring
  have hx' : 0 < x := by dsimp [x]; positivity
  refine ⟨hkm, hx, ?_⟩
  rw [neg_div, neg_le_iff_add_nonneg]
  change 0 ≤ (n : ℝ) * (-2) + 1 / (2 * (k + 1 : ℕ) * (x ^ 2 / q))
  have hden : 0 < 2 * (k + 1 : ℕ) * (x ^ 2 / q) := by positivity
  have hnum : (2 * (n : ℝ)) * (2 * ((k : ℝ) + 1)) * x ^ 2 ≤ q := calc
    _ ≤ (2 * (n : ℝ)) * (2 * (2 * t)) * (8 * t ^ 4 / n) ^ 2 := by gcongr
    _ = 512 * t ^ 9 / n := by field_simp; ring
    _ ≤ q := (div_le_iff₀ hn).mpr (by nlinarith [pow_nonneg ht'.le 9])
  have hd := (le_div_iff₀ hden).mpr (show (2 * (n : ℝ)) * (2 * (k + 1 : ℕ) * (x ^ 2 / q)) ≤ 1 by
    rw [← mul_div_assoc, ← mul_div_assoc, div_le_one hq, Nat.cast_add_one]
    linarith only [hnum])
  linarith only [hd]

private lemma complement_rpow_logb {q : ℝ} (hq : 0 < q) (hq1 : q < 1) {n : ℕ} (hn : 0 < (n : ℝ))
    (z : ℝ) : q ^ (Real.logb (1 / q) n * z) = (n : ℝ) ^ (-z) := by
  let b := 1 / q
  have hb : 1 < b := (one_lt_div hq).mpr (by simpa)
  calc
    _ = (b ^ (Real.logb b n * z))⁻¹ := by
      rw [← Real.inv_rpow (zero_lt_one.trans hb).le]
      simp [b]
    _ = _ := by rw [Real.rpow_mul (zero_lt_one.trans hb).le,
      Real.rpow_logb (zero_lt_one.trans hb) hb.ne' hn, Real.rpow_neg hn.le]

private lemma measure_large_independent_set_le_rpow {n H : ℕ} (p : I) (hq : 0 < 1 - (p : ℝ))
    (d : ℝ) (hd : 0 < d) (hn : 1 ≤ (n : ℝ)) (hbase : (n : ℝ) * (1 - (p : ℝ)) ^ H ≤ (n : ℝ) ^ (-d)) :
    (randomSubsetLaw (fun _ : Pair n => p)).real
      {ω | ∃ R : Finset (Fin n), R.card = 2 * H + 1 ∧ (pairGraph ω).IsIndepSet R} ≤
      (n : ℝ) ^ (-d) := by
  have hcast : (2 * H + 1).choose 2 = H * (2 * H + 1) := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_comm 2 H, ← mul_assoc,
      Nat.mul_div_cancel _ (by decide : 0 < 2), mul_comm]
  refine (measure_large_independent_set_le p _).trans ?_
  calc
    _ ≤ ((n : ℝ) ^ (2 * H + 1)) * (1 - (p : ℝ)) ^ ((2 * H + 1).choose 2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_pow n (2 * H + 1)) (by positivity)
    _ = ((n : ℝ) * (1 - (p : ℝ)) ^ H) ^ (2 * H + 1) := by rw [hcast, pow_mul, mul_pow]
    _ ≤ ((n : ℝ) ^ (-d)) ^ (2 * H + 1) := pow_le_pow_left₀ (by positivity) hbase _
    _ ≤ _ := by
      simpa only [pow_one] using pow_le_pow_of_le_one
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        (Real.rpow_le_one_of_one_le_of_nonpos hn (neg_nonpos.mpr hd.le))
        (show 1 ≤ 2 * H + 1 by omega)

private lemma colour_ratios {n k m K : ℕ} {t d ε : ℝ}
    (hn : 0 < (n : ℝ)) (ht : 1 ≤ t) (hd : 0 < d) (hd1 : d ≤ 1 / 8) (hdε : 5 * d ≤ ε)
    (htd : 4 ≤ t * d) (hK : 0 < (K : ℝ)) (hKhi : (K : ℝ) ≤ 2 * t * (1 + 2 * d))
    (hklow : 2 * t * (1 - 2 * d) ≤ k) (hmhi : (m : ℝ) ≤ 2 * (n / t ^ 2)) :
    1 - ε ≤ 2 * t / K ∧ (n / (k : ℝ) + m) / (n / (2 * t)) ≤ 1 + ε := by
  have ht' : 0 < t := by linarith
  have h1 : 0 < 1 - 2 * d := by linarith
  have hk : 0 < (k : ℝ) := lt_of_lt_of_le (by positivity) hklow
  constructor
  · refine le_trans (show 1 - ε ≤ 1 - 2 * d by linarith) ((le_div_iff₀ hK).mpr ?_)
    calc
      _ ≤ (1 - 2 * d) * (2 * t * (1 + 2 * d)) := mul_le_mul_of_nonneg_left hKhi h1.le
      _ ≤ _ := by nlinarith [mul_nonneg ht'.le (sq_nonneg d)]
  · have hkr : 2 * t / k ≤ 1 + 4 * d := (div_le_iff₀ hk).mpr (calc
        2 * t ≤ (1 + 4 * d) * (2 * t * (1 - 2 * d)) := by
          nlinarith [mul_nonneg (mul_nonneg ht'.le hd.le) (show 0 ≤ 1 - 4 * d by linarith)]
        _ ≤ _ := mul_le_mul_of_nonneg_left hklow (by positivity))
    have hmr : (m : ℝ) * (2 * t) / n ≤ d := by
      calc
        _ ≤ (2 * (n / t ^ 2)) * (2 * t) / n := by gcongr
        _ = 4 / t := by field_simp; ring
        _ ≤ _ := (div_le_iff₀ ht').mpr (by linarith)
    calc
      _ = 2 * t / k + (m : ℝ) * (2 * t) / n := by field_simp
      _ ≤ _ := by linarith only [hkr, hmr, hdε]

-- With t = log_b n, use sizes just below and just above 2t. The two failure
-- probabilities are bounded by an inverse power of n and a geometric sequence.
private lemma eventually_measure_near_ge (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {d ε : ℝ} (hd : 0 < d) (hd1 : d ≤ 1 / 8) (hdε : 5 * d ≤ ε) :
    ∀ᶠ n : ℕ in atTop,
      1 - ((n : ℝ) ^ (-d) + (2 * Real.exp (-2)) ^ n) ≤
      (randomSubsetLaw (fun _ : Pair n => p)).real
        {ω | |((pairGraph ω).chromaticNumber.toNat : ℝ) /
          (n / (2 * Real.logb (1 / (1 - (p : ℝ))) n)) - 1| ≤ ε} := by
  let q : ℝ := 1 - p
  let b := 1 / q
  have hq : 0 < q := sub_pos.mpr hp1
  have hq1 : q < 1 := sub_lt_self _ hp0
  have hb : 1 < b := (one_lt_div hq).mpr (by simpa)
  have hg := (Real.tendsto_logb_atTop hb).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hg.eventually_ge_atTop (4 / d), eventually_ge_atTop 1,
    eventually_polylog hb hd 8 (by norm_num) 4,
    eventually_polylog hb (by norm_num : (0 : ℝ) < 1) (1000 / q) (by positivity) 9]
    with n ht0 hn0 hg4 hg9
  let t := Real.logb b n
  change 4 / d ≤ t at ht0
  have htd := (div_le_iff₀ hd).mp ht0
  have ht : 1 ≤ t := by
    by_contra! h
    linarith [mul_lt_mul_of_pos_right h hd]
  have ht' : 0 < t := by linarith
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn0
  have hn : 0 < (n : ℝ) := by linarith
  let L := ⌊t * (1 - d)⌋₊
  let H := ⌈t * (1 + d)⌉₊
  let k := 2 * L - 1
  let m := ⌈(n : ℝ) / t ^ 2⌉₊
  have hL : (L : ℝ) ≤ t * (1 - d) := Nat.floor_le (mul_nonneg ht'.le (by linarith))
  have hL' : t * (1 - d) < (L : ℝ) + 1 := Nat.lt_floor_add_one _
  have hH : t * (1 + d) ≤ (H : ℝ) := Nat.le_ceil _
  have hH' : (H : ℝ) < t * (1 + d) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hL2 : 2 ≤ L := by
    have : (2 : ℝ) ≤ L := by nlinarith [mul_nonneg ht'.le (show 0 ≤ 1 - 2 * d by linarith)]
    exact_mod_cast this
  have hk2 : 2 ≤ k := by dsimp [k]; omega
  have hkL : k + 1 = 2 * L := by dsimp [k]; omega
  have hkre : (k : ℝ) + 1 = 2 * (L : ℝ) := by exact_mod_cast hkL
  have hku : (k : ℝ) + 1 ≤ 2 * t := by nlinarith [mul_nonneg ht'.le hd.le]
  have hkl : 2 * t * (1 - 2 * d) ≤ (k : ℝ) := by linarith
  have hK : 0 < (↑(2 * H):ℝ) := by push_cast; nlinarith [mul_nonneg ht'.le hd.le]
  have hKhi : (↑(2 * H):ℝ) ≤ 2 * t * (1 + 2 * d) := by push_cast; linarith
  have hbig : 1000 * t ^ 9 ≤ q * n := by
    change (1000 / q) * t ^ 9 ≤ (n : ℝ) ^ (1 : ℝ) at hg9
    rw [Real.rpow_one, div_mul_eq_mul_div, div_le_iff₀ hq] at hg9
    linarith
  have hm := Nat.le_ceil ((n : ℝ) / t ^ 2)
  have hmhi : (m : ℝ) ≤ 2 * (n / t ^ 2) := by
    have hmin : 1 ≤ (n : ℝ) / t ^ 2 := (le_div_iff₀ (sq_pos_of_pos ht')).mpr (by
      nlinarith [pow_le_pow_right₀ ht (by decide : 2 ≤ 9), mul_le_mul_of_nonneg_right hq1.le hn.le,
        pow_nonneg ht'.le 9])
    have he : (m : ℝ) < (n : ℝ) / t ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  obtain ⟨hkm, hx, htail⟩ := miss_exponent_le ht hq hq1.le hn (by omega : 0 < k) hku hm hbig
  have hcL : (n : ℝ) ^ d / n ≤ q ^ L := calc
    _ = (n : ℝ) ^ (-(1 - d)) := by
      rw [show -(1 - d) = d - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
    _ = q ^ (t * (1 - d)) := (complement_rpow_logb hq hq1 hn _).symm
    _ ≤ _ := by rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_ge hq hq1.le hL
  have hcH : (n : ℝ) * q ^ H ≤ (n : ℝ) ^ (-d) := calc
    _ ≤ (n : ℝ) * q ^ (t * (1 + d)) := by
      rw [← Real.rpow_natCast]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hq hq1.le hH) hn.le
    _ = _ := by
      rw [complement_rpow_logb hq hq1 hn, show -(1 + d) = -d - 1 by ring, Real.rpow_sub hn,
        Real.rpow_one, mul_div_cancel₀ _ hn.ne']
  have hmiss := measure_exists_missed_set_le (n := n) hk2 hkL.le hkm p hq
    (hx.trans ((div_le_div_of_nonneg_right hg4 hn.le).trans hcL))
  have htail' := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htail)
    (by positivity : 0 ≤ (2 : ℝ) ^ n)
  rw [Real.exp_nat_mul, ← mul_pow] at htail'
  obtain ⟨hl, hu⟩ := colour_ratios hn ht hd hd1 hdε htd hK hKhi hkl hmhi
  exact measure_near_of_bounds p hn (by omega : 0 < k) hK ht' hl hu
    (measure_large_independent_set_le_rpow p hq d hd hn1 hcH) (hmiss.trans htail')

/-- **Chromatic number of dense random graphs (Bollobás).** For a constant `0 < p < 1` and
`b = 1/(1 - p)`, with high probability `χ(G(n, p)) = (1 + o(1)) n / (2 log_b n)`: for every
`ε > 0`, the probability that `χ(G(n, p))` lies within a factor `1 ± ε` of `n / (2 log_b n)` tends
to `1` (B. Bollobás, *Combinatorica* 8 (1988); Frieze and Karoński, *Introduction to Random
Graphs*, 2016, Theorem 7.7). At `p = 1/2`, `b = 2` and the value is `n / (2 log₂ n)`. -/
theorem tendsto_measureReal_chromaticNumber_near (p : I) (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (randomSubsetLaw (fun _ : Pair n => p)).real
      {ω | |((pairGraph ω).chromaticNumber.toNat : ℝ) /
          (n / (2 * Real.logb (1 / (1 - (p : ℝ))) n)) - 1| ≤ ε}) atTop (𝓝 1) := by
  let d := min (ε / 8) (1 / 8)
  have hd : 0 < d := lt_min (by positivity) (by norm_num)
  have hd1 : d ≤ 1 / 8 := min_le_right _ _
  have hdε : 5 * d ≤ ε := by linarith [show d ≤ ε / 8 from min_le_left _ _]
  have hratio : 2 * Real.exp (-2) < 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
    linarith [Real.add_one_le_exp 2]
  have h1 := (tendsto_rpow_neg_atTop hd).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hratio
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' _ tendsto_const_nhds
    (eventually_measure_near_ge p hp0 hp1 hd hd1 hdε)
    (Eventually.of_forall fun _ => measureReal_le_one)
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (h1.add h2)

end MathlibExt.Combinatorics.SimpleGraph.RandomGraphChromaticNumberWanted
