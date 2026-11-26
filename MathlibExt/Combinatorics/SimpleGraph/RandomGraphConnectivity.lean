/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.RandomGraphNoIsolated
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast

/-!
# The connectivity threshold of `G(n, p)`

At `p = (log n + c)/n` the number of isolated vertices of `G(n, p)` is asymptotically Poisson with
mean `e^{-c}`, and with high probability `G(n, p)` has no component of order between `2` and
`⌊n/2⌋`. For `n ≥ 2`, on the event that it has no such component, `G(n, p)` is connected exactly
when it has no isolated vertex. The probabilities of the two events therefore differ by at most
the probability that such a component exists, which tends to `0`, and
`P(G(n, p) is connected) → e^{-e^{-c}}` (P. Erdős and A. Rényi, "On random graphs I", *Publ.
Math. Debrecen* 6 (1959); A. Frieze and M. Karoński, *Introduction to Random Graphs*, Cambridge
University Press 2016, Theorem 3.1 (ii) for the Poisson limit, and Theorem 4.1 with its proof,
which states the `G(n, p)` form used here).
The limiting probability of having no isolated vertex is proved in
`MathlibExt.Combinatorics.SimpleGraph.RandomGraphNoIsolated`.

`G(n, p)` is `pairGraph ω` for `ω` drawn from `randomSubsetLaw` with constant probability `p`.
The hypothesis `pₙ = (log n + c)/n` for all large `n` is satisfiable for every real `c`
(`RandomGraphIsolatedVertices.exists_prob_eventually_eq`), and implies `n pₙ - log n → c`
(`RandomGraphIsolatedVertices.tendsto_mul_sub_log_of_eventually_eq`).
-/

open MeasureTheory Filter Topology unitInterval Finset
  MathlibExt.Probability.Combinatorics.RandomSubset
  MathlibExt.Combinatorics.RamseyErdosLowerBound

namespace MathlibExt.Combinatorics.SimpleGraph.RandomGraphConnectivityWanted

private def crossing {n : ℕ} (s : Finset (Fin n)) : Finset (Pair n) :=
  (pairsIn s ∪ pairsIn sᶜ)ᶜ

private lemma card_crossing {n : ℕ} (s : Finset (Fin n)) :
    (crossing s).card = s.card * (n - s.card) := by
  have hd : Disjoint (pairsIn s) (pairsIn sᶜ) := by
    refine disjoint_left.mpr fun e he hf => ?_
    obtain ⟨v, hv⟩ := card_pos.mp (show 0 < e.val.card by rw [e.property]; decide)
    have hs : e.val ⊆ s := by simpa [pairsIn] using he
    have ht : e.val ⊆ sᶜ := by simpa [pairsIn] using hf
    exact mem_compl.mp (ht hv) (hs hv)
  have hall : pairsIn (univ : Finset (Fin n)) = univ := by simp [pairsIn]
  have htotal := card_pairsIn (univ : Finset (Fin n))
  rw [hall] at htotal
  simp only [card_univ, Fintype.card_fin] at htotal
  have hle := card_le_univ (pairsIn s ∪ pairsIn sᶜ)
  rw [card_union_of_disjoint hd, card_pairsIn, card_pairsIn, card_compl, Fintype.card_fin,
    htotal] at hle
  simp only [crossing, card_compl, htotal, card_union_of_disjoint hd, card_pairsIn,
    Fintype.card_fin]
  have hs : s.card ≤ n := by simpa using card_le_univ s
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
  simp only [Nat.cast_choose_two, Nat.cast_sub hs]
  ring

-- No edge crosses this cut, and at least one edge lies on its specified side.
private def cutEvent {n : ℕ} (s : Finset (Fin n)) : Set (Pair n → Bool) :=
  avoidEvent (crossing s) \ avoidEvent (crossing s ∪ pairsIn s)

private lemma measure_cutEvent {n : ℕ} (s : Finset (Fin n)) (p : I) :
    (randomSubsetLaw (fun _ : Pair n => p)).real (cutEvent s) =
      (1 - (p : ℝ)) ^ (s.card * (n - s.card)) *
        (1 - (1 - (p : ℝ)) ^ (s.card.choose 2)) := by
  have hsub : avoidEvent (crossing s ∪ pairsIn s) ⊆ avoidEvent (crossing s) :=
    fun _ h e he => h e (mem_union_left _ he)
  have hd : Disjoint (crossing s) (pairsIn s) :=
    disjoint_left.mpr fun e he hi => (mem_compl.mp he) (mem_union_left _ hi)
  rw [cutEvent, measureReal_sdiff hsub (Set.toFinite _).measurableSet,
    randomSubsetLaw_real_avoidEvent, randomSubsetLaw_real_avoidEvent,
    prod_const, prod_const, card_union_of_disjoint hd, card_crossing, card_pairsIn, pow_add]
  ring

private lemma mem_cutEvent_of_closed {n : ℕ} {ω : Pair n → Bool} {s : Finset (Fin n)}
    (hs : s.Nonempty) (hclosed : ∀ u v, (pairGraph ω).Adj u v → (u ∈ s ↔ v ∈ s))
    (hneighbor : ∀ v, ∃ w, (pairGraph ω).Adj v w) : ω ∈ cutEvent s := by
  constructor
  · intro e he
    by_contra! ht
    obtain ⟨u, v, huv, heq⟩ := card_eq_two.mp e.property
    have he' : (⟨{u, v}, card_pair huv⟩ : Pair n) = e := Subtype.ext heq.symm
    have hadj : (pairGraph ω).Adj u v := ⟨huv, by simpa [he'] using ht⟩
    have hc := hclosed u v hadj
    have hmem := mem_compl.mp he
    by_cases hu : u ∈ s
    · exact hmem (mem_union_left _ (by simp [pairsIn, heq, insert_subset_iff, hu, hc.mp hu]))
    · exact hmem (mem_union_right _ (by simp [pairsIn, heq, insert_subset_iff, hu, mt hc.mpr hu]))
  · obtain ⟨u, hu⟩ := hs
    obtain ⟨v, hv⟩ := hneighbor u
    have hvs := (hclosed u v hv).mp hu
    obtain ⟨hne, he⟩ := hv
    intro h
    have hi : (⟨{u, v}, card_pair hne⟩ : Pair n) ∈ pairsIn s := by
      simp [pairsIn, insert_subset_iff, hu, hvs]
    have := h _ (mem_union_right _ hi)
    simp_all

private lemma exists_small_cut {n : ℕ} (hn : 0 < n) (ω : Pair n → Bool)
    (hd : ¬ (pairGraph ω).Connected) (hv : ∀ v, ∃ w, (pairGraph ω).Adj v w) :
    ∃ s : Finset (Fin n), s.card ≤ n / 2 ∧ ω ∈ cutEvent s := by
  classical
  let u : Fin n := ⟨0, hn⟩
  obtain ⟨v, hvu⟩ : ∃ v, ¬ (pairGraph ω).Reachable u v := by
    by_contra! h
    exact hd (((pairGraph ω).connected_iff_exists_forall_reachable).mpr ⟨u, h⟩)
  let s := univ.filter ((pairGraph ω).Reachable u)
  have hmem (w) : w ∈ s ↔ (pairGraph ω).Reachable u w := by simp [s]
  have hc (x y) (h : (pairGraph ω).Adj x y) : x ∈ s ↔ y ∈ s := by
    rw [hmem, hmem]
    exact ⟨fun hx => hx.trans h.reachable, fun hy => hy.trans h.symm.reachable⟩
  by_cases hsize : s.card ≤ n / 2
  · have hne : s.Nonempty := ⟨u, (hmem u).mpr .rfl⟩
    exact ⟨s, hsize, mem_cutEvent_of_closed hne hc hv⟩
  · have hne : sᶜ.Nonempty := ⟨v, mem_compl.mpr (mt (hmem v).mp hvu)⟩
    refine ⟨sᶜ, ?_, mem_cutEvent_of_closed hne (fun x y h => ?_) hv⟩
    · simp only [card_compl, Fintype.card_fin]
      omega
    · simp only [mem_compl]
      exact (hc x y h).not

private noncomputable def cutTerm (n k : ℕ) (p : ℝ) : ℝ :=
  n.choose k * (1 - p) ^ (k * (n - k)) * (1 - (1 - p) ^ (k.choose 2))

private lemma measure_no_isolated_disconnected_le {n : ℕ} (hn : 0 < n) (p : I) :
    (randomSubsetLaw (fun _ : Pair n => p)).real
      {ω | (∀ v, ∃ w, (pairGraph ω).Adj v w) ∧ ¬ (pairGraph ω).Connected} ≤
        ∑ k ∈ range (n / 2 + 1), cutTerm n k p := by
  let μ := randomSubsetLaw (fun _ : Pair n => p)
  have : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (randomSubsetLaw _))
  let sets (k : ℕ) := (univ : Finset (Fin n)).powersetCard k
  let cuts (k : ℕ) := ⋃ s ∈ sets k, cutEvent s
  have hsub : {ω | (∀ v, ∃ w, (pairGraph ω).Adj v w) ∧ ¬ (pairGraph ω).Connected} ⊆
      ⋃ k ∈ range (n / 2 + 1), cuts k := by
    rintro ω ⟨hv, hd⟩
    obtain ⟨s, hk, hs⟩ := exists_small_cut hn ω hd hv
    exact Set.mem_biUnion (mem_range_succ_iff.mpr hk)
      (Set.mem_biUnion (mem_powersetCard.mpr ⟨subset_univ _, rfl⟩) hs)
  refine (measureReal_mono hsub (measure_ne_top μ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ?_)
  apply sum_le_sum
  intro k _
  refine (measureReal_biUnion_finset_le (μ := μ) (sets k) cutEvent).trans ?_
  apply le_of_eq
  calc ∑ s ∈ sets k, μ.real (cutEvent s) =
      ∑ _s ∈ sets k, (1 - (p : ℝ)) ^ (k * (n - k)) * (1 - (1 - (p : ℝ)) ^ (k.choose 2)) := by
        apply sum_congr rfl
        intro s hs
        dsimp only [μ]
        rw [measure_cutEvent, (mem_powersetCard.mp hs).2]
    _ = _ := by simp [sets, cutTerm, nsmul_eq_mul, mul_assoc]

private lemma absence_pow_le {n k : ℕ} (hk : k ≤ n) (p : I) :
    (1 - (p : ℝ)) ^ (k * (n - k)) ≤ Real.exp (-(p : ℝ) * (n - k)) ^ k := by
  rw [Nat.mul_comm, pow_mul]
  apply pow_le_pow_left₀ (pow_nonneg (sub_nonneg.mpr p.2.2) _)
  calc (1 - (p : ℝ)) ^ (n - k) ≤ Real.exp (-(p : ℝ)) ^ (n - k) :=
        pow_le_pow_left₀ (sub_nonneg.mpr p.2.2) (Real.one_sub_le_exp_neg _) _
    _ = _ := by rw [← Real.exp_nat_mul, Nat.cast_sub hk, mul_comm]

-- For k p ≤ 1 the absent crossing edges cancel the factor n^k in the count of cuts.
-- Requiring an internal edge contributes the extra factor p.
private lemma small_cut_bound {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) (p : I) (c : ℝ)
    (hp : (n : ℝ) * p = Real.log n + c) (hsmall : (k : ℝ) * p ≤ 1) :
    cutTerm n k p ≤ p * ((2 * Real.exp (1 - c)) ^ k / k.factorial) := by
  have hp0 := p.2.1
  have hfactor : (n : ℝ) * Real.exp (-(p : ℝ) * (n - k)) ≤ Real.exp (1 - c) := by
    conv_lhs => lhs; rw [← Real.exp_log (Nat.cast_pos.mpr hn : 0 < (n : ℝ))]
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith
  have hi : 1 - (1 - (p : ℝ)) ^ (k.choose 2) ≤ 2 ^ k * (p : ℝ) := by
    have hb := one_add_mul_le_pow (a := -(p : ℝ)) (by linarith [p.2.2]) (k.choose 2)
    have hc : ((k.choose 2 : ℕ) : ℝ) ≤ 2 ^ k := by exact_mod_cast Nat.choose_le_two_pow k 2
    rw [← sub_eq_add_neg] at hb
    linarith [mul_le_mul_of_nonneg_right hc p.2.1]
  have h0 := pow_nonneg (sub_nonneg.mpr p.2.2) (k * (n - k))
  calc cutTerm n k p ≤ (n.choose k : ℝ) * (1 - (p : ℝ)) ^ (k * (n - k)) * (2 ^ k * p) :=
        mul_le_mul_of_nonneg_left hi (mul_nonneg (Nat.cast_nonneg _) h0)
    _ ≤ ((n : ℝ) ^ k / k.factorial) * Real.exp (-(p : ℝ) * (n - k)) ^ k * (2 ^ k * p) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (Nat.choose_le_pow_div k n) (absence_pow_le hk p) h0 (by positivity))
          (by positivity)
    _ = p * ((2 * ((n : ℝ) * Real.exp (-(p : ℝ) * (n - k)))) ^ k / k.factorial) := by
        simp only [mul_pow]; ring
    _ ≤ _ := by gcongr

private noncomputable def largeRatio (x : ℝ) : ℝ := Real.exp 1 * (x * Real.exp (-(1 / 2) * x))

-- For k p > 1 the binomial bound (en/k)^k suffices even when k reaches n/2.
private lemma large_cut_bound {n k : ℕ} (hk : k ≤ n / 2) (p : I)
    (hlarge : 1 < (k : ℝ) * p) :
    cutTerm n k p ≤ largeRatio (n * (p : ℝ)) ^ k := by
  have hp0 := p.2.1
  have hkn : k ≤ n := by omega
  have hhalf : (2 : ℝ) * k ≤ n := by exact_mod_cast (show 2 * k ≤ n by omega)
  have hkpos : (0 : ℝ) < k := by
    by_contra! h
    have := mul_nonpos_of_nonpos_of_nonneg h p.2.1
    linarith
  have hcount : (n.choose k : ℝ) ≤ (Real.exp 1 / k * n) ^ k :=
    (single_le_sum (f := fun i => (n.choose i : ℝ)) (fun _ _ => by positivity)
      (self_mem_range_succ k)).trans (Real.sum_choose_le_exp_pow hkn)
  have hbase : Real.exp 1 / k * n * Real.exp (-(p : ℝ) * (n - k)) ≤
      largeRatio (n * (p : ℝ)) := by
    unfold largeRatio
    rw [← mul_assoc]
    apply mul_le_mul
    · have hd : Real.exp 1 / k ≤ Real.exp 1 * p := by
        rw [div_le_iff₀ hkpos]
        calc Real.exp 1 ≤ Real.exp 1 * ((k : ℝ) * p) :=
              le_mul_of_one_le_right (by positivity) hlarge.le
          _ = _ := by ring
      calc Real.exp 1 / k * n ≤ (Real.exp 1 * p) * n := by gcongr
        _ = _ := by ring
    · apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hhalf p.2.1]
    · positivity
    · positivity
  calc cutTerm n k p ≤ (n.choose k : ℝ) * (1 - (p : ℝ)) ^ (k * (n - k)) := by
        apply mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg _)
          (pow_nonneg (sub_nonneg.mpr p.2.2) _))
        linarith [pow_nonneg (sub_nonneg.mpr p.2.2) (k.choose 2)]
    _ ≤ (Real.exp 1 / k * n) ^ k * Real.exp (-(p : ℝ) * (n - k)) ^ k := by
        exact mul_le_mul hcount (absence_pow_le hkn p) (pow_nonneg (sub_nonneg.mpr p.2.2) _)
          (by positivity)
    _ ≤ _ := by rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hbase _

private lemma cut_sum_bound {n : ℕ} (hn : 0 < n) (p : I) (c : ℝ)
    (hp : (n : ℝ) * p = Real.log n + c) (hr : largeRatio (n * (p : ℝ)) ≤ 1 / 2) :
    ∑ k ∈ range (n / 2 + 1), cutTerm n k p ≤
      p * Real.exp (2 * Real.exp (1 - c)) + 4 * largeRatio (n * (p : ℝ)) := by
  let a := 2 * Real.exp (1 - c)
  let r := largeRatio (n * (p : ℝ))
  have hp0 := p.2.1
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hr0 : 0 ≤ r := by dsimp [r, largeRatio]; positivity
  have ht (k : ℕ) (hk : k ≤ n / 2) :
      cutTerm n k p ≤ p * (a ^ k / k.factorial) + 2 * r * (1 / 2) ^ k := by
    by_cases h : (k : ℝ) * p ≤ 1
    · exact (small_cut_bound hn (by omega) p c hp h).trans (le_add_of_nonneg_right (by positivity))
    · calc cutTerm n k p ≤ r ^ k := large_cut_bound hk p (lt_of_not_ge h)
           _ ≤ 2 * r * (1 / 2) ^ k := by
              cases k with
              | zero => simp at h
              | succ j =>
                rw [pow_succ, pow_succ]
                calc r ^ j * r ≤ (1 / 2) ^ j * r :=
                      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr0 hr _) hr0
                  _ = _ := by ring
           _ ≤ _ := le_add_of_nonneg_left (by positivity)
  have hg : ∑ k ∈ range (n / 2 + 1), (1 / 2 : ℝ) ^ k ≤ 2 := by
    convert geom_sum_Ico_le_of_lt_one (m := 0) (n := n / 2 + 1)
      (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) using 1 <;> norm_num
  calc ∑ k ∈ range (n / 2 + 1), cutTerm n k p ≤
      ∑ k ∈ range (n / 2 + 1), (p * (a ^ k / k.factorial) + 2 * r * (1 / 2) ^ k) :=
        sum_le_sum fun k hk => ht k (mem_range_succ_iff.mp hk)
    _ = p * (∑ k ∈ range (n / 2 + 1), a ^ k / k.factorial) +
        2 * r * ∑ k ∈ range (n / 2 + 1), (1 / 2) ^ k := by rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ p * Real.exp a + 2 * r * 2 := by
      gcongr
      exact Real.sum_le_exp_of_nonneg ha _
    _ = _ := by dsimp only [r, a]; ring

private lemma tendsto_largeRatio : Tendsto largeRatio atTop (𝓝 0) := by
  unfold largeRatio
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 2) (by norm_num)
  simpa only [Real.rpow_one, mul_zero] using h.const_mul (Real.exp 1)

/-- **Connectivity threshold of `G(n, p)` (Erdős–Rényi).** If `pₙ = (log n + c)/n` for all large
`n`, then `P(G(n, pₙ) is connected) → e^{-e^{-c}}` (P. Erdős and A. Rényi, 1959; Frieze and
Karoński, *Introduction to Random Graphs*, 2016, Theorem 4.1, whose proof establishes this
`G(n, p)` form before transferring it to `G(n, m)` with `m = n(log n + c)/2`). -/
public theorem tendsto_measureReal_connected (c : ℝ) (p : ℕ → I)
    (hp : ∀ᶠ n : ℕ in atTop, (p n : ℝ) = (Real.log n + c) / n) :
    Tendsto (fun n : ℕ => (randomSubsetLaw (fun _ : Pair n => p n)).real
      {ω | (pairGraph ω).Connected}) atTop (𝓝 (Real.exp (-Real.exp (-c)))) := by
  let μ (n : ℕ) := randomSubsetLaw (fun _ : Pair n => p n)
  let A (n : ℕ) : Set (Pair n → Bool) := {ω | ∀ v, ∃ w, (pairGraph ω).Adj v w}
  let C (n : ℕ) : Set (Pair n → Bool) := {ω | (pairGraph ω).Connected}
  have hμ (n) : IsProbabilityMeasure (μ n) := inferInstanceAs (IsProbabilityMeasure
    (randomSubsetLaw _))
  have hA := tendsto_measureReal_no_isolated c p
    (RandomGraphIsolatedVertices.tendsto_mul_sub_log_of_eventually_eq c _ hp)
  have heq : ∀ᶠ n : ℕ in atTop, (n : ℝ) * p n = Real.log n + c := by
    filter_upwards [hp, eventually_gt_atTop 0] with n h hn
    rw [h, mul_comm, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')]
  have hx : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop atTop :=
    (tendsto_atTop_add_const_right _ c
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).congr' (heq.mono fun _ h => h.symm)
  have hr := tendsto_largeRatio.comp hx
  have hp0 : Tendsto (fun n => (p n : ℝ)) atTop (𝓝 0) := by
    have hlog := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    have h := hlog.add (tendsto_one_div_atTop_nhds_zero_nat.const_mul c)
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    filter_upwards [hp] with n hn
    simp [hn, Function.comp_apply, div_eq_mul_inv, add_mul]
  have herror := (hp0.mul_const (Real.exp (2 * Real.exp (1 - c)))).add (hr.const_mul 4)
  simp only [zero_mul, mul_zero, add_zero] at herror
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa only [sub_zero] using hA.sub herror) hA
  · filter_upwards [heq, eventually_ge_atTop 2, hr.eventually (ge_mem_nhds (by norm_num :
        (0 : ℝ) < 1 / 2))] with n h hn hratio
    have := Fin.nontrivial_iff_two_le.mpr hn
    have hsub : C n ⊆ A n := fun ω hω => hω.preconnected.exists_adj_of_nontrivial
    have hd := (measure_no_isolated_disconnected_le (by omega : 0 < n) (p n)).trans
      (cut_sum_bound (by omega) (p n) c h hratio)
    change (μ n).real (A n \ C n) ≤ _ at hd
    rw [measureReal_sdiff hsub (Set.toFinite _).measurableSet] at hd
    change (μ n).real (A n) - _ ≤ (μ n).real (C n)
    dsimp only [Function.comp_apply]
    linarith only [hd]
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have := Fin.nontrivial_iff_two_le.mpr hn
    exact measureReal_mono (fun ω (hω : (pairGraph ω).Connected) =>
      hω.preconnected.exists_adj_of_nontrivial)

end MathlibExt.Combinatorics.SimpleGraph.RandomGraphConnectivityWanted
