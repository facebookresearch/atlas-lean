/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.RandomGraphIsolatedVertices
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm

/-!
# No isolated vertices at the connectivity threshold

When `n pₙ - log n → c`, the probability that every vertex of the binomial random graph
has a neighbor tends to `exp (-exp (-c))`. We bound the probability by truncating
inclusion–exclusion and compute the limit of each binomial moment of the isolated-vertex count.
-/

open MeasureTheory Filter Topology unitInterval Finset
  MathlibExt.Probability.Combinatorics.RandomSubset
  MathlibExt.Combinatorics.RamseyErdosLowerBound
  MathlibExt.Combinatorics.SimpleGraph.RandomGraphIsolatedVertices

namespace MathlibExt.Combinatorics.SimpleGraph.RandomGraphConnectivityWanted

private noncomputable def isolated {n : ℕ} (ω : Pair n → Bool) : Finset (Fin n) := by
  classical
  exact univ.filter fun v => ∀ w, ¬ (pairGraph ω).Adj v w

private lemma joint_isolation {n : ℕ} (s : Finset (Fin n)) (p : I) :
    (randomSubsetLaw (fun _ : Pair n => p)).real {ω | s ⊆ isolated ω} =
      (1 - (p : ℝ)) ^ (n.choose 2 - (n - s.card).choose 2) := by
  classical
  -- The forbidden edges are all pairs except those entirely outside the prescribed set.
  have he : {ω | s ⊆ isolated ω} = avoidEvent (pairsIn sᶜ)ᶜ := by
    ext ω
    have hv (v : Fin n) : v ∈ isolated ω ↔ ω ∈ avoidEvent (pairsAt v) := by
      rw [← setOf_isolated_eq_avoidEvent]
      simp [isolated]
    constructor
    · intro h e he
      have hn : ¬ e.val ⊆ sᶜ := by simpa [pairsIn] using he
      obtain ⟨v, hve, hvs⟩ := Finset.not_subset.mp hn
      exact (hv v).mp (h (by simpa using hvs)) e (by simpa [pairsAt] using hve)
    · intro h v hvs
      apply (hv v).mpr
      intro e he
      have hve : v ∈ e.val := by simpa [pairsAt] using he
      exact h e (by simpa [pairsIn] using
        (show ¬ e.val ⊆ sᶜ from fun hsub => (mem_compl.mp (hsub hve)) hvs))
  simp [he, randomSubsetLaw_real_avoidEvent, card_compl, card_pairsIn]

private noncomputable def moment (n : ℕ) (p : I) (k : ℕ) : ℝ :=
  n.choose k * (1 - (p : ℝ)) ^ (n.choose 2 - (n - k).choose 2)

private lemma integral_choose (n : ℕ) (p : I) (k : ℕ) :
    (∫ ω, ((isolated ω).card.choose k : ℝ) ∂randomSubsetLaw (fun _ : Pair n => p)) =
      moment n p k := by
  classical
  let sets := (univ : Finset (Fin n)).powersetCard k
  have hcount (ω : Pair n → Bool) : ((isolated ω).card.choose k : ℝ) =
      ∑ s ∈ sets, ({ω | s ⊆ isolated ω} : Set (Pair n → Bool)).indicator 1 ω := by
    have hfilter : sets.filter (· ⊆ isolated ω) = (isolated ω).powersetCard k := by
      ext s
      simp [sets, and_comm]
    simp [Set.indicator_apply, hfilter]
  simp_rw [hcount]
  rw [integral_finsetSum _ fun _ _ => Integrable.of_finite]
  simp_rw [integral_indicator_one ((Set.toFinite _).measurableSet), joint_isolation]
  calc
    _ = ∑ _s ∈ sets, (1 - (p : ℝ)) ^ (n.choose 2 - (n - k).choose 2) := by
      apply sum_congr rfl
      intro s hs
      rw [(mem_powersetCard.mp hs).2]
    _ = _ := by simp [sets, moment, nsmul_eq_mul]

private lemma exponent_eq {n k : ℕ} (hk : k ≤ n) (hn : 1 ≤ n) :
    n.choose 2 - (n - k).choose 2 + k.choose 2 = (n - 1) * k := by
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_add, Nat.cast_sub (Nat.choose_le_choose 2 (Nat.sub_le ..)), Nat.cast_mul,
    Nat.cast_sub hn]
  simp only [Nat.cast_choose_two, Nat.cast_sub hk, Nat.cast_one]
  ring

private lemma tendsto_moment (c : ℝ) (p : ℕ → I)
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n - Real.log n) atTop (𝓝 c)) (k : ℕ) :
    Tendsto (fun n => moment n (p n) k) atTop (𝓝 (Real.exp (-c) ^ k / k.factorial)) := by
  have hlog := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  have hp0 : Tendsto (fun n => (p n : ℝ)) atTop (𝓝 0) := by
    have h := (hp.mul tendsto_one_div_atTop_nhds_zero_nat).add hlog
    simp only [mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    simp [Function.comp_apply]
    field_simp
    ring
  have hq : Tendsto (fun n => 1 - (p n : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hp0
  -- The product of k single-vertex probabilities counts each internal pair twice.
  have hfirst := tendsto_mul_one_sub_pow c (fun n => (p n : ℝ)) hp
  have h := (ProbabilityTheory.tendsto_choose_mul_pow_atTop k hfirst).div
    (hq.pow (k.choose 2)) (by simp)
  simp only [one_pow, div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop k, eventually_ge_atTop 1,
    hq.eventually_ne one_ne_zero] with n hk hn hne
  dsimp only [moment, Pi.div_apply]
  rw [← pow_mul, ← exponent_eq hk hn, pow_add]
  field_simp

private noncomputable def alternatingChoose (r m : ℕ) : ℝ :=
  ∑ k ∈ range (m + 1), (-1 : ℝ) ^ k * r.choose k

-- For a positive count, the alternating partial sum has the sign of its last term.
private lemma alternating_bounds (r m : ℕ) :
    alternatingChoose r (2 * m + 1) ≤ (if r = 0 then 1 else 0) ∧
      (if r = 0 then 1 else 0) ≤ alternatingChoose r (2 * m) := by
  cases r with
  | zero =>
    have h (j : ℕ) : alternatingChoose 0 j = 1 := by
      simp [alternatingChoose, sum_range_succ', Nat.choose_zero_succ]
    simp [h]
  | succ r =>
    have h (j : ℕ) : alternatingChoose (r + 1) j = (-1 : ℝ) ^ j * r.choose j := by
      unfold alternatingChoose
      exact_mod_cast (Int.alternating_sum_range_choose_eq_choose (n := r) (m := j))
    simp [h, pow_add, pow_mul]

private noncomputable def partialMoment (n : ℕ) (p : I) (m : ℕ) : ℝ :=
  ∑ k ∈ range (m + 1), (-1 : ℝ) ^ k * moment n p k

private lemma probability_bounds (n : ℕ) (p : I) (m : ℕ) :
    partialMoment n p (2 * m + 1) ≤ (randomSubsetLaw (fun _ : Pair n => p)).real
      {ω | ∀ v, ∃ w, (pairGraph ω).Adj v w} ∧
    (randomSubsetLaw (fun _ : Pair n => p)).real {ω | ∀ v, ∃ w, (pairGraph ω).Adj v w} ≤
      partialMoment n p (2 * m) := by
  classical
  let μ := randomSubsetLaw (fun _ : Pair n => p)
  let A : Set (Pair n → Bool) := {ω | ∀ v, ∃ w, (pairGraph ω).Adj v w}
  have hA (ω : Pair n → Bool) : ω ∈ A ↔ (isolated ω).card = 0 := by
    simp [A, isolated, filter_eq_empty_iff]
  have hind (ω : Pair n → Bool) : A.indicator (1 : (Pair n → Bool) → ℝ) ω =
      if (isolated ω).card = 0 then 1 else 0 := by
    simp [Set.indicator_apply, hA]
  have hpart (j : ℕ) : (∫ ω, alternatingChoose (isolated ω).card j ∂μ) =
      partialMoment n p j := by
    simp only [alternatingChoose, integral_finsetSum _ (fun _ _ => Integrable.of_finite),
      integral_const_mul, μ, integral_choose, partialMoment]
  change partialMoment n p _ ≤ μ.real A ∧ μ.real A ≤ partialMoment n p _
  rw [← integral_indicator_one (Set.toFinite A).measurableSet, ← hpart, ← hpart]
  constructor
  · exact integral_mono Integrable.of_finite Integrable.of_finite fun ω => by
      rw [hind]
      exact (alternating_bounds _ _).1
  · exact integral_mono Integrable.of_finite Integrable.of_finite fun ω => by
      rw [hind]
      exact (alternating_bounds _ _).2

/-- **No isolated vertex at the connectivity threshold (Erdős–Rényi).** If `n pₙ - log n → c`,
then `P(G(n, pₙ) has no isolated vertex) → e^{-e^{-c}}`: the number of isolated vertices converges
in distribution to a Poisson law of mean `e^{-c}` (Frieze and Karoński, *Introduction to Random
Graphs*, 2016, Theorem 3.1 (ii) and (3.2) with `k = 0`; the first moment
`n (1 - pₙ)^{n-1} → e^{-c}` is
`MathlibExt.Combinatorics.SimpleGraph.RandomGraphIsolatedVertices.tendsto_mul_one_sub_pow`). -/
public theorem tendsto_measureReal_no_isolated (c : ℝ) (p : ℕ → I)
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n - Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (randomSubsetLaw (fun _ : Pair n => p n)).real
      {ω | ∀ v, ∃ w, (pairGraph ω).Adj v w}) atTop (𝓝 (Real.exp (-Real.exp (-c)))) := by
  let a := Real.exp (-c)
  let S (j : ℕ) := ∑ k ∈ range j, (-a) ^ k / k.factorial
  have hseries : Tendsto S atTop (𝓝 (Real.exp (-a))) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (-a)).tendsto_sum_nat
  have hpart (m : ℕ) : Tendsto (fun n => partialMoment n (p n) m) atTop (𝓝 (S (m + 1))) := by
    apply tendsto_finsetSum
    intro k _
    have h := (tendsto_moment c p hp k).const_mul ((-1 : ℝ) ^ k)
    simpa [a, ← mul_div_assoc, ← mul_pow] using h
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨m, hm⟩ := eventually_atTop.mp (tendsto_order.mp hseries |>.1 b hb)
    filter_upwards [tendsto_order.mp (hpart (2 * m + 1)) |>.1 b (hm _ (by omega))] with n hn
    exact hn.trans_le (probability_bounds n (p n) m).1
  · intro b hb
    obtain ⟨m, hm⟩ := eventually_atTop.mp (tendsto_order.mp hseries |>.2 b hb)
    filter_upwards [tendsto_order.mp (hpart (2 * m)) |>.2 b (hm _ (by omega))] with n hn
    exact (probability_bounds n (p n) m).2.trans_lt hn

end MathlibExt.Combinatorics.SimpleGraph.RandomGraphConnectivityWanted
