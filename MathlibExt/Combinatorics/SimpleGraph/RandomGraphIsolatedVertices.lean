/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.RamseyErdosLowerBound
public import MathlibExt.Probability.Combinatorics.RandomSubset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Isolated vertices of `G(n, p)` at the connectivity threshold

In the binomial random graph `G(n, p)` a vertex is isolated with probability `(1 - p)^(n - 1)`,
so the expected number of isolated vertices is `n (1 - p)^(n - 1)`. When `n p - log n → c`, for
example at `p = (log n + c)/n`, this first moment tends to `e^{-c}`. This is the first-moment part
of the analysis of the connectivity threshold: the number of isolated vertices is then
asymptotically Poisson with mean `e^{-c}`, and with high probability isolated vertices are the
only obstruction to connectivity, so `P(G(n, p) connected) → e^{-e^{-c}}` (A. Frieze and
M. Karoński, *Introduction to Random Graphs*, Cambridge University Press 2016, Theorem 3.1 with
(3.1) and (3.3), and Theorem 4.1 with its proof). Those two statements are recorded in
`WantedExt.Combinatorics.SimpleGraph.RandomGraphConnectivityWanted`.

Main results:
* `measureReal_isolated`: `P(v is isolated) = (1 - p)^(n - 1)`.
* `measureReal_exists_isolated_le`: `P(G(n, p) has an isolated vertex) ≤ n (1 - p)^(n - 1)`.
* `tendsto_mul_one_sub_pow`: `n (1 - pₙ)^(n - 1) → e^{-c}` when `n pₙ - log n → c`.
* `tendsto_mul_sub_log_of_eventually_eq`: `pₙ = (log n + c)/n` eventually gives `n pₙ - log n → c`.
* `eventually_measureReal_exists_isolated_le`: hence, for every `δ > 0`, eventually
  `P(G(n, pₙ) has an isolated vertex) ≤ e^{-c} + δ`.
* `exists_prob_eventually_eq`: such a sequence of probabilities exists for every real `c`.

`G(n, p)` is `pairGraph ω` for the random set `ω` of pairs drawn from
`MathlibExt.Probability.Combinatorics.RandomSubset.randomSubsetLaw` with constant probability `p`,
as in `MathlibExt.Combinatorics.RandomGraphTriangleThreshold`.
-/

@[expose] public section

open MeasureTheory Filter Topology unitInterval Real Finset
  MathlibExt.Probability.Combinatorics.RandomSubset
  MathlibExt.Combinatorics.RamseyErdosLowerBound

namespace MathlibExt.Combinatorics.SimpleGraph.RandomGraphIsolatedVertices

variable {n : ℕ}

/-- **Pairs at a vertex.** The two-element subsets of `Fin n` containing `v`, the possible edges
of a graph on `Fin n` at `v`; there are `n - 1` of them (`card_pairsAt`). -/
def pairsAt (v : Fin n) : Finset (Pair n) :=
  univ.filter fun s => v ∈ s.1

lemma card_pairsAt (v : Fin n) : (pairsAt v).card = n - 1 := by
  classical
  have h : (univ.erase v).card = (pairsAt v).card := by
    refine card_bij (fun w hw => (⟨{v, w}, card_pair (Ne.symm (ne_of_mem_erase hw))⟩ : Pair n))
      ?_ ?_ ?_
    · intro w hw
      simp [pairsAt]
    · intro a ha b hb hab
      have hab' : ({v, a} : Finset (Fin n)) = {v, b} := congrArg Subtype.val hab
      have : a ∈ ({v, b} : Finset (Fin n)) := hab' ▸ mem_insert_of_mem (mem_singleton_self a)
      rcases mem_insert.1 this with h | h
      · exact absurd h (ne_of_mem_erase ha)
      · exact mem_singleton.1 h
    · intro s hs
      simp only [pairsAt, mem_filter, mem_univ, true_and] at hs
      obtain ⟨x, y, hxy, hs'⟩ := card_eq_two.1 s.2
      rw [hs'] at hs
      rcases mem_insert.1 hs with rfl | h
      · exact ⟨y, mem_erase.2 ⟨Ne.symm hxy, mem_univ _⟩, Subtype.ext hs'.symm⟩
      · rw [mem_singleton.1 h]
        exact ⟨x, mem_erase.2 ⟨hxy, mem_univ _⟩, Subtype.ext (hs'.trans (pair_comm x y)).symm⟩
  rw [← h, card_erase_of_mem (mem_univ v), card_univ, Fintype.card_fin]

/-- **Isolation is avoidance of the pairs at a vertex.** The vertex `v` is isolated in
`pairGraph ω` exactly when `ω` contains no pair at `v` (Frieze and Karoński, *Introduction to
Random Graphs*, 2016, Section 3.1, the indicator `I_v` of an isolated vertex). -/
theorem setOf_isolated_eq_avoidEvent (v : Fin n) :
    {ω : Pair n → Bool | ∀ w, ¬ (pairGraph ω).Adj v w} = avoidEvent (pairsAt v) := by
  ext ω
  simp only [Set.mem_ofPred_eq, avoidEvent]
  constructor
  · intro h s hs
    simp only [pairsAt, mem_filter, mem_univ, true_and] at hs
    obtain ⟨x, y, hxy, hs'⟩ := card_eq_two.1 s.2
    by_contra hω
    rw [Bool.not_eq_false] at hω
    rw [hs'] at hs
    rcases mem_insert.1 hs with rfl | h'
    · exact h y ⟨hxy, by rw [← hω]; exact congrArg ω (Subtype.ext hs'.symm)⟩
    · obtain rfl := mem_singleton.1 h'
      exact h x ⟨Ne.symm hxy, by
        rw [← hω]; exact congrArg ω (Subtype.ext (hs'.trans (pair_comm x v)).symm)⟩
  · rintro h w ⟨hvw, hω⟩
    have hmem : (⟨{v, w}, card_pair hvw⟩ : Pair n) ∈ pairsAt v := by simp [pairsAt]
    rw [h _ hmem] at hω
    exact Bool.false_ne_true hω

/-- **Probability that a vertex of `G(n, p)` is isolated.** Each of the `n - 1` pairs at `v` is
absent independently with probability `1 - p`, so `P(v is isolated) = (1 - p)^(n - 1)` (Frieze and
Karoński, *Introduction to Random Graphs*, 2016, Section 3.1, `E I_v` in (3.3)). -/
theorem measureReal_isolated (p : I) (v : Fin n) :
    (randomSubsetLaw (fun _ : Pair n => p)).real {ω | ∀ w, ¬ (pairGraph ω).Adj v w} =
      (1 - (p : ℝ)) ^ (n - 1) := by
  rw [setOf_isolated_eq_avoidEvent, randomSubsetLaw_real_avoidEvent, prod_const, card_pairsAt]

/-- **First moment bound for isolated vertices of `G(n, p)`.** The probability that `G(n, p)` has
an isolated vertex is at most the expected number `n (1 - p)^(n - 1)` of isolated vertices (union
bound, i.e. the first moment method, with `E X₀ = n (1 - p)^{n-1}` from Frieze and Karoński,
*Introduction to Random Graphs*, 2016, Section 3.1). -/
theorem measureReal_exists_isolated_le (p : I) :
    (randomSubsetLaw (fun _ : Pair n => p)).real {ω | ∃ v, ∀ w, ¬ (pairGraph ω).Adj v w} ≤
      (n : ℝ) * (1 - (p : ℝ)) ^ (n - 1) := by
  set μ := randomSubsetLaw (fun _ : Pair n => p)
  have hsub : {ω | ∃ v, ∀ w, ¬ (pairGraph ω).Adj v w} ⊆
      ⋃ v ∈ (univ : Finset (Fin n)), {ω | ∀ w, ¬ (pairGraph ω).Adj v w} := by
    intro ω ⟨v, hv⟩
    exact Set.mem_biUnion (mem_univ v) hv
  calc μ.real {ω | ∃ v, ∀ w, ¬ (pairGraph ω).Adj v w}
      ≤ μ.real (⋃ v ∈ (univ : Finset (Fin n)), {ω | ∀ w, ¬ (pairGraph ω).Adj v w}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ v : Fin n, μ.real {ω | ∀ w, ¬ (pairGraph ω).Adj v w} :=
        measureReal_biUnion_finset_le _ _
    _ = (n : ℝ) * (1 - (p : ℝ)) ^ (n - 1) := by
        simp only [μ, measureReal_isolated, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `log n / n → 0` and `(log n)² / n → 0` along the natural numbers. -/
private lemma tendsto_log_pow_div_nat (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log n ^ k / n) atTop (𝓝 0) := by
  have h := (tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun n => ?_
  simp

/-- **First moment of isolated vertices at the connectivity threshold.** If
`n pₙ - log n → c`, then the expected number `n (1 - pₙ)^(n - 1)` of isolated vertices of
`G(n, pₙ)` tends to `e^{-c}` (A. Frieze and M. Karoński, *Introduction to Random Graphs*, 2016,
equation (3.1), computed in (3.3) in the proof of Theorem 3.1). -/
theorem tendsto_mul_one_sub_pow (c : ℝ) (p : ℕ → ℝ)
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n - Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (n : ℝ) * (1 - p n) ^ (n - 1)) atTop (𝓝 (Real.exp (-c))) := by
  set cn : ℕ → ℝ := fun n => (n : ℝ) * p n - Real.log n with hcn
  have hlog1 := tendsto_log_pow_div_nat 1
  have hlog2 := tendsto_log_pow_div_nat 2
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  -- `pₙ = (log n + cₙ)/n`, so `pₙ → 0` and `n pₙ² → 0`
  have hpeq : ∀ n : ℕ, 1 ≤ n → p n = (Real.log n + cn n) / n := by
    intro n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    simp only [hcn]
    field_simp
    ring
  have hp0 : Tendsto p atTop (𝓝 0) := by
    have := hlog1.add (hp.mul hinv)
    simp only [pow_one, mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hpeq n hn]
    ring
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) * p n ^ 2) atTop (𝓝 0) := by
    have := (hlog2.add ((hp.const_mul 2).mul hlog1)).add ((hp.pow 2).mul hinv)
    simp only [pow_one, mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    rw [hpeq n hn]
    field_simp
    ring
  -- eventually `0 ≤ pₙ < 1`
  have hlogc : ∀ᶠ n : ℕ in atTop, 1 - c < Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (1 - c)
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 0 ≤ p n ∧ p n < 1 := by
    filter_upwards [eventually_ge_atTop 1, hlogc, hp.eventually (lt_mem_nhds (by linarith :
      c - 1 < c)), hp0.eventually (gt_mem_nhds one_pos)] with n hn hlc hcl hlt
    refine ⟨hn, ?_, hlt⟩
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have : 0 < (n : ℝ) * p n := by linarith
    exact (pos_of_mul_pos_right this hnpos.le).le
  -- the logarithm of `n (1 - pₙ)^(n-1)` is squeezed between two sequences tending to `-c`
  set L : ℕ → ℝ := fun n => Real.log n + ((n : ℝ) - 1) * Real.log (1 - p n)
  have hU : Tendsto (fun n : ℕ => -cn n + p n) atTop (𝓝 (-c)) := by
    simpa using hp.neg.add hp0
  have hD : Tendsto (fun n : ℕ => -cn n + p n - ((n : ℝ) - 1) * p n ^ 2 / (1 - p n)) atTop
      (𝓝 (-c)) := by
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) - 1) * p n ^ 2) atTop (𝓝 0) := by
      have := h1.sub (hp0.pow 2)
      simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
      exact this.congr fun n => by ring
    have h3 : Tendsto (fun n : ℕ => ((n : ℝ) - 1) * p n ^ 2 / (1 - p n)) atTop (𝓝 0) := by
      have := h2.div (tendsto_const_nhds.sub hp0) (by norm_num : (1 : ℝ) - 0 ≠ 0)
      rwa [zero_div] at this
    simpa using hU.sub h3
  have hLU : ∀ᶠ n : ℕ in atTop, L n ≤ -cn n + p n := by
    filter_upwards [hev] with n ⟨hn, hp0', hp1⟩
    have hlog : Real.log (1 - p n) ≤ -p n := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 - p n)
      linarith
    have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    calc L n ≤ Real.log n + ((n : ℝ) - 1) * (-p n) := by
          simp only [L]; gcongr
      _ = -cn n + p n := by simp only [hcn]; ring
  have hLD : ∀ᶠ n : ℕ in atTop, -cn n + p n - ((n : ℝ) - 1) * p n ^ 2 / (1 - p n) ≤ L n := by
    filter_upwards [hev] with n ⟨hn, hp0', hp1⟩
    have hpos : (0 : ℝ) < 1 - p n := by linarith
    have hlog : -(p n / (1 - p n)) ≤ Real.log (1 - p n) := by
      have := Real.one_sub_inv_le_log_of_pos hpos
      have e : 1 - (1 - p n)⁻¹ = -(p n / (1 - p n)) := by field_simp; ring
      linarith
    have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    calc -cn n + p n - ((n : ℝ) - 1) * p n ^ 2 / (1 - p n)
        = Real.log n + ((n : ℝ) - 1) * (-(p n / (1 - p n))) := by
          simp only [hcn]
          field_simp
          ring
      _ ≤ L n := by simp only [L]; gcongr
  have hL : Tendsto L atTop (𝓝 (-c)) := tendsto_of_tendsto_of_tendsto_of_le_of_le' hD hU hLD hLU
  refine ((Real.continuous_exp.tendsto _).comp hL).congr' ?_
  filter_upwards [hev] with n ⟨hn, hp0', hp1⟩
  have hpos : (0 : ℝ) < 1 - p n := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp, L]
  rw [Real.exp_add, Real.exp_log hnpos, ← Real.log_rpow hpos, Real.exp_log (by positivity),
    ← Real.rpow_natCast, Nat.cast_sub hn, Nat.cast_one]

/-- **The exact threshold sequence satisfies `n pₙ - log n → c`.** If `pₙ = (log n + c)/n` for all
large `n`, then `n pₙ - log n` is eventually equal to `c`. -/
theorem tendsto_mul_sub_log_of_eventually_eq (c : ℝ) (p : ℕ → ℝ)
    (hp : ∀ᶠ n : ℕ in atTop, p n = (Real.log n + c) / n) :
    Tendsto (fun n : ℕ => (n : ℝ) * p n - Real.log n) atTop (𝓝 c) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hp, eventually_ge_atTop 1] with n hpn hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [hpn]
  field_simp
  ring

/-- **Isolated vertices are rare beyond `e^{-c}`.** If `n pₙ - log n → c`, then for every
`δ > 0`, eventually `P(G(n, pₙ) has an isolated vertex) ≤ e^{-c} + δ` (first moment method, with
`E X₀ = n (1 - p)^{n-1}` from Frieze and Karoński, *Introduction to Random Graphs*, 2016,
Section 3.1). The exact limit `1 - e^{-e^{-c}}` is the Poisson statement of Theorem 3.1 (ii)
there, recorded in `WantedExt.Combinatorics.SimpleGraph.RandomGraphConnectivityWanted`. -/
theorem eventually_measureReal_exists_isolated_le (c : ℝ) (p : ℕ → I)
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n - Real.log n) atTop (𝓝 c)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (randomSubsetLaw (fun _ : Pair n => p n)).real
      {ω | ∃ v, ∀ w, ¬ (pairGraph ω).Adj v w} ≤ Real.exp (-c) + δ := by
  have h := tendsto_mul_one_sub_pow c (fun n => (p n : ℝ)) hp
  filter_upwards [h.eventually (ge_mem_nhds (lt_add_of_pos_right _ hδ))] with n hn
  exact (measureReal_exists_isolated_le (p n)).trans hn

/-- **The threshold probabilities exist.** For every real `c` there is a sequence of
probabilities `pₙ ∈ [0, 1]` with `pₙ = (log n + c)/n` for all large `n`; so the hypotheses of
`tendsto_mul_one_sub_pow` and of the connectivity statements are jointly satisfiable. -/
theorem exists_prob_eventually_eq (c : ℝ) :
    ∃ p : ℕ → I, ∀ᶠ n : ℕ in atTop, (p n : ℝ) = (Real.log n + c) / n := by
  refine ⟨fun n => Set.projIcc 0 1 zero_le_one ((Real.log n + c) / n), ?_⟩
  have hlogc : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log n + c :=
    (tendsto_atTop_add_const_right _ c
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 0
  have hq0 : Tendsto (fun n : ℕ => (Real.log n + c) / n) atTop (𝓝 0) := by
    have := (tendsto_log_pow_div_nat 1).add (tendsto_one_div_atTop_nhds_zero_nat.const_mul c)
    simp only [pow_one, mul_zero, add_zero] at this
    refine this.congr' (Eventually.of_forall fun n => ?_)
    simp only
    ring
  filter_upwards [hlogc, eventually_gt_atTop 0, hq0.eventually (ge_mem_nhds one_pos)]
    with n hlc hn hle
  rw [Set.projIcc_of_mem _ ⟨by positivity, hle⟩]

end MathlibExt.Combinatorics.SimpleGraph.RandomGraphIsolatedVertices
