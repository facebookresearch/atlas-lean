/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.PadicNumbers

import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Strassmann's theorem over the p-adic numbers

A nonzero p-adic power series whose coefficients tend to zero has finitely many zeros in
the closed unit ball.
-/

namespace Padic

/-- Factoring out a zero of a convergent power series over `ℚ_[p]`. -/
private theorem strassmann_factor (p : ℕ) [Fact p.Prime] (b : ℕ → ℚ_[p])
    (hb : Filter.Tendsto b Filter.cofinite (nhds 0))
    (α y : ℚ_[p]) (hα : ‖α‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    (∑' m, b m * y ^ m - ∑' m, b m * α ^ m
      = (y - α) * ∑' i, (∑' m, b (m + (i + 1)) * α ^ m) * y ^ i)
    ∧ (∀ i C, (∀ m > i, ‖b m‖ ≤ C) →
        ‖∑' m, b (m + (i + 1)) * α ^ m‖ ≤ C)
    ∧ Filter.Tendsto (fun i => ∑' m, b (m + (i + 1)) * α ^ m)
        Filter.cofinite (nhds 0) := by
  classical
  have hαpow : ∀ n, ‖α ^ n‖ ≤ 1 := fun n => by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hα
  have hypow : ∀ n, ‖y ^ n‖ ≤ 1 := fun n => by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hy
  set G : ℕ × ℕ → ℚ_[p] := fun q =>
    if q.2 < q.1 then b q.1 * (y ^ q.2 * α ^ (q.1 - 1 - q.2)) else 0
  have hGval : ∀ m i, G (m, i)
      = if i < m then b m * (y ^ i * α ^ (m - 1 - i)) else 0 := fun m i => rfl
  have hGbound : ∀ q : ℕ × ℕ, ‖G q‖ ≤ ‖b q.1‖ := by
    rintro ⟨m, i⟩
    by_cases h : i < m
    · rw [hGval, ite_eq_left h]
      have e1 : ‖y ^ i‖ ≤ 1 := hypow _
      have e2 : ‖α ^ (m - 1 - i)‖ ≤ 1 := hαpow _
      calc ‖b m * (y ^ i * α ^ (m - 1 - i))‖
          = ‖b m‖ * (‖y ^ i‖ * ‖α ^ (m - 1 - i)‖) := by
            rw [norm_mul, norm_mul]
        _ ≤ ‖b m‖ * (1 * 1) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            exact mul_le_mul e1 e2 (norm_nonneg _) zero_le_one
        _ = ‖b m‖ := by ring
    · rw [hGval, ite_eq_right h, norm_zero]
      exact norm_nonneg _
  have hdom : ∀ F : ℕ → ℚ_[p], ∀ t : ℕ, (∀ n, ‖F n‖ ≤ ‖b (n + t)‖) →
      Filter.Tendsto F Filter.cofinite (nhds 0) := by
    intro F t hF
    rw [Filter.tendsto_def]
    intro s hs
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
    have hbε : ∀ᶠ m in Filter.cofinite, dist (b m) 0 < ε := by
      have hmem : Metric.ball (0 : ℚ_[p]) ε ∈ nhds (0 : ℚ_[p]) :=
        Metric.ball_mem_nhds _ hε
      have h2 := hb hmem
      filter_upwards [h2] with m hm
      have hm' : b m ∈ Metric.ball (0 : ℚ_[p]) ε := hm
      exact Metric.mem_ball.mp hm'
    have hfin : {m | ¬ dist (b m) 0 < ε}.Finite :=
      Filter.eventually_cofinite.mp hbε
    have hinj : Function.Injective (fun n => n + t) := fun a c h =>
      Nat.add_right_cancel h
    have hpre : ((fun n => n + t) ⁻¹' {m | ¬ dist (b m) 0 < ε}).Finite :=
      Set.Finite.preimage (Set.injOn_of_injective hinj) hfin
    have hsub : {n | ¬ F n ∈ s}
        ⊆ (fun n => n + t) ⁻¹' {m | ¬ dist (b m) 0 < ε} := by
      intro n hn
      have hn' : ¬ F n ∈ s := hn
      intro hcon
      apply hn'
      apply hball
      rw [Metric.mem_ball]
      calc dist (F n) 0 = ‖F n‖ := dist_zero_right _
        _ ≤ ‖b (n + t)‖ := hF n
        _ = dist (b (n + t)) 0 := (dist_zero_right _).symm
        _ < ε := hcon
    exact Filter.eventually_cofinite.mpr (Set.Finite.subset hpre hsub)
  have hG0 : Filter.Tendsto G Filter.cofinite (nhds 0) := by
    rw [Filter.tendsto_def]
    intro s hs
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
    have hbε : ∀ᶠ m in Filter.cofinite, dist (b m) 0 < ε := by
      have hmem : Metric.ball (0 : ℚ_[p]) ε ∈ nhds (0 : ℚ_[p]) :=
        Metric.ball_mem_nhds _ hε
      have h2 := hb hmem
      filter_upwards [h2] with m hm
      have hm' : b m ∈ Metric.ball (0 : ℚ_[p]) ε := hm
      exact Metric.mem_ball.mp hm'
    have hfin : {m | ¬ dist (b m) 0 < ε}.Finite :=
      Filter.eventually_cofinite.mp hbε
    obtain ⟨F, hF⟩ := Set.Finite.exists_finset_coe hfin
    have hsub : {q | ¬ G q ∈ s} ⊆ ↑(F ×ˢ Finset.range (F.sup id + 1)) := by
      intro q hq
      have hq' : ¬ G q ∈ s := hq
      obtain ⟨m, i⟩ := q
      have hdi : ¬ dist (G (m, i)) 0 < ε := by
        intro hcon
        exact hq' (hball (Metric.mem_ball.mpr hcon))
      have him : i < m := by
        by_contra hcon
        have h0 : G (m, i) = 0 := by
          rw [hGval]
          exact ite_eq_right hcon
        rw [h0] at hdi
        have hpos : dist (0 : ℚ_[p]) 0 < ε := by
          rw [dist_self]
          exact hε
        exact hdi hpos
      have hmF : m ∈ F := by
        have hmem : m ∈ {m | ¬ dist (b m) 0 < ε} := by
          intro hcon
          apply hdi
          calc dist (G (m, i)) 0 = ‖G (m, i)‖ := dist_zero_right _
            _ ≤ ‖b m‖ := hGbound (m, i)
            _ = dist (b m) 0 := (dist_zero_right _).symm
            _ < ε := hcon
        rw [← hF] at hmem
        exact Finset.mem_coe.mp hmem
      have hiR : i ∈ Finset.range (F.sup id + 1) := by
        rw [Finset.mem_range]
        have hle : m ≤ F.sup id := Finset.le_sup (f := id) hmF
        omega
      exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hmF, hiR⟩)
    exact Filter.eventually_cofinite.mpr
      (Set.Finite.subset (Finset.finite_toSet _) hsub)
  have hGsum2 : Summable G :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hG0
  have hGunc : Summable (Function.uncurry fun m i => G (m, i)) := hGsum2
  have hrow : ∀ m, Summable (fun i => G (m, i)) := by
    intro m
    have hinj : Function.Injective (fun i : ℕ => (m, i)) := by
      intro a c h
      exact congrArg Prod.snd h
    exact hGsum2.comp_injective hinj
  have hcol : ∀ i, Summable (fun m => G (m, i)) := by
    intro i
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    apply hdom _ 0
    intro n
    exact hGbound (n, i)
  have hsum : ∀ z : ℚ_[p], ‖z‖ ≤ 1 → Summable (fun m => b m * z ^ m) := by
    intro z hz
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    apply hdom _ 0
    intro n
    calc ‖b n * z ^ n‖ = ‖b n‖ * ‖z ^ n‖ := norm_mul _ _
      _ ≤ ‖b n‖ * 1 := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [norm_pow]
          exact pow_le_one₀ (norm_nonneg _) hz
      _ = ‖b (n + 0)‖ := by rw [Nat.add_zero, mul_one]
  have hsumk : ∀ i, Summable (fun k => b (k + (i + 1)) * α ^ k) := by
    intro i
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    apply hdom _ (i + 1)
    intro k
    calc ‖b (k + (i + 1)) * α ^ k‖ = ‖b (k + (i + 1))‖ * ‖α ^ k‖ := norm_mul _ _
      _ ≤ ‖b (k + (i + 1))‖ * 1 := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [norm_pow]
          exact pow_le_one₀ (norm_nonneg _) hα
      _ = ‖b (k + (i + 1))‖ := by ring
  have hSbound : ∀ m, ‖∑' i, G (m, i)‖ ≤ ‖b m‖ := by
    intro m
    exact IsUltrametricDist.norm_tsum_le_of_forall_le (fun i => hGbound (m, i))
  have hSsum : Summable (fun m => ∑' i, G (m, i)) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    apply hdom _ 0
    intro n
    exact hSbound n
  have hrow_eq : ∀ m, (∑' i, G (m, i))
      = ∑ i ∈ Finset.range m, b m * (y ^ i * α ^ (m - 1 - i)) := by
    intro m
    rw [tsum_eq_sum (show ∀ b ∉ Finset.range m, G (m, b) = 0 from by
      intro i hi
      rw [hGval]
      exact ite_eq_right (fun h => hi (Finset.mem_range.mpr h)))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hGval, ite_eq_left (Finset.mem_range.mp hi)]
  have hrow_term : ∀ m,
      (∑ i ∈ Finset.range m, b m * (y ^ i * α ^ (m - 1 - i))) * (y - α)
        = b m * (y ^ m - α ^ m) := by
    intro m
    have h := geom_sum₂_mul y α m
    rw [← Finset.mul_sum, mul_assoc, h]
  have hcol_eq : ∀ i, (∑' m, G (m, i))
      = (∑' m, b (m + (i + 1)) * α ^ m) * y ^ i := by
    intro i
    have hshift : (∑' k, G (k + (i + 1), i)) = ∑' m, G (m, i) :=
      Function.Injective.tsum_eq (g := fun k => k + (i + 1))
        (f := fun m => G (m, i)) (fun a c h => Nat.add_right_cancel h) (by
        intro m hm
        rw [Function.mem_support] at hm
        have him : i < m := by
          by_contra hcon
          have h0 : G (m, i) = 0 := by
            rw [hGval]
            exact ite_eq_right hcon
          exact hm h0
        exact Set.mem_range.mpr ⟨m - (i + 1), Nat.sub_add_cancel him⟩)
    have hfac : (∑' k, b (k + (i + 1)) * α ^ k * y ^ i)
        = (∑' k, b (k + (i + 1)) * α ^ k) * y ^ i :=
      Summable.tsum_mul_right _ (hsumk i)
    have hterm : ∀ k, G (k + (i + 1), i)
        = b (k + (i + 1)) * α ^ k * y ^ i := by
      intro k
      have hexp : (k + (i + 1)) - 1 - i = k := by omega
      rw [hGval, ite_eq_left (by omega), hexp]
      ring
    rw [← hshift, tsum_congr hterm]
    exact hfac
  have hRHS : (∑' i, ∑' m, G (m, i))
      = ∑' i, (∑' m, b (m + (i + 1)) * α ^ m) * y ^ i := by
    apply tsum_congr
    intro i
    exact hcol_eq i
  have hLHS : (∑' m, ∑' i, G (m, i)) * (y - α)
      = ∑' m, b m * y ^ m - ∑' m, b m * α ^ m := by
    have h1 : (∑' m, ∑' i, G (m, i)) * (y - α)
        = ∑' m, (∑' i, G (m, i)) * (y - α) :=
      (Summable.tsum_mul_right _ hSsum).symm
    rw [h1]
    have h2 : (fun m => (∑' i, G (m, i)) * (y - α))
        = (fun m => b m * y ^ m - b m * α ^ m) := by
      funext m
      rw [hrow_eq m, hrow_term m, mul_sub]
    rw [h2]
    exact (hsum y hy).tsum_sub (hsum α hα)
  have hswap : (∑' i, ∑' m, G (m, i)) = (∑' m, ∑' i, G (m, i)) :=
    Summable.tsum_comm' hGunc hrow hcol
  refine ⟨?_, ?_, ?_⟩
  · rw [← hLHS, ← hswap, hRHS]
    exact mul_comm _ _
  · intro i C hC
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC (i + 1) (by omega))
    apply IsUltrametricDist.norm_tsum_le_of_forall_le
    intro m
    calc ‖b (m + (i + 1)) * α ^ m‖ = ‖b (m + (i + 1))‖ * ‖α ^ m‖ := norm_mul _ _
      _ ≤ C * 1 := by
          refine mul_le_mul (hC _ (by omega)) (hαpow m) (norm_nonneg _) hC0
      _ = C := by ring
  · rw [Filter.tendsto_def]
    intro s hs
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
    have hbε : ∀ᶠ m in Filter.cofinite, ‖b m‖ < ε / 2 := by
      have hmem : Metric.ball (0 : ℚ_[p]) (ε / 2) ∈ nhds (0 : ℚ_[p]) :=
        Metric.ball_mem_nhds _ (half_pos hε)
      have h2 := hb hmem
      filter_upwards [h2] with m hm
      have hm' : b m ∈ Metric.ball (0 : ℚ_[p]) (ε / 2) := hm
      rw [← dist_zero_right]
      exact Metric.mem_ball.mp hm'
    rw [Nat.cofinite_eq_atTop] at hbε
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hbε
    have hsub : {i | ¬ (∑' m, b (m + (i + 1)) * α ^ m) ∈ s}
        ⊆ ↑(Finset.range N₀) := by
      intro i hi
      have hi' : ¬ (∑' m, b (m + (i + 1)) * α ^ m) ∈ s := hi
      rw [Finset.mem_coe, Finset.mem_range]
      by_contra hcon
      have hle : N₀ ≤ i := not_lt.mp hcon
      have hbound : ‖∑' m, b (m + (i + 1)) * α ^ m‖ ≤ ε / 2 := by
        apply IsUltrametricDist.norm_tsum_le_of_forall_le
        intro m
        calc ‖b (m + (i + 1)) * α ^ m‖ = ‖b (m + (i + 1))‖ * ‖α ^ m‖ :=
              norm_mul _ _
          _ ≤ (ε / 2) * 1 := by
              refine mul_le_mul ?_ (hαpow m) (norm_nonneg _) ?_
              · exact le_of_lt (hN₀ _ (by omega))
              · exact le_of_lt (half_pos hε)
          _ = ε / 2 := by ring
      have hmem : (∑' m, b (m + (i + 1)) * α ^ m) ∈ Metric.ball 0 ε := by
        rw [Metric.mem_ball, dist_zero_right]
        calc ‖∑' m, b (m + (i + 1)) * α ^ m‖ ≤ ε / 2 := hbound
          _ < ε := (half_lt_self_iff).mpr hε
      exact hi' (hball hmem)
    exact Filter.eventually_cofinite.mpr
      (Set.Finite.subset (Finset.finite_toSet _) hsub)

/-- Uniform gap below a strict local maximum of norms. -/
private theorem strassmann_gap (p : ℕ) [Fact p.Prime] (b : ℕ → ℚ_[p]) (N : ℕ)
    (hb : Filter.Tendsto b Filter.cofinite (nhds 0))
    (hlt : ∀ m > N, ‖b m‖ < ‖b N‖) :
    ∃ C, C < ‖b N‖ ∧ ∀ m > N, ‖b m‖ ≤ C := by
  classical
  have hr : 0 < ‖b N‖ :=
    lt_of_le_of_lt (norm_nonneg _) (hlt (N + 1) (Nat.lt_succ_self N))
  have hev : ∀ᶠ m in Filter.cofinite, ‖b m‖ < ‖b N‖ / 2 := by
    have hmem : ∀ᶠ y in nhds (0 : ℚ_[p]), dist y 0 < ‖b N‖ / 2 :=
      Metric.ball_mem_nhds _ (half_pos hr)
    have h2 := hb.eventually hmem
    exact h2.mono fun m hm => by simpa only [dist_zero_right] using hm
  have hSfin : {m | ¬ ‖b m‖ < ‖b N‖ / 2}.Finite :=
    Filter.mem_cofinite.mp hev
  set T : Finset ℕ := hSfin.toFinset.filter (fun m => N < m) with hTdef
  set U : Finset ℝ := (T.image fun m => ‖b m‖) ∪ {‖b N‖ / 2} with hUdef
  have hmem : ‖b N‖ / 2 ∈ U :=
    Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
  refine ⟨U.max' ⟨‖b N‖ / 2, hmem⟩, ?_, ?_⟩
  · have hCmem : U.max' ⟨‖b N‖ / 2, hmem⟩ ∈ U := Finset.max'_mem _ _
    rcases Finset.mem_union.mp hCmem with himg | hsing
    · obtain ⟨m, hmT, hmeq⟩ := Finset.mem_image.mp himg
      rw [← hmeq]
      exact hlt m (Finset.mem_filter.mp hmT |>.2)
    · rw [Finset.mem_singleton.mp hsing]
      exact (half_lt_self_iff).mpr hr
  · intro m hmN
    by_cases hm : ‖b m‖ < ‖b N‖ / 2
    · exact le_trans hm.le (Finset.le_max' U _ hmem)
    · have hmT : m ∈ T := Finset.mem_filter.mpr
        ⟨(Set.Finite.mem_toFinset hSfin).mpr hm, hmN⟩
      have hUmem : ‖b m‖ ∈ U :=
        Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨m, hmT, rfl⟩))
      exact Finset.le_max' U _ hUmem

@[expose] public section

/-- **Strassmann's theorem.** Let $p$ be a prime and let $(b_m)_{m \ge 0}$ be a sequence in
$\mathbb{Q}_p$, not identically zero, with $b_m \to 0$. Then the power series
$\sum_{m \ge 0} b_m y^m$ has only finitely many zeros $y \in \mathbb{Q}_p$ with $|y|_p \le 1$.

Source: R. Strassmann, J. Reine Angew. Math. 159 (1928). -/
public theorem strassmann (p : ℕ) [Fact p.Prime] (b : ℕ → ℚ_[p])
    (hb : Filter.Tendsto b Filter.cofinite (nhds 0)) (hne : b ≠ 0) :
    {y : ℚ_[p] | ‖y‖ ≤ 1 ∧ ∑' m, b m * y ^ m = 0}.Finite := by
  classical
  have key : ∀ N (c : ℕ → ℚ_[p]),
      Filter.Tendsto c Filter.cofinite (nhds 0) → c N ≠ 0 →
      (∀ m, ‖c m‖ ≤ ‖c N‖) → (∀ m > N, ‖c m‖ < ‖c N‖) →
      {y : ℚ_[p] | ‖y‖ ≤ 1 ∧ ∑' m, c m * y ^ m = 0}.Finite := by
    intro N
    induction N with
    | zero =>
      intro c hc hc0 hle hlt
      obtain ⟨C, hClt, hCbound⟩ := strassmann_gap p c 0 hc hlt
      have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hCbound 1 one_pos)
      have hno : ∀ y : ℚ_[p], ‖y‖ ≤ 1 → ∑' m, c m * y ^ m ≠ 0 := by
        intro y hy
        obtain ⟨hfac, hcb, -⟩ := strassmann_factor p c hc 0 y
          (by rw [norm_zero]; exact zero_le_one) hy
        have h0sum : (∑' m, c m * (0 : ℚ_[p]) ^ m) = c 0 := by
          have hsupp : ∀ m ∉ ({0} : Finset ℕ), c m * (0 : ℚ_[p]) ^ m = 0 := by
            intro m hm
            rw [Finset.mem_singleton] at hm
            rw [zero_pow hm, mul_zero]
          rw [tsum_eq_sum hsupp, Finset.sum_singleton, pow_zero, mul_one]
        have hTbound :
            ‖∑' i, (∑' m, c (m + (i + 1)) * (0 : ℚ_[p]) ^ m) * y ^ i‖ ≤ C := by
          apply IsUltrametricDist.norm_tsum_le_of_forall_le
          intro i
          have hci : ‖∑' m, c (m + (i + 1)) * (0 : ℚ_[p]) ^ m‖ ≤ C :=
            hcb i C (fun m _ => hCbound m (by omega))
          have hyi : ‖y ^ i‖ ≤ 1 := by
            rw [norm_pow]
            exact pow_le_one₀ (norm_nonneg _) hy
          calc ‖(∑' m, c (m + (i + 1)) * (0 : ℚ_[p]) ^ m) * y ^ i‖
              = ‖∑' m, c (m + (i + 1)) * (0 : ℚ_[p]) ^ m‖ * ‖y ^ i‖ :=
                norm_mul _ _
            _ ≤ C * 1 := mul_le_mul hci hyi (norm_nonneg _) hC0
            _ = C := by ring
        rw [h0sum] at hfac
        have htail :
            ‖(y - 0) * (∑' i, (∑' m, c (m + (i + 1)) * (0 : ℚ_[p]) ^ m) * y ^ i)‖
              < ‖c 0‖ := by
          calc ‖(y - 0) * (∑' i, (∑' m, c (m + (i + 1)) * (0 : ℚ_[p]) ^ m) * y ^ i)‖
              = ‖y - 0‖ * ‖∑' i, (∑' m, c (m + (i + 1)) * (0 : ℚ_[p]) ^ m) * y ^ i‖ :=
                norm_mul _ _
            _ ≤ 1 * C := by
                refine mul_le_mul ?_ hTbound (norm_nonneg _) zero_le_one
                rw [sub_zero]
                exact hy
            _ = C := by ring
            _ < ‖c 0‖ := hClt
        have hA : (∑' m, c m * y ^ m)
            = c 0 + (y - 0) * (∑' i, (∑' m, c (m + (i + 1)) * (0 : ℚ_[p]) ^ m) * y ^ i) := by
          linear_combination hfac
        rw [hA]
        intro hcon
        have h1 : ‖c 0 + (y - 0) * (∑' i, (∑' m, c (m + (i + 1)) * (0 : ℚ_[p]) ^ m) * y ^ i)‖
            = 0 := by rw [hcon, norm_zero]
        have hne : ‖c 0‖
            ≠ ‖(y - 0) * (∑' i, (∑' m, c (m + (i + 1)) * (0 : ℚ_[p]) ^ m) * y ^ i)‖ :=
          (ne_of_lt htail).symm
        rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne,
          max_eq_left (le_of_lt htail)] at h1
        exact norm_ne_zero_iff.mpr hc0 h1
      exact Set.Finite.subset Set.finite_empty (fun y hy => by
        have hy' : ‖y‖ ≤ 1 ∧ ∑' m, c m * y ^ m = 0 := hy
        exact absurd hy'.2 (hno y hy'.1))
    | succ N ih =>
      intro c hc hcSN hle hlt
      by_cases hzero : ∃ y : ℚ_[p], ‖y‖ ≤ 1 ∧ ∑' m, c m * y ^ m = 0
      · obtain ⟨α₀, hα₀, hα₀z⟩ := hzero
        obtain ⟨-, hcb, hclim⟩ := strassmann_factor p c hc α₀ α₀ hα₀ hα₀
        obtain ⟨C, hClt, hCbound⟩ := strassmann_gap p c (N + 1) hc hlt
        have hC0 : 0 ≤ C :=
          le_trans (norm_nonneg _) (hCbound (N + 2) (by omega))
        have hc_le : ∀ i, ‖∑' m, c (m + (i + 1)) * α₀ ^ m‖ ≤ ‖c (N + 1)‖ :=
          fun i => hcb i _ (fun m _ => hle m)
        have hc_lt : ∀ i > N, ‖∑' m, c (m + (i + 1)) * α₀ ^ m‖ ≤ C := by
          intro i hi
          apply hcb i C
          intro m hm
          exact hCbound m (by omega)
        have hcN : ‖∑' m, c (m + (N + 1)) * α₀ ^ m‖ = ‖c (N + 1)‖ := by
          set e : ℕ → ℚ_[p] := fun m => if m = 0 then c (N + 1) else 0
          have he0 : ∀ m, e m = if m = 0 then c (N + 1) else 0 := fun m => rfl
          have hesum : (∑' m, e m) = c (N + 1) := by
            have hsupp : ∀ m ∉ ({0} : Finset ℕ), e m = 0 := by
              intro m hm
              rw [he0]
              rw [Finset.mem_singleton] at hm
              exact ite_eq_right hm
            rw [tsum_eq_sum hsupp, Finset.sum_singleton]
            rw [he0, ite_eq_left rfl]
          have hFsum : Summable (fun m => c (m + (N + 1)) * α₀ ^ m) := by
            apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
            rw [Filter.tendsto_def]
            intro s hs
            obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
            have hcε : ∀ᶠ m in Filter.cofinite, dist (c m) 0 < ε := by
              have hmem : Metric.ball (0 : ℚ_[p]) ε ∈ nhds (0 : ℚ_[p]) :=
                Metric.ball_mem_nhds _ hε
              have h2 := hc hmem
              filter_upwards [h2] with m hm
              have hm' : c m ∈ Metric.ball (0 : ℚ_[p]) ε := hm
              exact Metric.mem_ball.mp hm'
            have hfin : {m | ¬ dist (c m) 0 < ε}.Finite :=
              Filter.eventually_cofinite.mp hcε
            have hinj : Function.Injective (fun n => n + (N + 1)) := fun a c_ h =>
              Nat.add_right_cancel h
            have hpre : ((fun n => n + (N + 1)) ⁻¹' {m | ¬ dist (c m) 0 < ε}).Finite :=
              Set.Finite.preimage (Set.injOn_of_injective hinj) hfin
            have hsub : {n | ¬ (c (n + (N + 1)) * α₀ ^ n) ∈ s}
                ⊆ (fun n => n + (N + 1)) ⁻¹' {m | ¬ dist (c m) 0 < ε} := by
              intro n hn
              have hn' : ¬ (c (n + (N + 1)) * α₀ ^ n) ∈ s := hn
              intro hcon
              apply hn'
              apply hball
              rw [Metric.mem_ball]
              have hα₀pow : ‖α₀ ^ n‖ ≤ 1 := by
                rw [norm_pow]
                exact pow_le_one₀ (norm_nonneg _) hα₀
              calc dist (c (n + (N + 1)) * α₀ ^ n) 0
                  = ‖c (n + (N + 1))‖ * ‖α₀ ^ n‖ := by
                    rw [dist_zero_right, norm_mul]
                _ ≤ dist (c (n + (N + 1))) 0 * 1 := by
                    rw [dist_zero_right]
                    exact mul_le_mul_of_nonneg_left hα₀pow (norm_nonneg _)
                _ = dist (c (n + (N + 1))) 0 := by ring
                _ < ε := hcon
            exact Filter.eventually_cofinite.mpr (Set.Finite.subset hpre hsub)
          have he_sum : Summable e := by
            apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
            rw [Filter.tendsto_def]
            intro s hs
            obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
            have hsub : {n | ¬ e n ∈ s} ⊆ ↑(({0} : Finset ℕ)) := by
              intro n hn
              have hn' : ¬ e n ∈ s := hn
              rw [Finset.mem_coe, Finset.mem_singleton]
              by_contra hcon
              have hm0 : n ≠ 0 := by simpa using hcon
              have he0' : e n = 0 := by
                rw [he0]
                exact ite_eq_right hm0
              apply hn'
              apply hball
              rw [Metric.mem_ball, he0', dist_self]
              exact hε
            exact Filter.eventually_cofinite.mpr
              (Set.Finite.subset (Finset.finite_toSet _) hsub)
          have hR : (∑' m, c (m + (N + 1)) * α₀ ^ m) - c (N + 1)
              = ∑' m, (c (m + (N + 1)) * α₀ ^ m - e m) := by
            rw [← hesum]
            exact (hFsum.tsum_sub he_sum).symm
          have hRbound : ‖∑' m, (c (m + (N + 1)) * α₀ ^ m - e m)‖ ≤ C := by
            apply IsUltrametricDist.norm_tsum_le_of_forall_le
            intro m
            by_cases hm : m = 0
            · subst hm
              have hthis : c (0 + (N + 1)) * α₀ ^ 0 - e 0 = 0 := by
                rw [he0]
                simp
              rw [hthis, norm_zero]
              exact hC0
            · have hem : e m = 0 := by
                rw [he0]
                exact ite_eq_right hm
              have hterm : c (m + (N + 1)) * α₀ ^ m - e m
                  = c (m + (N + 1)) * α₀ ^ m := by
                rw [hem, sub_zero]
              rw [hterm]
              have hα₀pow : ‖α₀ ^ m‖ ≤ 1 := by
                rw [norm_pow]
                exact pow_le_one₀ (norm_nonneg _) hα₀
              calc ‖c (m + (N + 1)) * α₀ ^ m‖
                  = ‖c (m + (N + 1))‖ * ‖α₀ ^ m‖ := norm_mul _ _
                _ ≤ C * 1 := by
                    refine mul_le_mul ?_ hα₀pow (norm_nonneg _) hC0
                    exact hCbound _ (by omega)
                _ = C := by ring
          have hdecomp : (∑' m, c (m + (N + 1)) * α₀ ^ m)
              = c (N + 1) + ∑' m, (c (m + (N + 1)) * α₀ ^ m - e m) := by
            linear_combination hR
          have hneC : ‖c (N + 1)‖
              ≠ ‖∑' m, (c (m + (N + 1)) * α₀ ^ m - e m)‖ :=
            (ne_of_lt (lt_of_le_of_lt hRbound hClt)).symm
          rw [hdecomp,
            IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hneC,
            max_eq_left (le_of_lt (lt_of_le_of_lt hRbound hClt))]
        have hcNne : (∑' m, c (m + (N + 1)) * α₀ ^ m) ≠ 0 := by
          have hposN : 0 < ‖c (N + 1)‖ := norm_pos_iff.mpr hcSN
          intro h0
          rw [h0, norm_zero] at hcN
          linarith
        have hIH := ih (fun i => ∑' m, c (m + (i + 1)) * α₀ ^ m) hclim hcNne
          (fun i => by rw [hcN]; exact hc_le i)
          (fun i hi => by rw [hcN]; exact lt_of_le_of_lt (hc_lt i hi) hClt)
        apply Set.Finite.subset (Set.Finite.insert α₀ hIH)
        intro y hy
        have hy' : ‖y‖ ≤ 1 ∧ ∑' m, c m * y ^ m = 0 := hy
        obtain ⟨hyy, hyz⟩ := hy'
        by_cases heq : y = α₀
        · subst heq
          exact Set.mem_insert_iff.mpr (Or.inl rfl)
        · have hfac_y := (strassmann_factor p c hc α₀ y hα₀ hyy).1
          rw [hyz, hα₀z] at hfac_y
          have hT0 : (∑' i, (∑' m, c (m + (i + 1)) * α₀ ^ m) * y ^ i) = 0 := by
            have hne' : y - α₀ ≠ 0 := sub_ne_zero.mpr heq
            simp only [sub_self] at hfac_y
            rcases mul_eq_zero.mp hfac_y.symm with h | h
            · exact absurd h hne'
            · exact h
          exact Set.mem_insert_iff.mpr (Or.inr ⟨hyy, hT0⟩)
      · apply Set.Finite.subset Set.finite_empty
        intro y hy
        have hy' : ‖y‖ ≤ 1 ∧ ∑' m, c m * y ^ m = 0 := hy
        obtain ⟨hyy, hyz⟩ := hy'
        have hcon : ∃ y : ℚ_[p], ‖y‖ ≤ 1 ∧ ∑' m, c m * y ^ m = 0 :=
          ⟨y, hyy, hyz⟩
        exact absurd hcon hzero
  obtain ⟨m₀, hm₀⟩ := Function.ne_iff.mp hne
  have hm₀' : b m₀ ≠ 0 := hm₀
  have hpos : 0 < ‖b m₀‖ := norm_pos_iff.mpr hm₀'
  have hTfin : {m | ‖b m₀‖ ≤ ‖b m‖}.Finite := by
    have hbε : ∀ᶠ m in Filter.cofinite, dist (b m) 0 < ‖b m₀‖ := by
      have hmem : Metric.ball (0 : ℚ_[p]) ‖b m₀‖ ∈ nhds (0 : ℚ_[p]) :=
        Metric.ball_mem_nhds _ hpos
      have h2 := hb hmem
      filter_upwards [h2] with m hm
      have hm' : b m ∈ Metric.ball (0 : ℚ_[p]) ‖b m₀‖ := hm
      exact Metric.mem_ball.mp hm'
    have hfin : {m | ¬ dist (b m) 0 < ‖b m₀‖}.Finite :=
      Filter.eventually_cofinite.mp hbε
    apply Set.Finite.subset hfin
    intro m hm
    rw [Set.mem_ofPred_eq, dist_zero_right]
    exact not_lt.mpr hm
  have hm₀T : m₀ ∈ hTfin.toFinset := by
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  obtain ⟨M, hMT, hMmax⟩ := Finset.exists_max_image
    hTfin.toFinset (fun m => ‖b m‖) ⟨m₀, hm₀T⟩
  have hglob : ∀ m, ‖b m‖ ≤ ‖b M‖ := by
    intro m
    by_cases hm : m ∈ hTfin.toFinset
    · exact hMmax m hm
    · have hmlt : ‖b m‖ < ‖b m₀‖ := by
        have hnge : ¬ ‖b m₀‖ ≤ ‖b m‖ := by
          intro hle
          exact hm (by rw [Set.Finite.mem_toFinset]; exact hle)
        exact lt_of_not_ge hnge
      exact le_trans hmlt.le (hMmax m₀ hm₀T)
  have hT'ne : ((hTfin.toFinset).filter (fun m => ‖b m‖ = ‖b M‖)).Nonempty :=
    ⟨M, Finset.mem_filter.mpr ⟨hMT, rfl⟩⟩
  set N := ((hTfin.toFinset).filter (fun m => ‖b m‖ = ‖b M‖)).max' hT'ne
  have hNmem : N ∈ (hTfin.toFinset).filter (fun m => ‖b m‖ = ‖b M‖) :=
    Finset.max'_mem _ _
  have hNbN : ‖b N‖ = ‖b M‖ := (Finset.mem_filter.mp hNmem).2
  have hNe : b N ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hNbN
    have hM0 : ‖b m₀‖ ≤ ‖b M‖ := hMmax m₀ hm₀T
    linarith
  have hNmax : ∀ m > N, ‖b m‖ < ‖b N‖ := by
    intro m hmN
    by_contra hcon
    have hge : ‖b N‖ ≤ ‖b m‖ := le_of_not_gt hcon
    have hgeM : ‖b M‖ ≤ ‖b m‖ := by
      rw [← hNbN]
      exact hge
    have heqM : ‖b m‖ = ‖b M‖ := le_antisymm (hglob m) hgeM
    have hle0 : ‖b m₀‖ ≤ ‖b m‖ := le_trans (hMmax m₀ hm₀T) heqM.symm.le
    have hmT : m ∈ hTfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact hle0
    have hmfilt : m ∈ (hTfin.toFinset).filter (fun m => ‖b m‖ = ‖b M‖) :=
      Finset.mem_filter.mpr ⟨hmT, heqM⟩
    have hleN : m ≤ N := Finset.le_max' _ _ hmfilt
    omega
  exact key N b hb hNe (fun m => by rw [hNbN]; exact hglob m) hNmax

end

end Padic
