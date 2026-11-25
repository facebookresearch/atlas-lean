/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Order.Lattice

namespace MetaMathlibExt

@[expose] public section

/-- A convergent complex sequence is bounded in norm. -/
private theorem aux_bounded_of_tendsto (x : ℕ → ℂ) (L : ℂ)
    (hx : Filter.Tendsto x Filter.atTop (nhds L)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k, ‖x k‖ ≤ B := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hx) 1 one_pos
  refine ⟨(∑ k ∈ Finset.range N, ‖x k‖) + ‖L‖ + 1, ?_, fun k => ?_⟩
  · exact add_nonneg
      (add_nonneg (Finset.sum_nonneg (fun k _ => norm_nonneg _))
        (norm_nonneg _)) (zero_le_one : (0 : ℝ) ≤ 1)
  · by_cases hk : k < N
    · calc ‖x k‖ ≤ ∑ k ∈ Finset.range N, ‖x k‖ :=
            Finset.single_le_sum (fun i _ => norm_nonneg _)
              (Finset.mem_range.mpr hk)
        _ ≤ (∑ k ∈ Finset.range N, ‖x k‖) + ‖L‖ + 1 := by
            linarith [norm_nonneg L, (zero_le_one : (0 : ℝ) ≤ 1)]
    · have h := hN k (Nat.le_of_not_lt hk)
      rw [dist_eq_norm] at h
      calc ‖x k‖ = ‖(x k - L) + L‖ := by rw [sub_add_cancel]
        _ ≤ ‖x k - L‖ + ‖L‖ := norm_add_le _ _
        _ ≤ 1 + ‖L‖ := by linarith [h]
        _ ≤ (∑ k ∈ Finset.range N, ‖x k‖) + ‖L‖ + 1 := by
            have hsum : (0 : ℝ) ≤ ∑ k ∈ Finset.range N, ‖x k‖ :=
              Finset.sum_nonneg (fun k _ => norm_nonneg _)
            linarith [hsum]

/-- The transformed null sequence tends to zero. -/
private theorem aux_tsum_tendsto_zero (A : ℕ → ℕ → ℂ) (M : ℝ)
    (hM : 0 ≤ M)
    (hrow : ∀ n, Summable (fun k => ‖A n k‖))
    (hle : ∀ n, ∑' k, ‖A n k‖ ≤ M)
    (h_col : ∀ k, Filter.Tendsto (fun n => A n k) Filter.atTop (nhds 0))
    (y : ℕ → ℂ) (hy : Filter.Tendsto y Filter.atTop (nhds 0))
    (hsy : ∀ n, Summable (fun k => A n k * y k)) :
    Filter.Tendsto (fun n => ∑' k, A n k * y k) Filter.atTop (nhds 0) := by
  obtain ⟨By, _, hBy⟩ := aux_bounded_of_tendsto y 0 hy
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  have hM1' : M + 1 ≠ 0 := ne_of_gt hM1
  set τ : ℝ := ε / (2 * (M + 1)) with hτdef
  have hτpos : 0 < τ := by
    rw [hτdef]
    exact div_pos hε (by linarith)
  obtain ⟨K₀, hK₀⟩ := Metric.tendsto_atTop.mp hy τ hτpos
  have hterm : ∀ k, Filter.Tendsto (fun n => A n k * y k) Filter.atTop
      (nhds 0) := by
    intro k
    have hc : Filter.Tendsto (fun _ : ℕ => y k) Filter.atTop (nhds (y k)) :=
      tendsto_const_nhds
    have h := (h_col k).mul hc
    simpa using h
  have hhead_lim : Filter.Tendsto (fun n => ∑ k ∈ Finset.range K₀, A n k * y k)
      Filter.atTop (nhds 0) := by
    have h := tendsto_finsetSum (Finset.range K₀) (fun k _ => hterm k)
    simpa using h
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hhead_lim (ε / 2) (by linarith)
  refine ⟨N₁, fun n hn => ?_⟩
  have hn1 : ‖∑ k ∈ Finset.range K₀, A n k * y k‖ < ε / 2 := by
    have h := hN₁ n hn
    simpa [dist_eq_norm] using h
  have hsplit : (∑ x ∈ Finset.range K₀, A n x * y x) +
      (∑' x : {x : ℕ // x ∉ (↑(Finset.range K₀) : Set ℕ)},
        A n x.val * y x.val) =
      ∑' x, A n x * y x :=
    Summable.sum_add_tsum_compl (s := Finset.range K₀) (hsy n)
  have hsubN : Summable
      (fun x : {x : ℕ // x ∉ (↑(Finset.range K₀) : Set ℕ)} =>
        ‖A n x.val * y x.val‖) := by
    apply Summable.of_norm_bounded
      (((hrow n).subtype (fun k => k ∉ (↑(Finset.range K₀) : Set ℕ))).mul_left
        By)
    intro x
    rw [norm_norm]
    calc ‖A n x.val * y x.val‖ = ‖A n x.val‖ * ‖y x.val‖ := norm_mul _ _
      _ ≤ ‖A n x.val‖ * By :=
          mul_le_mul_of_nonneg_left (hBy _) (norm_nonneg _)
      _ = By * ‖A n x.val‖ := mul_comm _ _
  have hsubN' : Summable
      (fun x : {x : ℕ // x ∉ (↑(Finset.range K₀) : Set ℕ)} => ‖A n x.val‖) :=
    (hrow n).subtype (fun k => k ∉ (↑(Finset.range K₀) : Set ℕ))
  have hynorm : ∀ x : {x : ℕ // x ∉ (↑(Finset.range K₀) : Set ℕ)},
      ‖y x.val‖ ≤ τ := by
    intro x
    have hxK : K₀ ≤ x.val := by
      by_contra hcon
      have hlt : x.val < K₀ := lt_of_not_ge hcon
      apply x.property
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr hlt)
    have hdist := hK₀ x.val hxK
    rw [dist_eq_norm, sub_zero] at hdist
    exact le_of_lt hdist
  have htail_bound : ‖∑' x : {x : ℕ // x ∉ (↑(Finset.range K₀) : Set ℕ)},
      A n x.val * y x.val‖ ≤ ε / 2 := by
    have hg : Summable
        (fun x : {x : ℕ // x ∉ (↑(Finset.range K₀) : Set ℕ)} =>
          τ * ‖A n x.val‖) :=
      hsubN'.mul_left τ
    have hle1 :
        (∑' x : {x : ℕ // x ∉ (↑(Finset.range K₀) : Set ℕ)},
          ‖A n x.val * y x.val‖) ≤
        ∑' x : {x : ℕ // x ∉ (↑(Finset.range K₀) : Set ℕ)},
          τ * ‖A n x.val‖ := by
      refine Summable.tsum_le_tsum ?_ hsubN hg
      intro x
      calc ‖A n x.val * y x.val‖ = ‖A n x.val‖ * ‖y x.val‖ := norm_mul _ _
        _ ≤ ‖A n x.val‖ * τ :=
            mul_le_mul_of_nonneg_left (hynorm x) (norm_nonneg _)
        _ = τ * ‖A n x.val‖ := mul_comm _ _
    have hsplitN : (∑ x ∈ Finset.range K₀, ‖A n x‖) +
        (∑' x : {x : ℕ // x ∉ (↑(Finset.range K₀) : Set ℕ)}, ‖A n x.val‖) =
        ∑' k, ‖A n k‖ :=
      Summable.sum_add_tsum_compl (s := Finset.range K₀) (hrow n)
    have hhead_nn : 0 ≤ ∑ x ∈ Finset.range K₀, ‖A n x‖ :=
      Finset.sum_nonneg (fun k _ => norm_nonneg _)
    have hsub_le :
        (∑' x : {x : ℕ // x ∉ (↑(Finset.range K₀) : Set ℕ)}, ‖A n x.val‖) ≤
        ∑' k, ‖A n k‖ := by
      linarith [hsplitN, hhead_nn]
    have hfinal : τ * (∑' k, ‖A n k‖) ≤ ε / 2 := by
      have h1 : τ * (∑' k, ‖A n k‖) ≤ τ * M :=
        mul_le_mul_of_nonneg_left (hle n) (le_of_lt hτpos)
      have h2 : τ * M = ε / 2 * (M / (M + 1)) := by
        rw [hτdef]
        field_simp
      have hMle : M / (M + 1) ≤ 1 := by
        rw [div_le_one hM1]
        linarith
      have h3 : ε / 2 * (M / (M + 1)) ≤ ε / 2 :=
        mul_le_of_le_one_right (by linarith) hMle
      linarith [h1, h2, h3]
    calc ‖∑' x : {x : ℕ // x ∉ (↑(Finset.range K₀) : Set ℕ)},
          A n x.val * y x.val‖
        ≤ ∑' x : {x : ℕ // x ∉ (↑(Finset.range K₀) : Set ℕ)},
            ‖A n x.val * y x.val‖ :=
          norm_tsum_le_tsum_norm hsubN
      _ ≤ ∑' x : {x : ℕ // x ∉ (↑(Finset.range K₀) : Set ℕ)},
            τ * ‖A n x.val‖ := hle1
      _ = τ * (∑' x : {x : ℕ // x ∉ (↑(Finset.range K₀) : Set ℕ)},
            ‖A n x.val‖) :=
          Summable.tsum_mul_left τ hsubN'
      _ ≤ τ * (∑' k, ‖A n k‖) :=
          mul_le_mul_of_nonneg_left hsub_le (le_of_lt hτpos)
      _ ≤ ε / 2 := hfinal
  change dist (∑' k, A n k * y k) 0 < ε
  rw [dist_eq_norm, sub_zero, ← hsplit]
  calc ‖(∑ x ∈ Finset.range K₀, A n x * y x) +
        (∑' x : {x : ℕ // x ∉ (↑(Finset.range K₀) : Set ℕ)},
          A n x.val * y x.val)‖
      ≤ ‖∑ x ∈ Finset.range K₀, A n x * y x‖ +
          ‖∑' x : {x : ℕ // x ∉ (↑(Finset.range K₀) : Set ℕ)},
            A n x.val * y x.val‖ :=
        norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hn1 htail_bound
    _ = ε := by ring

/-- **Silverman–Toeplitz theorem (sufficiency).** Let $(a_{nk})_{n, k \ge 0}$ be an infinite
matrix of complex numbers. Suppose that there is a real $C$ such that for every $n$ the series
$\sum_k |a_{nk}|$ converges with sum at most $C$, that $a_{nk} \to 0$ as $n \to \infty$ for every
$k$, and that $\sum_k a_{nk} \to 1$ as $n \to \infty$. Then for every sequence $(x_k)$ of complex
numbers converging to $L$, the series $\sum_k a_{nk} x_k$ converges absolutely for every $n$, and
$\sum_k a_{nk} x_k \to L$ as $n \to \infty$.

Source: https://en.wikipedia.org/wiki/Silverman%E2%80%93Toeplitz_theorem
(statement silverman-toeplitz-s1).
Proves `Wanted` entry `silverman_toeplitz`.
-/
theorem silverman_toeplitz (A : ℕ → ℕ → ℂ)
    (h_bdd : ∃ C : ℝ, ∀ n, Summable (fun k => ‖A n k‖) ∧
      ∑' k, ‖A n k‖ ≤ C)
    (h_col : ∀ k, Filter.Tendsto (fun n => A n k) Filter.atTop (nhds 0))
    (h_sum : Filter.Tendsto (fun n => ∑' k, A n k) Filter.atTop (nhds 1)) :
    ∀ (x : ℕ → ℂ) (L : ℂ), Filter.Tendsto x Filter.atTop (nhds L) →
      (∀ n, Summable (fun k => A n k * x k)) ∧
        Filter.Tendsto (fun n => ∑' k, A n k * x k) Filter.atTop (nhds L) := by
  obtain ⟨C, hC⟩ := h_bdd
  have hMnn : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hle : ∀ n, ∑' k, ‖A n k‖ ≤ max C 0 :=
    fun n => le_trans (hC n).2 (le_max_left _ _)
  have hrow : ∀ n, Summable (fun k => ‖A n k‖) := fun n => (hC n).1
  have hAsum : ∀ n, Summable (fun k => A n k) := fun n => (hrow n).of_norm
  intro x L hx
  obtain ⟨B, _, hB⟩ := aux_bounded_of_tendsto x L hx
  have hpart1 : ∀ n, Summable (fun k => A n k * x k) := by
    intro n
    apply Summable.of_norm_bounded ((hrow n).mul_left B)
    intro k
    calc ‖A n k * x k‖ = ‖A n k‖ * ‖x k‖ := norm_mul _ _
      _ ≤ ‖A n k‖ * B := mul_le_mul_of_nonneg_left (hB k) (norm_nonneg _)
      _ = B * ‖A n k‖ := mul_comm _ _
  refine ⟨hpart1, ?_⟩
  have hAL : ∀ n, Summable (fun k => A n k * L) :=
    fun n => (hAsum n).mul_right L
  have hAy : ∀ n, Summable (fun k => A n k * (x k - L)) := by
    intro n
    have h := (hpart1 n).sub (hAL n)
    have hpw : (fun k => A n k * (x k - L)) =
        (fun k => A n k * x k - A n k * L) := by
      funext k
      rw [mul_sub]
    rw [hpw]
    exact h
  have hx0 : Filter.Tendsto (fun k => x k - L) Filter.atTop (nhds 0) := by
    have hc : Filter.Tendsto (fun _ : ℕ => L) Filter.atTop (nhds L) :=
      tendsto_const_nhds
    have h := hx.sub hc
    simpa using h
  have hT : Filter.Tendsto (fun n => ∑' k, A n k * (x k - L)) Filter.atTop
      (nhds 0) :=
    aux_tsum_tendsto_zero A (max C 0) hMnn hrow hle h_col _ hx0 hAy
  have hcL : Filter.Tendsto (fun _ : ℕ => L) Filter.atTop (nhds L) :=
    tendsto_const_nhds
  have hR : Filter.Tendsto (fun n => (∑' k, A n k) * L) Filter.atTop
      (nhds (1 * L)) :=
    h_sum.mul hcL
  have hsum_eq : ∀ n, (∑' k, A n k * x k) =
      (∑' k, A n k * (x k - L)) + (∑' k, A n k) * L := by
    intro n
    have h1 := Summable.tsum_add (hAy n) (hAL n)
    have h2 := (hAsum n).tsum_mul_right L
    have hpw : (fun k => A n k * x k) =
        (fun k => (A n k * (x k - L)) + (A n k * L)) := by
      funext k
      rw [mul_sub, sub_add_cancel]
    rw [hpw, h1, h2]
  have hlim : Filter.Tendsto
      (fun n => (∑' k, A n k * (x k - L)) + (∑' k, A n k) * L) Filter.atTop
      (nhds (0 + 1 * L)) :=
    hT.add hR
  rw [zero_add, one_mul] at hlim
  exact Filter.Tendsto.congr (fun n => (hsum_eq n).symm) hlim

end

end MetaMathlibExt
