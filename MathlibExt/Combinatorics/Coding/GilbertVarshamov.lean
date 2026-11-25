/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.HammingBall
public import MathlibExt.InformationTheory.HammingBallVolume
import Lean.Elab.Tactic.Omega

/-!
# The Gilbert–Varshamov bound (greedy form)

Gilbert's greedy construction: keep adding words at distance at least `d` from every word
already chosen. When no word can be added, the Hamming balls of radius `d - 1` around the chosen
words cover the whole space, so the code has at least `q ^ n / Vol_q(n, d - 1)` words.

* `biUnion_ball_eq_univ_of_maximal`: a code to which no word can be added is covered by the
  radius-`(d - 1)` balls around its codewords.
* `exists_code_pow_le_card_mul_sum` (**Gilbert–Varshamov bound**): for every `n` and every
  `d ≥ 1` there is a code of length `n` and minimum distance at least `d` with
  `q ^ n ≤ |C| · ∑_{i < d} C(n, i) (q - 1) ^ i`.
* `exists_code_exp_le_card` (**Gilbert–Varshamov bound, rate form**): for `q ≥ 2`,
  `0 ≤ δ ≤ 1 - 1/q` and `1 ≤ d ≤ δ n + 1` there is such a code with
  `|C| ≥ q ^ {(1 - H_q(δ)) n}`, combining the counting form with the entropy bound on the volume
  of a Hamming ball.

## References

* E. N. Gilbert, "A comparison of signalling alphabets", *Bell System Technical Journal* 31
  (1952), 504–522.
* V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025,
  Theorem 4.2.1 and its proof in Section 4.2.1 (Algorithm 4.2.1 and equation (4.2)).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Coding.GilbertVarshamov

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- **A maximal code is covering.** Let `C` be a code of length `n` to which no word can be
added without violating minimum distance `d`: every word at distance at least `d` from all
codewords already lies in `C`. Then the Hamming balls of radius `d - 1` around the codewords
cover all words of length `n` (Guruswami, Rudra and Sudan, *Essential Coding Theory*, draft of
August 26, 2025, equation (4.2) in the proof of Theorem 4.2.1). -/
theorem biUnion_ball_eq_univ_of_maximal (C : Finset (Fin n → α)) {d : ℕ}
    (hmax : ∀ v, (∀ c ∈ C, d ≤ hammingDist c v) → v ∈ C) :
    C.biUnion (fun c => Hamming.ball c (d - 1)) = univ := by
  refine eq_univ_of_forall fun v => ?_
  rw [mem_biUnion]
  by_contra h
  push Not at h
  have hfar : ∀ c ∈ C, d ≤ hammingDist c v := by
    intro c hc
    have := h c hc
    rw [Hamming.mem_ball] at this
    omega
  exact h v (hmax v hfar) (by rw [Hamming.mem_ball, hammingDist_self]; exact Nat.zero_le _)

/-- **Gilbert–Varshamov bound.** Let `α` be a finite alphabet with `q` letters and let
`n ≥ 0`, `d ≥ 1`. There is a code `C` of words of length `n` over `α`, with any two distinct
codewords at Hamming distance at least `d`, such that
`q ^ n ≤ |C| · ∑_{i=0}^{d-1} C(n, i) (q - 1) ^ i`, that is, `|C| · Vol_q(n, d - 1) ≥ q ^ n`.

This is the counting inequality behind Theorem 4.2.1 of Guruswami, Rudra and Sudan, *Essential
Coding Theory* (draft of August 26, 2025), obtained there from Gilbert's greedy construction
(Algorithm 4.2.1, Section 4.2.1); the rate form `R ≥ 1 - H_q(δ)` follows from it with the volume
estimate `Vol_q(n, δn) ≤ q ^ {H_q(δ) n}` (`exists_code_exp_le_card`). The proof takes a code of
maximum size, which is maximal (`biUnion_ball_eq_univ_of_maximal`). Source:
E. N. Gilbert, "A comparison of signalling alphabets", *Bell System Technical Journal* 31 (1952),
504–522. -/
theorem exists_code_pow_le_card_mul_sum (n : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : Finset (Fin n → α),
      (∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂) ∧
      Fintype.card α ^ n ≤
        C.card * ∑ i ∈ range d, n.choose i * (Fintype.card α - 1) ^ i := by
  classical
  -- Codes of minimum distance at least `d`.
  set good : Finset (Finset (Fin n → α)) :=
    univ.filter fun C => ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂ with hgood
  have hne : good.Nonempty := ⟨∅, by simp [hgood]⟩
  obtain ⟨C, hC, hCmax⟩ := exists_max_image good card hne
  have hCdist : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂ := by
    simpa [hgood] using hC
  refine ⟨C, hCdist, ?_⟩
  -- A code of maximum size is maximal.
  have hmax : ∀ v, (∀ c ∈ C, d ≤ hammingDist c v) → v ∈ C := by
    intro v hv
    by_contra hvC
    have hins : insert v C ∈ good := by
      simp only [hgood, mem_filter, mem_univ, true_and, mem_insert]
      rintro c₁ (rfl | h₁) c₂ (rfl | h₂) hne
      · exact absurd rfl hne
      · rw [hammingDist_comm]; exact hv c₂ h₂
      · exact hv c₁ h₁
      · exact hCdist c₁ h₁ c₂ h₂ hne
    have := hCmax _ hins
    rw [card_insert_of_notMem hvC] at this
    omega
  have hcover := biUnion_ball_eq_univ_of_maximal C hmax
  have hvol : ∀ c ∈ C, (Hamming.ball c (d - 1)).card =
      ∑ i ∈ range d, n.choose i * (Fintype.card α - 1) ^ i := by
    intro c _
    rw [Hamming.card_ball, Fintype.card_fin, Nat.sub_add_cancel hd]
  calc Fintype.card α ^ n = (univ : Finset (Fin n → α)).card := by
        rw [card_univ, Fintype.card_fun, Fintype.card_fin]
    _ = (C.biUnion fun c => Hamming.ball c (d - 1)).card := by rw [hcover]
    _ ≤ ∑ c ∈ C, (Hamming.ball c (d - 1)).card := card_biUnion_le
    _ = C.card * ∑ i ∈ range d, n.choose i * (Fintype.card α - 1) ^ i := by
        rw [sum_congr rfl hvol, sum_const, smul_eq_mul]

/-- **Gilbert–Varshamov bound, rate form.** Let `α` be an alphabet with `q ≥ 2` letters, let
`0 ≤ δ ≤ 1 - 1/q`, and let `n, d` be natural numbers with `1 ≤ d` and `d - 1 ≤ δ n`. There is a
code `C` of length `n` over `α` with any two distinct codewords at Hamming distance at least `d`
and `|C| ≥ exp (n (log q - Real.qaryEntropy q δ)) = q ^ {(1 - H_q(δ)) n}`. When `δ n > 0`, taking
`d = ⌈δ n⌉` gives a code of rate at least `1 - H_q(δ)` and relative distance at least `δ`.

This is the general-code part of Theorem 4.2.1 of Guruswami, Rudra and Sudan, *Essential Coding
Theory* (draft of August 26, 2025), stated there for `0 ≤ δ < 1 - 1/q` as a family of codes; it
follows from Gilbert's greedy bound `exists_code_pow_le_card_mul_sum` and the volume estimate of
Proposition 3.3.3 (i) there (`sum_choose_mul_pow_le_exp`). -/
theorem exists_code_exp_le_card (hq : 2 ≤ Fintype.card α) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 - 1 / (Fintype.card α : ℝ)) (n : ℕ) {d : ℕ} (hd : 1 ≤ d)
    (hdδ : ((d - 1 : ℕ) : ℝ) ≤ δ * n) :
    ∃ C : Finset (Fin n → α),
      (∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂) ∧
      Real.exp (n * (Real.log (Fintype.card α) - Real.qaryEntropy (Fintype.card α) δ)) ≤
        C.card := by
  obtain ⟨C, hC, hcount⟩ := exists_code_pow_le_card_mul_sum (α := α) n hd
  refine ⟨C, hC, ?_⟩
  set q := Fintype.card α with hqdef
  set V := ∑ i ∈ range d, n.choose i * (q - 1) ^ i with hV
  have hvol : (V : ℝ) ≤ Real.exp (n * Real.qaryEntropy q δ) := by
    have := MathlibExt.InformationTheory.HammingBallVolume.sum_choose_mul_pow_le_exp
      (q := q) (n := n) (e := d - 1) hq hδ0 hδ1 hdδ
    rwa [Nat.sub_add_cancel hd] at this
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hcount' : (q : ℝ) ^ n ≤ C.card * V := by exact_mod_cast hcount
  have hqn : (q : ℝ) ^ n = Real.exp (n * Real.log q) := by
    rw [Real.exp_nat_mul, Real.exp_log hqpos]
  rw [mul_sub, Real.exp_sub, ← hqn, div_le_iff₀ (Real.exp_pos _)]
  calc (q : ℝ) ^ n ≤ C.card * V := hcount'
    _ ≤ C.card * Real.exp (n * Real.qaryEntropy q δ) :=
        mul_le_mul_of_nonneg_left hvol (Nat.cast_nonneg _)

end MathlibExt.Combinatorics.Coding.GilbertVarshamov
