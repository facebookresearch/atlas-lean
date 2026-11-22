/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Coding.ListDecoding
public import MathlibExt.InformationTheory.HammingBallVolume
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega

/-!
# List-decoding capacity

A code with `q ^ k` messages, `k ≤ (1 - H_q(ρ) - 1/L) n`, is `(ρ, L)`-list decodable for some
choice of codewords. The proof counts: among the `(q ^ n) ^ {q ^ k}` encoding maps, a bad map puts
`L + 1` messages in some ball of radius `ρn`; there are at most
`q ^ n · C(q ^ k, L + 1) · Vol_q(n, ρn) ^ {L + 1} · (q ^ n) ^ {q ^ k - L - 1}` bad maps, fewer than
all maps since `Vol_q(n, ρn) ≤ q ^ {H_q(ρ) n}`. This is the union bound of the probabilistic
proof, written as a count (`exists_encoding_listDecodable`, `exists_isListDecodable`).

Conversely, codes of rate `1 - H_q(ρ) + ε` have a ball of radius `ρn` with at least `q ^ {εn/2}`
codewords for large `n` (`exists_many_in_ball`), by averaging over the centre and the lower bound
`Vol_q(n, ρn) ≥ q ^ {H_q(ρ) n - o(n)}`.

## References

* V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025,
  Theorems 7.4.1 and 7.4.2 and their proofs in Section 7.4.1, equations (7.7)–(7.17).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Coding.ListDecodingCapacity

open Finset Real

/-- **List-decoding capacity, achievability.** Let `α` be an alphabet with `q ≥ 2` letters, let
`0 < ρ < 1 - 1/q`, `L ≥ 1`, and let `n, k` be natural numbers with
`k ≤ (1 - H_q(ρ) - 1/L) n`, where `H_q(ρ) = Real.qaryEntropy q ρ / log q`. There is an encoding
map `C : αᵏ → αⁿ` such that every Hamming ball of radius `ρn` contains the encodings of at most
`L` messages.

This is Theorem 7.4.2 (i) of Guruswami, Rudra and Sudan, *Essential Coding Theory* (draft of
August 26, 2025), in the form proved in Section 7.4.1, where the codewords of the `q ^ k` messages
are picked independently and uniformly at random and the union bound shows that a bad event has
probability at most `q ^ {-n/L} < 1`; here that union bound is a count of encoding maps. List
sizes are counted over messages, as in that proof. -/
theorem exists_encoding_listDecodable {α : Type*} [Fintype α] [DecidableEq α]
    (hq : 2 ≤ Fintype.card α) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 - 1 / (Fintype.card α : ℝ))
    {L : ℕ} (hL : 1 ≤ L) (n k : ℕ)
    (hk : (k : ℝ) ≤
      (1 - qaryEntropy (Fintype.card α) ρ / log (Fintype.card α) - 1 / (L : ℝ)) * n) :
    ∃ C : (Fin k → α) → (Fin n → α), ∀ y : Fin n → α,
      (univ.filter fun m => (hammingDist y (C m) : ℝ) ≤ ρ * n).card ≤ L := by
  classical
  set q := Fintype.card α with hqdef
  set e := ⌊ρ * n⌋₊ with he
  set N := Fintype.card (Fin k → α) with hN
  set V := ∑ i ∈ range (e + 1), n.choose i * (q - 1) ^ i with hV
  have hρn : 0 ≤ ρ * n := by positivity
  have hdist : ∀ y w : Fin n → α, (hammingDist y w : ℝ) ≤ ρ * n ↔ hammingDist y w ≤ e :=
    fun y w => (Nat.le_floor_iff hρn).symm
  simp_rw [hdist]
  -- Bad encoding maps put `L + 1` messages in one ball.
  set bad : Finset ((Fin k → α) → (Fin n → α)) :=
    univ.filter fun C => ∃ y, L < (univ.filter fun m => hammingDist y (C m) ≤ e).card with hbad
  set box : (Fin n → α) → Finset (Fin k → α) → Finset ((Fin k → α) → (Fin n → α)) :=
    fun y S => Fintype.piFinset fun m => if m ∈ S then Hamming.ball y e else univ with hbox
  have hsub : bad ⊆ (univ : Finset (Fin n → α)).biUnion fun y =>
      (powersetCard (L + 1) (univ : Finset (Fin k → α))).biUnion fun S => box y S := by
    intro C hC
    obtain ⟨y, hy⟩ := (mem_filter.mp hC).2
    obtain ⟨S, hS, hcard⟩ := exists_subset_card_eq (Nat.succ_le_of_lt hy)
    simp only [mem_biUnion, mem_univ, true_and, mem_powersetCard, subset_univ]
    refine ⟨y, S, hcard, ?_⟩
    simp only [hbox, Fintype.mem_piFinset]
    intro m
    split_ifs with hm
    · have := hS hm
      rw [mem_filter] at this
      rw [Hamming.mem_ball]
      exact this.2
    · exact mem_univ _
  -- The size of a box.
  have hboxcard : ∀ y, ∀ S ∈ powersetCard (L + 1) (univ : Finset (Fin k → α)),
      (box y S).card = V ^ (L + 1) * (q ^ n) ^ (N - (L + 1)) := by
    intro y S hS
    rw [mem_powersetCard] at hS
    simp only [hbox, Fintype.card_piFinset, apply_ite card, Hamming.card_ball, card_univ,
      Fintype.card_fun, Fintype.card_fin]
    rw [prod_ite, prod_const, prod_const]
    have h1 : (univ.filter fun m : Fin k → α => m ∈ S).card = L + 1 := by
      rw [filter_mem_eq_inter, univ_inter, hS.2]
    have h2 : (univ.filter fun m : Fin k → α => m ∉ S).card = N - (L + 1) := by
      have := card_filter_add_card_filter_not (s := (univ : Finset (Fin k → α))) (· ∈ S)
      rw [card_univ, h1] at this
      omega
    rw [h1, h2]
  have hbadcard :
      bad.card ≤ q ^ n * (N.choose (L + 1) * (V ^ (L + 1) * (q ^ n) ^ (N - (L + 1)))) := by
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    calc ∑ y : Fin n → α, ((powersetCard (L + 1) univ).biUnion fun S => box y S).card
        ≤ ∑ _y : Fin n → α, N.choose (L + 1) * (V ^ (L + 1) * (q ^ n) ^ (N - (L + 1))) := by
          refine sum_le_sum fun y _ => card_biUnion_le.trans ?_
          rw [sum_congr rfl (hboxcard y), sum_const, card_powersetCard, card_univ, smul_eq_mul]
      _ = q ^ n * (N.choose (L + 1) * (V ^ (L + 1) * (q ^ n) ^ (N - (L + 1)))) := by
          rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]
  have hall : (univ : Finset ((Fin k → α) → (Fin n → α))).card = (q ^ n) ^ N := by
    rw [card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]
  -- The count of bad maps is smaller than the count of all maps.
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hlogq : 0 < log (q : ℝ) := log_pos hq1
  have hqn : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  have hlt : bad.card < (univ : Finset ((Fin k → α) → (Fin n → α))).card := by
    rw [hall]
    rcases Nat.lt_or_ge N (L + 1) with hNL | hNL
    · rw [Nat.choose_eq_zero_of_lt hNL] at hbadcard
      simp only [zero_mul, mul_zero] at hbadcard
      have : 0 < (q ^ n) ^ N := by positivity
      omega
    refine lt_of_le_of_lt hbadcard ?_
    have hsplit : (q ^ n) ^ N = (q ^ n) ^ (L + 1) * (q ^ n) ^ (N - (L + 1)) := by
      rw [← pow_add, Nat.add_sub_cancel' hNL]
    rw [hsplit, ← mul_assoc, ← mul_assoc, mul_assoc (q ^ n)]
    rw [show q ^ n * (N.choose (L + 1) * V ^ (L + 1)) * (q ^ n) ^ (N - (L + 1)) =
      q ^ n * N.choose (L + 1) * V ^ (L + 1) * (q ^ n) ^ (N - (L + 1)) by ring]
    refine Nat.mul_lt_mul_of_pos_right ?_ (by positivity)
    -- Real-number estimate: `q ^ n · C(N, L + 1) · V ^ (L + 1) < (q ^ n) ^ (L + 1)`.
    have hV : (V : ℝ) ≤ exp (n * qaryEntropy q ρ) := by
      have := MathlibExt.InformationTheory.HammingBallVolume.sum_choose_mul_pow_le_exp
        (q := q) (n := n) (e := e) hq hρ0.le hρ1.le (Nat.floor_le hρn)
      simpa [hV] using this
    have hqpos : (0 : ℝ) < q := by linarith
    have hpow : ∀ j : ℕ, ((q : ℝ) ^ j) = exp (j * log q) := by
      intro j; rw [exp_nat_mul, exp_log hqpos]
    have hNq : (N : ℝ) = exp (k * log q) := by
      rw [hN, Fintype.card_fun, Fintype.card_fin]; push_cast; exact hpow k
    set H := qaryEntropy q ρ with hH
    set lq := log (q : ℝ) with hlq
    have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hkq : (k : ℝ) * lq + n * H ≤ n * lq - n * lq / L := by
      have h1 := mul_le_mul_of_nonneg_right hk hlogq.le
      have h2 : (1 - H / lq - 1 / (L : ℝ)) * n * lq = n * lq - n * H - n * lq / L := by
        field_simp
      linarith
    have hexp : (n : ℝ) * lq + (L + 1) * ((k : ℝ) * lq + n * H) ≤ (L + 1) * (n * lq) := by
      have h3 : (L + 1 : ℝ) * ((k : ℝ) * lq + n * H) ≤ (L + 1) * (n * lq - n * lq / L) :=
        mul_le_mul_of_nonneg_left hkq (by positivity)
      have h4 : (L + 1 : ℝ) * (n * lq - n * lq / L) = L * (n * lq) - n * lq / L := by
        field_simp; ring
      have h5 : 0 ≤ (n : ℝ) * lq / L := by positivity
      nlinarith
    have hchoose : (N.choose (L + 1) : ℝ) ≤ (N : ℝ) ^ (L + 1) / 2 := by
      refine (Nat.choose_le_pow_div (L + 1) N).trans ?_
      have : (2 : ℝ) ≤ ((L + 1).factorial : ℝ) := by
        have := Nat.self_le_factorial (L + 1)
        exact_mod_cast (by omega : 2 ≤ (L + 1).factorial)
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) this
    suffices h : ((q ^ n * N.choose (L + 1) * V ^ (L + 1) : ℕ) : ℝ) <
        (((q ^ n) ^ (L + 1) : ℕ) : ℝ) by
      exact_mod_cast h
    push_cast
    calc (q : ℝ) ^ n * (N.choose (L + 1) : ℝ) * (V : ℝ) ^ (L + 1)
        ≤ exp (n * lq) * ((N : ℝ) ^ (L + 1) / 2) * exp (n * H) ^ (L + 1) := by
          rw [hpow n]
          gcongr
      _ = exp ((n : ℝ) * lq + (L + 1) * ((k : ℝ) * lq + n * H)) / 2 := by
          rw [hNq, ← exp_nat_mul, ← exp_nat_mul]
          push_cast
          rw [show (n : ℝ) * lq + (L + 1) * ((k : ℝ) * lq + n * H) =
            n * lq + (L + 1) * (k * lq) + (L + 1) * (n * H) by ring, exp_add, exp_add]
          ring
      _ ≤ exp ((L + 1) * (n * lq)) / 2 := by gcongr
      _ < exp ((L + 1) * (n * lq)) := half_lt_self (exp_pos _)
      _ = ((q : ℝ) ^ n) ^ (L + 1) := by
          rw [hpow n, ← exp_nat_mul]; push_cast; ring_nf
  obtain ⟨C, -, hC⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨C, fun y => ?_⟩
  by_contra h
  push Not at h
  exact hC (mem_filter.mpr ⟨mem_univ _, y, h⟩)

/-- **List-decoding capacity, converse.** Let `α` be an alphabet with `q ≥ 2` letters, let
`0 < ρ < 1 - 1/q` and `ε > 0`. For all large enough `n`, every code `C` of length `n` over `α`
with at least `q ^ {(1 - H_q(ρ) + ε) n}` codewords has a Hamming ball of radius `ρn` containing
at least `q ^ {εn/2}` codewords; so a `(ρ, L)`-list-decodable code of rate `1 - H_q(ρ) + ε` has
`L ≥ q ^ {εn/2}`.

This is Theorem 7.4.1 (ii) (equivalently Theorem 7.4.2 (ii)) of Guruswami, Rudra and Sudan,
*Essential Coding Theory* (draft of August 26, 2025), which states `L ≥ q ^ {Ω(εn)}`, with the
constant in `Ω` taken to be `1/2`. The proof is theirs: average over a uniformly random centre
(`exists_mul_card_filter_ge`) and bound the volume below (`sum_choose_mul_pow_ge_exp`,
Proposition 3.3.3 (ii)). Here `q ^ x` is written `exp (x log q)` and
`H_q(ρ) log q = Real.qaryEntropy q ρ`. -/
theorem exists_many_in_ball {α : Type*} [Fintype α] [DecidableEq α]
    (hq : 2 ≤ Fintype.card α) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 - 1 / (Fintype.card α : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ C : Finset (Fin n → α),
      exp (n * (log (Fintype.card α) - qaryEntropy (Fintype.card α) ρ +
        ε * log (Fintype.card α))) ≤ C.card →
      ∃ y : Fin n → α,
        exp (ε * n / 2 * log (Fintype.card α)) ≤
          ((C.filter fun c => (hammingDist y c : ℝ) ≤ ρ * n).card : ℝ) := by
  classical
  set q := Fintype.card α with hqdef
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hlq : 0 < log (q : ℝ) := log_pos hq1
  have hρle : ρ ≤ 1 := by
    have : 0 < 1 / (q : ℝ) := by positivity
    linarith
  obtain ⟨N, hN⟩ := MathlibExt.InformationTheory.HammingBallVolume.sum_choose_mul_pow_ge_exp
    hq hρ0.le hρle (η := ε * log q / 2) (by positivity)
  refine ⟨N, fun n hn C hC => ?_⟩
  have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨y, hy⟩ :=
    MathlibExt.Combinatorics.Coding.ListDecoding.exists_mul_card_filter_ge C ⌊ρ * n⌋₊
  refine ⟨y, ?_⟩
  have hρn : 0 ≤ ρ * n := by positivity
  have hfilter : (C.filter fun c => (hammingDist y c : ℝ) ≤ ρ * n) =
      C.filter fun c => hammingDist y c ≤ ⌊ρ * n⌋₊ := by
    refine filter_congr fun c _ => ?_
    exact (Nat.le_floor_iff hρn).symm
  rw [hfilter]
  set K := ((C.filter fun c => hammingDist y c ≤ ⌊ρ * n⌋₊).card : ℝ) with hK
  set V := ∑ i ∈ range (⌊ρ * n⌋₊ + 1), n.choose i * (q - 1) ^ i with hV
  have hV' : exp (n * qaryEntropy q ρ - ε * log q / 2 * n) ≤ (V : ℝ) := hN n hn
  have hy0 : C.card * V ≤ q ^ n * (C.filter fun c => hammingDist y c ≤ ⌊ρ * n⌋₊).card := hy
  have hy' : (C.card : ℝ) * V ≤ (q : ℝ) ^ n * K := by rw [hK]; exact_mod_cast hy0
  have hqn : (q : ℝ) ^ n = exp (n * log q) := by
    rw [exp_nat_mul, exp_log (by linarith)]
  have hprod : exp (n * (log q - qaryEntropy q ρ + ε * log q)) *
      exp (n * qaryEntropy q ρ - ε * log q / 2 * n) ≤ exp (n * log q) * K := by
    rw [← hqn]
    refine le_trans ?_ hy'
    exact mul_le_mul hC hV' (exp_pos _).le (Nat.cast_nonneg _)
  rw [← exp_add] at hprod
  have hsplit : (n : ℝ) * (log q - qaryEntropy q ρ + ε * log q) +
      (n * qaryEntropy q ρ - ε * log q / 2 * n) = n * log q + ε * n / 2 * log q := by ring
  rw [hsplit, exp_add, mul_le_mul_iff_right₀ (exp_pos _)] at hprod
  exact hprod

open MathlibExt.Combinatorics.Coding.ListDecoding in
/-- **Codes of rate `1 - H_q(ρ) - 1/L` that are list decodable.** Under the hypotheses of
`exists_encoding_listDecodable`, there is a code `C ⊆ αⁿ` that is list decodable from `⌊ρn⌋`
errors with list size `L` and has `q ^ k ≤ L · |C|` codewords: the set of codewords of the
encoding map, each of which has at most `L` preimages. So the rate of `C` is at least
`k / n - log_q L / n`, and `1 - H_q(ρ) - 1/L - o(1)` for `k = ⌊(1 - H_q(ρ) - 1/L) n⌋`
(Guruswami, Rudra and Sudan, *Essential Coding Theory*, draft of August 26, 2025, Theorem 7.4.2
(i), in the set form of Definition 7.2.1). -/
theorem exists_isListDecodable {α : Type*} [Fintype α] [DecidableEq α]
    (hq : 2 ≤ Fintype.card α) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 - 1 / (Fintype.card α : ℝ))
    {L : ℕ} (hL : 1 ≤ L) (n k : ℕ)
    (hk : (k : ℝ) ≤
      (1 - qaryEntropy (Fintype.card α) ρ / log (Fintype.card α) - 1 / (L : ℝ)) * n) :
    ∃ C : Finset (Fin n → α), IsListDecodable C ⌊ρ * n⌋₊ L ∧
      Fintype.card α ^ k ≤ L * C.card := by
  classical
  obtain ⟨E, hE⟩ := exists_encoding_listDecodable hq hρ0 hρ1 hL n k hk
  have hρn : 0 ≤ ρ * n := by positivity
  have hball : ∀ y : Fin n → α,
      (univ.filter fun m => hammingDist y (E m) ≤ ⌊ρ * n⌋₊).card ≤ L := by
    intro y
    have := hE y
    simp_rw [← Nat.le_floor_iff hρn] at this
    exact this
  refine ⟨univ.image E, fun y => ?_, ?_⟩
  · calc ((univ.image E).filter fun c => hammingDist y c ≤ ⌊ρ * n⌋₊).card
        = ((univ.filter fun m => hammingDist y (E m) ≤ ⌊ρ * n⌋₊).image E).card := by
          rw [filter_image]
      _ ≤ (univ.filter fun m => hammingDist y (E m) ≤ ⌊ρ * n⌋₊).card := card_image_le
      _ ≤ L := hball y
  · have h := card_le_mul_card_image (univ : Finset (Fin k → α)) L (f := E) fun c _ => by
      refine (card_le_card fun m hm => ?_).trans (hball c)
      simp only [mem_filter, mem_univ, true_and] at hm ⊢
      rw [hm, hammingDist_self]
      exact Nat.zero_le _
    rwa [card_univ, Fintype.card_fun, Fintype.card_fin] at h

end MathlibExt.Combinatorics.Coding.ListDecodingCapacity
