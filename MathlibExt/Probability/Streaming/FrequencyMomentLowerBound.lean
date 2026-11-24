/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Streaming.Algorithm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial space for estimating higher frequency moments

`space_lower_bound_freqMoment` bounds the memory of a one-pass estimator of the `k`-th frequency
moment for `k ≥ 6`. Compare independent uniform input blocks with blocks that each contain a copy
of the same hidden symbol. In the latter distribution the moment is at least the number of blocks
raised to the power `k`. In the former its expectation is at most a constant times the alphabet
size. The finite-state estimate below bounds the change in acceptance probability when planting
the symbol in one block at a time. With `p` blocks of length `m`, a constant gap in acceptance
forces `m = O(s p²)` for an estimator using `s` bits. Taking `p` of order `n^(1/k)` and
`m = ⌊n/p⌋` yields the asserted exponent.
-/

public section

open Finset Real
open scoped BigOperators

namespace MathlibExt.Probability.Streaming

private lemma expect_prod_iid {α : Type} [Fintype α] (m : ℕ) (g : α → ℝ) :
    (𝔼 x : Fin m → α, ∏ i, g (x i)) = (𝔼 a, g a) ^ m := by
  rw [expect_pow]
  simp

-- An encoder can select among only 2^s tests of the empirical distribution in a block.
private lemma block_information {α : Type} [Fintype α] [Nonempty α] {m s : ℕ}
    (enc : (Fin m → α) → Fin (2 ^ s)) (f : Fin (2 ^ s) → α → ℝ)
    (hf : ∀ q a, f q a ∈ Set.Icc 0 1) {θ : ℝ} (hθ : 0 < θ) (hsmall : θ ≤ 1 / 2) :
    (𝔼 x : Fin m → α, ∑ i, (f (enc x) (x i) - 𝔼 a, f (enc x) a)) * θ ≤
      s * log 2 + 2 * m * θ ^ 2 := by
  let μ q := 𝔼 a, f q a
  have hμ (q) : μ q ∈ Set.Icc 0 1 := by
    constructor
    · exact expect_nonneg fun a _ => (hf q a).1
    · exact (expect_le_expect (s := univ) fun a _ => (hf q a).2).trans_eq
        (expect_const univ_nonempty _)
  let g q a := 1 + θ * (f q a - μ q)
  have hdev (q a) : |θ * (f q a - μ q)| ≤ θ := by
    rw [abs_mul, abs_of_pos hθ]
    have h := hf q a
    have hh := hμ q
    exact (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [h.1, hh.2],
      by linarith [h.2, hh.1]⟩) hθ.le).trans_eq (mul_one _)
  have hpos (q a) : 0 < g q a := by
    dsimp [g]
    linarith [(abs_le.mp (hdev q a)).1]
  have hlog (q a) : θ * (f q a - μ q) - 2 * θ ^ 2 ≤ log (g q a) := by
    let z := θ * (f q a - μ q)
    have hz : |z| ≤ θ := hdev _ _
    have hzsq : z ^ 2 ≤ θ ^ 2 := (sq_le_sq).mpr (by simpa [abs_of_pos hθ] using hz)
    apply le_trans _ (one_sub_inv_le_log_of_pos (hpos q a))
    change z - 2 * θ ^ 2 ≤ 1 - (1 + z)⁻¹
    rw [le_sub_comm, inv_eq_one_div, div_le_iff₀ (by linarith [(abs_le.mp hz).1])]
    nlinarith [mul_nonneg (sq_nonneg θ) (show 0 ≤ 1 + 2 * z by linarith [(abs_le.mp hz).1])]
  -- For each fixed test, the product over independent positions has expectation one.
  have hg (q) : (𝔼 a, g q a) = 1 := by
    simp [g, expect_add_distrib, ← mul_expect, expect_sub_distrib, μ, univ_nonempty]
  let W (x : Fin m → α) := ∏ i, g (enc x) (x i)
  have hW (x) : 0 < W x := prod_pos fun _ _ => hpos _ _
  have hmean : (𝔼 x, W x) ≤ (2 : ℝ) ^ s := calc
    _ ≤ 𝔼 x : Fin m → α, ∑ q : Fin (2 ^ s), ∏ i, g q (x i) := by
      apply expect_le_expect
      exact fun x _ => single_le_sum (fun q _ => prod_nonneg fun i _ => (hpos q (x i)).le)
        (mem_univ (enc x))
    _ = _ := by simp [expect_sum_comm, expect_prod_iid, hg]
  -- Tangent-line bound for log at 2^s.
  have hlogW (x) : log (W x) ≤ s * log 2 + W x / (2 : ℝ) ^ s - 1 := by
    have ht := log_le_sub_one_of_pos (div_pos (hW x) (by positivity : 0 < (2 : ℝ) ^ s))
    rw [log_div (hW x).ne' (by positivity), log_pow] at ht
    linarith
  have hx (x : Fin m → α) : (∑ i, (f (enc x) (x i) - μ (enc x))) * θ -
      m * (2 * θ ^ 2) ≤ s * log 2 + ((2 : ℝ) ^ s)⁻¹ * W x - 1 := by
    have h := sum_le_sum (s := (univ : Finset (Fin m))) fun i _ => hlog (enc x) (x i)
    simp only [sum_sub_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h
    rw [← log_prod (fun i _ => (hpos _ _).ne')] at h
    have hu := hlogW x
    rw [div_eq_inv_mul] at hu
    change _ ≤ log (W x) at h
    simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith only [hu, h]
  have hm := expect_le_expect (s := univ) (fun x _ => hx x)
  simp only [expect_sub_distrib, expect_add_distrib, ← expect_mul, ← mul_expect,
    expect_const univ_nonempty] at hm
  have hratio : ((2 : ℝ) ^ s)⁻¹ * (𝔼 x, W x) ≤ 1 := by
    rw [← div_eq_inv_mul, div_le_one (by positivity)]
    exact hmean
  dsimp [μ] at hm
  linarith

-- Plant a uniform symbol at a uniform position. For fixed symbol and block the density
-- relative to uniform sampling is the alphabet size times its empirical frequency.
private noncomputable def density {n m : ℕ} (a : Fin n) (x : Fin m → Fin n) : ℝ :=
  𝔼 i, if x i = a then (n : ℝ) else 0

private lemma density_nonneg {n m : ℕ} (a : Fin n) (x : Fin m → Fin n) :
    0 ≤ density a x := expect_nonneg fun _ _ => by split <;> positivity

private lemma density_mean {n m : ℕ} [NeZero n] [NeZero m] (a : Fin n) :
    (𝔼 x : Fin m → Fin n, density a x) = 1 := by
  unfold density
  rw [expect_comm]
  apply (expect_congr rfl ?_).trans (expect_const univ_nonempty 1)
  intro i _
  have h := Fintype.sum_piFinset_apply (fun b : Fin n => if b = a then (n : ℝ) else 0) univ i
  cases m with
  | zero => exact Fin.elim0 i
  | succ m =>
    simp only [Fintype.piFinset_univ, card_univ, Fintype.card_fin, Nat.add_sub_cancel,
      nsmul_eq_mul, sum_ite_eq', mem_univ, ite_true] at h
    rw [Fintype.expect_eq_sum_div_card, h]
    simp [pow_succ, NeZero.ne n]

private lemma density_test {n m : ℕ} [NeZero n] (x : Fin m → Fin n) (f : Fin n → ℝ) :
    (𝔼 a, density a x * f a) = 𝔼 i, f (x i) := by
  simp only [density, expect_mul, expect_comm (univ : Finset (Fin n)) (univ : Finset (Fin m))]
  apply expect_congr rfl
  intro i _
  rw [Fintype.expect_eq_sum_div_card]
  simp [ite_mul, Fintype.card_fin, NeZero.ne n]

private lemma density_pos_mem {n m : ℕ} {a : Fin n} {x : Fin m → Fin n}
    (h : 0 < density a x) : a ∈ List.ofFn x := by
  contrapose! h
  simp only [List.mem_ofFn, not_exists] at h
  simp [density, h]

private lemma one_block {n m s : ℕ} [NeZero n] [NeZero m]
    (enc : (Fin m → Fin n) → Fin (2 ^ s)) (f : Fin (2 ^ s) → Fin n → ℝ)
    (hf : ∀ q a, f q a ∈ Set.Icc 0 1) {θ : ℝ} (hθ : 0 < θ) (hsmall : θ ≤ 1 / 2) :
    (𝔼 x : Fin m → Fin n, 𝔼 a, density a x * f (enc x) a) ≤
      (𝔼 x : Fin m → Fin n, 𝔼 a, f (enc x) a) + (s * log 2 / (m * θ) + 2 * θ) := by
  simp_rw [density_test]
  have h := block_information enc f hf hθ hsmall
  have hm : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have he (x : Fin m → Fin n) : (∑ i, (f (enc x) (x i) - 𝔼 a, f (enc x) a)) =
      (m : ℝ) * ((𝔼 i, f (enc x) (x i)) - 𝔼 a, f (enc x) a) := by
    rw [mul_sub]
    simp [sum_sub_distrib, nsmul_eq_mul, Fintype.expect_eq_sum_div_card]
    field_simp
  simp_rw [he] at h
  rw [← mul_expect, expect_sub_distrib] at h
  have heq := div_mul_cancel₀ ((s : ℝ) * log 2) (mul_ne_zero hm.ne' hθ.ne')
  apply (le_of_mul_le_mul_right (a := (m : ℝ) * θ) _ (mul_pos hm hθ))
  linarith only [show (m : ℝ) * _ * θ ≤ _ from h, heq]

private def blockStream {α : Type} {m p : ℕ} (X : Fin p → Fin m → α) : List α :=
  (List.ofFn fun i => List.ofFn (X i)).flatten

private lemma blockStream_cons {α : Type} {m p : ℕ} (x : Fin m → α)
    (X : Fin p → Fin m → α) :
    blockStream (Fin.cons x X) = List.ofFn x ++ blockStream X := by
  simp [blockStream, List.ofFn_succ]

private lemma stream_length {α : Type} {m p : ℕ} (X : Fin p → Fin m → α) :
    (blockStream X).length = p * m := by
  induction p with
  | zero => simp [blockStream]
  | succ p ih =>
    rw [← Fin.cons_self_tail X, blockStream_cons, List.length_append, ih]
    simp [Nat.succ_mul, Nat.add_comm]

private noncomputable def blockLaw {n m s : ℕ} (w : (Fin m → Fin n) → ℝ)
    (step : Fin (2 ^ s) → Fin n → Fin (2 ^ s)) (p : ℕ) (q : Fin (2 ^ s))
    (test : Fin (2 ^ s) → ℝ) : ℝ :=
  𝔼 X : Fin p → Fin m → Fin n, (∏ i, w (X i)) * test ((blockStream X).foldl step q)

private lemma expect_cons {β : Type} [Fintype β] {p : ℕ} (f : (Fin (p + 1) → β) → ℝ) :
    (𝔼 X, f X) = 𝔼 x, 𝔼 X, f (Fin.cons x X) := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (p + 1) => β)
  calc
    _ = 𝔼 z : β × (Fin p → β), f (e z) :=
      (expect_equiv e (by simp) (by simp)).symm
    _ = _ := by simpa only [univ_product_univ, e, Fin.consEquiv_apply] using
        (expect_product univ univ (fun z => f (e z)))

private lemma blockLaw_succ {n m s p : ℕ} (w step q test) :
    blockLaw (n := n) (m := m) (s := s) w step (p + 1) q test =
      𝔼 x, w x * blockLaw w step p ((List.ofFn x).foldl step q) test := by
  unfold blockLaw
  rw [expect_cons]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, blockStream_cons,
    List.foldl_append, mul_expect, mul_assoc]

private lemma blockLaw_range {n m s p : ℕ} [NeZero n] [NeZero m] (a : Fin n)
    (step q) (test : Fin (2 ^ s) → ℝ) (h : ∀ q, test q ∈ Set.Icc 0 1) :
    blockLaw (m := m) (density a) step p q test ∈ Set.Icc 0 1 := by
  let d (X : Fin p → Fin m → Fin n) := ∏ i, density a (X i)
  have hd (X) : 0 ≤ d X := prod_nonneg fun _ _ => density_nonneg _ _
  constructor
  · exact expect_nonneg fun X _ => mul_nonneg (hd X) (h _).1
  · calc
      _ ≤ 𝔼 X, d X := expect_le_expect fun X _ => mul_le_of_le_one_right (hd X) (h _).2
      _ = 1 := by simp [d, expect_prod_iid, density_mean]

-- Replace the first planted block by a uniform block. The score for each possible next state
-- is its acceptance probability on the remaining planted blocks.
private lemma hidden_blocks {n m s : ℕ} [NeZero n] [NeZero m]
    (step : Fin (2 ^ s) → Fin n → Fin (2 ^ s)) (test : Fin (2 ^ s) → ℝ)
    (hf : ∀ q, test q ∈ Set.Icc 0 1) {θ : ℝ} (hθ : 0 < θ) (hsmall : θ ≤ 1 / 2)
    (p : ℕ) (q : Fin (2 ^ s)) :
    (𝔼 a : Fin n, blockLaw (m := m) (density a) step p q test) ≤
      blockLaw (m := m) (fun _ => 1) step p q test +
        p * (s * log 2 / (m * θ) + 2 * θ) := by
  induction p generalizing q with
  | zero => simp [blockLaw, blockStream, univ_nonempty]
  | succ p ih =>
    let enc (x : Fin m → Fin n) := (List.ofFn x).foldl step q
    let f (q : Fin (2 ^ s)) (a : Fin n) := blockLaw (m := m) (density a) step p q test
    let err := s * log 2 / (m * θ) + 2 * θ
    have h := one_block enc f (fun q a => blockLaw_range a step q test hf) hθ hsmall
    simp_rw [blockLaw_succ, one_mul]
    rw [expect_comm]
    refine h.trans ?_
    have hh := expect_le_expect (s := univ) (fun x _ => ih (enc x))
    rw [expect_add_distrib, expect_const univ_nonempty] at hh
    change (𝔼 x, 𝔼 a, f (enc x) a) + err ≤
      (𝔼 x, blockLaw (fun _ => 1) step p (enc x) test) + ↑(p + 1) * err
    push_cast
    dsimp [f, err, enc] at *
    linarith

private lemma stream_count {m n p : ℕ} (X : Fin p → Fin m → Fin n) (a : Fin n) :
    (blockStream X).count a = ∑ i, (List.ofFn (X i)).count a := by
  induction p with
  | zero => simp [blockStream]
  | succ p ih =>
    rw [← Fin.cons_self_tail X, blockStream_cons, List.count_append, ih, Fin.sum_univ_succ]
    simp

private lemma planted_moment {m n p : ℕ} (k : ℕ) (a : Fin n) (X : Fin p → Fin m → Fin n)
    (hw : (∏ i, density a (X i)) ≠ 0) : p ^ k ≤ freqMoment k (blockStream X) := by
  have h (i) : 1 ≤ (List.ofFn (X i)).count a := by
    apply List.count_pos_iff.mpr
    exact density_pos_mem (lt_of_le_of_ne (density_nonneg _ _)
      (fun he => hw (prod_eq_zero (mem_univ i) he.symm)))
  have hh := sum_le_sum (s := univ) (fun i _ => h i)
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hh
  rw [← stream_count] at hh
  exact (Nat.pow_le_pow_left hh k).trans
    (single_le_sum (f := fun b => (blockStream X).count b ^ k)
      (fun _ _ => Nat.zero_le _) (mem_univ a))

-- A fixed symbol has a binomial count in the uniform stream. Its exponential moment
-- bounds every fixed power of the count.
private lemma uniform_moment {m n p : ℕ} [NeZero n] (k : ℕ) (hlen : p * m ≤ n) :
    (𝔼 X : Fin p → Fin m → Fin n, (freqMoment k (blockStream X) : ℝ)) ≤
      n * ((k.factorial : ℝ) * exp (exp 1 - 1)) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have he : 0 ≤ exp 1 - 1 := sub_nonneg.mpr (one_le_exp (by norm_num))
  have per (a : Fin n) :
      (𝔼 X : Fin p → Fin m → Fin n, exp ((blockStream X).count a : ℝ)) ≤ exp (exp 1 - 1) := by
    let g (b : Fin n) := if b = a then exp 1 else 1
    have hpow (x : Fin m → Fin n) : exp ((List.ofFn x).count a : ℝ) = ∏ i, g (x i) := by
      simp [g, prod_ite, ← exp_nat_mul]
    have hs (X : Fin p → Fin m → Fin n) :
        exp ((blockStream X).count a : ℝ) = ∏ i, ∏ j, g (X i j) := by
      rw [stream_count, Nat.cast_sum, exp_sum]
      simp_rw [hpow]
    have hg : (𝔼 b, g b) = 1 + (exp 1 - 1) / n := by
      have ht (b) : g b = 1 + (if b = a then exp 1 - 1 else 0) := by
        by_cases h : b = a <;> simp [g, h]
      simp_rw [ht, expect_add_distrib, expect_const univ_nonempty]
      rw [Fintype.expect_eq_sum_div_card]
      simp
    simp_rw [hs]
    rw [expect_prod_iid p (fun x : Fin m → Fin n => ∏ j, g (x j)), expect_prod_iid, hg, ← pow_mul]
    exact (pow_le_pow_right₀ (by linarith [div_nonneg he hn.le])
      (by rwa [Nat.mul_comm])).trans (one_add_div_pow_le_exp (by linarith))
  have hk : 0 < (k.factorial : ℝ) := by positivity
  calc
    _ = ∑ a, 𝔼 X : Fin p → Fin m → Fin n, ((blockStream X).count a : ℝ) ^ k := by
      simp [freqMoment, expect_sum_comm]
    _ ≤ ∑ _a : Fin n, (k.factorial : ℝ) * exp (exp 1 - 1) := by
      apply sum_le_sum
      intro a _
      calc
        _ ≤ 𝔼 X : Fin p → Fin m → Fin n, k.factorial * exp ((blockStream X).count a : ℝ) := by
          refine expect_le_expect fun X _ => ?_
          exact ((div_le_iff₀ hk).1 (pow_div_factorial_le_exp _ (Nat.cast_nonneg _) k)).trans_eq
            (mul_comm _ _)
        _ ≤ _ := by rw [← mul_expect]; exact mul_le_mul_of_nonneg_left (per a) hk.le
    _ = _ := by simp [nsmul_eq_mul]

private noncomputable def errorBit {n s : ℕ} {R : Type} (A : StreamingAlgorithm (Fin n) R s)
    (k : ℕ) (l : List (Fin n)) (r : R) : ℝ :=
  if |A.output r l - freqMoment k l| ≤ 0.1 * (freqMoment k l : ℝ) then 0 else 1

private lemma error_mean {n s : ℕ} {R : Type} [Fintype R] [Nonempty R]
    (A : StreamingAlgorithm (Fin n) R s) (k : ℕ) (l : List (Fin n)) :
    (𝔼 r, errorBit A k l r) =
      A.failProb (fun l z => |z - freqMoment k l| ≤ 0.1 * (freqMoment k l : ℝ)) l := by
  classical
  rw [Fintype.expect_eq_sum_div_card, StreamingAlgorithm.failProb]
  congr 1
  rw [← sum_boole]
  apply sum_congr rfl
  intro r _
  unfold errorBit
  split <;> simp_all

private lemma space_pos {n s k : ℕ} [NeZero n] (hk : 0 < k) {γ : ℝ} (hγ : γ < 1 / 2)
    {R : Type} [Fintype R] [Nonempty R] (A : StreamingAlgorithm (Fin n) R s)
    (hA : ∀ l : List (Fin n), l.length ≤ n → (𝔼 r, errorBit A k l r) ≤ γ) : 0 < s := by
  by_contra! hz
  obtain rfl : s = 0 := Nat.eq_zero_of_le_zero hz
  have hs (r : R) : 1 ≤ errorBit A k [] r + errorBit A k [0] r := by
    have : Subsingleton (Fin (2 ^ 0)) := by
      simpa only [pow_zero] using (inferInstance : Subsingleton (Fin 1))
    have hout : A.output r [0] = A.output r [] := congrArg (A.out r) (Subsingleton.elim _ _)
    have h1 : freqMoment k ([0] : List (Fin n)) = 1 := by
      simp [freqMoment, List.count_singleton, apply_ite (· ^ k), zero_pow hk.ne']
    have h0 : freqMoment k ([] : List (Fin n)) = 0 := by simp [freqMoment, zero_pow hk.ne']
    simp only [errorBit, hout, h1, h0, Nat.cast_zero, Nat.cast_one, mul_zero, sub_zero,
      mul_one, abs_nonpos_iff]
    split_ifs <;> simp_all
    norm_num at *
  have h := expect_le_expect (s := univ) fun r _ => hs r
  rw [expect_const univ_nonempty, expect_add_distrib] at h
  linarith [hA [] (by simp), hA [0] (by simpa using (show 1 ≤ n by have := NeZero.ne n; omega))]

-- Accept outputs at least half the planted lower bound. On ordinary streams the acceptance
-- probability is controlled by the error probability and the expected frequency moment.
private lemma distinguish {n m p s : ℕ} [NeZero n] [NeZero m] [NeZero p] (k : ℕ)
    {R : Type} [Fintype R] [Nonempty R] (A : StreamingAlgorithm (Fin n) R s)
    {γ : ℝ} (hA : ∀ l : List (Fin n), l.length ≤ n → (𝔼 r, errorBit A k l r) ≤ γ)
    (hlen : p * m ≤ n) {θ : ℝ} (hθ : 0 < θ) (hsmall : θ ≤ 1 / 2) :
    1 - 2 * γ ≤ (3 / (p : ℝ) ^ k) * (n * ((k.factorial : ℝ) * exp (exp 1 - 1))) +
      p * (s * log 2 / (m * θ) + 2 * θ) := by
  let T := (p : ℝ) ^ k
  have hp : 0 < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hT : 0 < T := pow_pos hp _
  let test (r : R) (q : Fin (2 ^ s)) : ℝ := if T / 2 ≤ A.out r q then 1 else 0
  let sig (l : List (Fin n)) (r : R) := test r (l.foldl (A.step r) (A.init r))
  have hsig (l r) : sig l r = if T / 2 ≤ A.output r l then 1 else 0 := rfl
  have htest r q : test r q ∈ Set.Icc 0 1 := by dsimp [test]; split <;> constructor <;> norm_num
  let D (a : Fin n) (X : Fin p → Fin m → Fin n) := ∏ i, density a (X i)
  have hD a X : 0 ≤ D a X := prod_nonneg fun _ _ => density_nonneg _ _
  have hnull (l : List (Fin n)) (hl : l.length ≤ n) :
      (𝔼 r, sig l r) ≤ γ + 3 / T * freqMoment k l := by
    have hs (r) : sig l r ≤ errorBit A k l r + 3 / T * freqMoment k l := by
      rw [hsig]
      unfold errorBit
      have hF : 0 ≤ (freqMoment k l : ℝ) := by positivity
      have hz : 0 ≤ 3 / T * (freqMoment k l : ℝ) := by positivity
      split_ifs with high good good
      · have hu := (abs_le.mp good).2
        have hu' : T ≤ 3 * (freqMoment k l : ℝ) := by linarith
        rw [zero_add, div_mul_eq_mul_div, le_div_iff₀ hT]
        linarith
      all_goals linarith
    have hh := expect_le_expect (s := univ) (fun r _ => hs r)
    rw [expect_add_distrib, expect_const univ_nonempty] at hh
    linarith [hA l hl]
  have hplant (l : List (Fin n)) (hl : l.length ≤ n) (hF : T ≤ freqMoment k l) :
      1 - γ ≤ 𝔼 r, sig l r := by
    have hs (r) : 1 - errorBit A k l r ≤ sig l r := by
      rw [hsig]
      unfold errorBit
      split_ifs with good high high
      · norm_num
      · linarith [(abs_le.mp good).1]
      all_goals norm_num
    have hh := expect_le_expect (s := univ) (fun r _ => hs r)
    rw [expect_sub_distrib, expect_const univ_nonempty] at hh
    linarith [hA l hl]
  have upper : (𝔼 X : Fin p → Fin m → Fin n, 𝔼 r, sig (blockStream X) r) ≤
      γ + 3 / T * (n * ((k.factorial : ℝ) * exp (exp 1 - 1))) := by
    have h := expect_le_expect (s := univ) (fun X _ =>
      hnull (blockStream X) ((stream_length X).trans_le hlen))
    rw [expect_add_distrib, expect_const univ_nonempty, ← mul_expect] at h
    exact h.trans (add_le_add_right (mul_le_mul_of_nonneg_left (uniform_moment k hlen)
      (show 0 ≤ 3 / T by positivity)) _)
  have lower (a : Fin n) : 1 - γ ≤
      𝔼 X : Fin p → Fin m → Fin n, D a X * (𝔼 r, sig (blockStream X) r) := by
    have hs (X : Fin p → Fin m → Fin n) :
        D a X * (1 - γ) ≤ D a X * (𝔼 r, sig (blockStream X) r) := by
      by_cases h : D a X = 0
      · simp [h]
      apply mul_le_mul_of_nonneg_left _ (hD a X)
      exact hplant _ ((stream_length X).trans_le hlen)
        (by dsimp [T]; exact_mod_cast planted_moment k a X h)
    have h := expect_le_expect (s := univ) (fun X _ => hs X)
    simpa only [← expect_mul, D, expect_prod_iid, density_mean, one_pow, one_mul] using h
  have hu := expect_le_expect (s := univ) (fun (r : R) _ =>
    hidden_blocks (m := m) (A.step r) (test r) (htest r) hθ hsmall p (A.init r))
  have hl := expect_le_expect (s := univ) (fun a _ => lower a)
  rw [expect_const univ_nonempty] at hl
  rw [expect_add_distrib, expect_const univ_nonempty] at hu
  simp only [blockLaw, prod_const_one, one_mul] at hu
  rw [expect_comm (univ : Finset R) (univ : Finset (Fin n))] at hu
  simp_rw [expect_comm (univ : Finset R) (univ : Finset (Fin p → Fin m → Fin n)),
    ← mul_expect] at hu
  dsimp [D, sig] at hl upper
  change 1 - 2 * γ ≤ 3 / T * _ + _
  linarith only [hl, hu, upper]

/-- **Polynomial space for approximating `F_k`, `k ≥ 6`.** For every fixed integer `k > 5` and
every `0 < γ < 1/2` there is `c > 0` such that every randomized streaming algorithm over `Fin n`
with `s` bits of memory that, on every stream of at most `n` elements, outputs `Z` with
`|Z - F_k| > 0.1 F_k` with probability less than `γ` uses `s ≥ c n^{1 - 5/k}` bits (N. Alon,
Y. Matias and M. Szegedy, J. Comput. System Sci. 58 (1999), Theorem 3.2, via the multiparty
unique-intersection game of Proposition 3.3). The seed is not charged to the memory. This is
harmless because Proposition 3.3 is proved against a fixed input distribution: after amplification
by independent copies and averaging over that distribution, one seed can be fixed, which gives a
deterministic protocol to which the distributional bound applies, whatever the size of the seed
space. -/
theorem space_lower_bound_freqMoment :
    ∀ k : ℕ, 5 < k → ∀ γ : ℝ, 0 < γ → γ < 1 / 2 → ∃ c : ℝ, 0 < c ∧
      ∀ (n s : ℕ) (R : Type) [Fintype R] [Nonempty R] (A : StreamingAlgorithm (Fin n) R s),
        (∀ l : List (Fin n), l.length ≤ n →
          A.failProb (fun l z => |z - freqMoment k l| ≤ 0.1 * (freqMoment k l : ℝ)) l < γ) →
        c * (n : ℝ) ^ (1 - 5 / (k : ℝ)) ≤ s := by
  classical
  intro k hk γ hγ hhalf
  let d := (1 - 2 * γ) / 8
  have hd : 0 < d := by dsimp [d]; linarith
  have hd' : d ≤ 1 / 2 := by dsimp [d]; linarith
  let C := (k.factorial : ℝ) * exp (exp 1 - 1)
  let B := 3 * C / d
  let K := 1 + log 2 / d ^ 2
  let e := (k : ℝ)⁻¹
  have hB : 0 < B := by dsimp [B, C]; positivity
  have hlog : 0 < log 2 := log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  let L := B ^ e + 1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨(K * L ^ 3)⁻¹, by positivity, ?_⟩
  intro n s R _ _ A hA
  by_cases hn0 : n = 0
  · subst n
    have hpos : 0 < 1 - 5 / (k : ℝ) := by
      rw [sub_pos, div_lt_one (by positivity)]
      exact_mod_cast hk
    simp [zero_rpow hpos.ne']
  have : NeZero n := ⟨hn0⟩
  have hn : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hA' (l : List (Fin n)) (hl : l.length ≤ n) : (𝔼 r, errorBit A k l r) ≤ γ :=
    (error_mean A k l).trans_le (hA l hl).le
  have hs : 1 ≤ (s : ℝ) := by exact_mod_cast space_pos (by omega : 0 < k) hhalf A hA'
  -- Choose enough blocks for the planted moment to dominate the uniform expectation.
  let p := ⌈(B * n) ^ e⌉₊
  have hceil : (B * n) ^ e ≤ (p : ℝ) := Nat.le_ceil _
  have hp : 0 < (p : ℝ) := lt_of_lt_of_le (by positivity) hceil
  have hpN : 0 < p := Nat.cast_pos.mp hp
  have : NeZero p := ⟨hpN.ne'⟩
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hpN
  have hr := one_le_rpow hn he.le
  have hsize : (p : ℝ) ≤ L * (n : ℝ) ^ e := by
    calc
      _ ≤ (B * n) ^ e + 1 := (Nat.ceil_lt_add_one (by positivity)).le
      _ ≤ _ := by rw [mul_rpow hB.le (by positivity)]; dsimp [L]; linarith
  have hTk : B * n ≤ (p : ℝ) ^ k := by
    have h := pow_le_pow_left₀ (by positivity) hceil k
    rwa [rpow_inv_natCast_pow (by positivity) (by omega : k ≠ 0)] at h
  let m := n / p
  have hlen : p * m ≤ n := Nat.mul_div_le n p
  have hmBound : (m : ℝ) ≤ (log 2 / d ^ 2) * s * p ^ 2 := by
    by_cases hm0 : m = 0
    · rw [hm0, Nat.cast_zero]
      positivity
    have : NeZero m := ⟨hm0⟩
    have hm : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
    have hT : 0 < (p : ℝ) ^ k := pow_pos hp _
    have hcost : 3 / (p : ℝ) ^ k * (n * C) ≤ d := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hT]
      have h := mul_le_mul_of_nonneg_right hTk hd.le
      dsimp [B] at h
      field_simp at h
      linarith only [h]
    have hθ : 0 < d / p := div_pos hd hp
    have hθ' : d / p ≤ 1 / 2 := by
      exact (div_le_self hd.le hp1).trans hd'
    have h := distinguish k A hA' hlen hθ hθ'
    change 1 - 2 * γ ≤ 3 / (p : ℝ) ^ k * (n * C) + _ at h
    have hadv : d ≤ p * (s * log 2 / (m * (d / p))) := by
      have hδ := div_mul_cancel₀ d hp.ne'
      dsimp [d] at *
      linarith only [h, hcost, hδ, hd.le]
    field_simp [hp.ne', hm.ne', hd.ne'] at hadv ⊢
    linarith only [hadv]
  have hnat : n < p * (m + 1) := (Nat.div_lt_iff_lt_mul hpN).mp (Nat.lt_succ_self m)
    |>.trans_le (Nat.mul_comm _ _).le
  have hnBound : (n : ℝ) ≤ K * s * (p : ℝ) ^ 3 := calc
    _ ≤ (p : ℝ) * ((m : ℝ) + 1) := by exact_mod_cast hnat.le
    _ ≤ (p : ℝ) * (K * s * (p : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hp.le
      have hp2 : 1 ≤ (p : ℝ) ^ 2 := one_le_pow₀ hp1
      dsimp [K]
      nlinarith only [hmBound, one_le_mul_of_one_le_of_one_le hs hp2]
    _ = _ := by ring
  have hpow : ((n : ℝ) ^ e) ^ (3 : ℕ) ≤ (n : ℝ) ^ (5 / (k : ℝ)) := by
    rw [← rpow_natCast, ← rpow_mul (by positivity)]
    apply rpow_le_rpow_of_exponent_le hn
    dsimp [e]
    rw [div_eq_mul_inv]
    linarith [inv_pos.mpr (by exact_mod_cast (by omega : 0 < k) : 0 < (k : ℝ))]
  have hfinal : (n : ℝ) ≤ (K * L ^ 3 * s) * (n : ℝ) ^ (5 / (k : ℝ)) := calc
    _ ≤ K * s * (p : ℝ) ^ 3 := hnBound
    _ ≤ K * s * (L * (n : ℝ) ^ e) ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.le hsize 3) (by positivity)
    _ ≤ _ := by
      rw [mul_pow]
      nlinarith only [mul_le_mul_of_nonneg_left hpow (show 0 ≤ K * s * L ^ 3 by positivity)]
  rw [rpow_sub (by positivity), rpow_one, ← div_eq_inv_mul, div_le_iff₀ (by positivity),
    div_le_iff₀ (by positivity)]
  linarith only [hfinal]

end MathlibExt.Probability.Streaming
