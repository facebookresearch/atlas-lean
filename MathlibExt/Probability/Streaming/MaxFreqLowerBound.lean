/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Streaming.Algorithm
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Space lower bound for approximating the largest multiplicity

`space_lower_bound_maxFreq` shows that a streaming algorithm which estimates the largest
multiplicity to relative error less than a third needs linearly many bits of memory.
Appending one symbol tests a membership bit of the prefix. We count how many bit strings the
algorithm can encode using the binary entropy bound for this random access scheme.
-/

public section

namespace MathlibExt.Probability.Streaming

open Finset Real

private noncomputable def wordPrefix {n : ℕ} (x : Fin n → Bool) : List (Fin n) :=
  (univ.filter fun i => x i).toList

private lemma maxFreq_query {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    maxFreq (wordPrefix x ++ [i]) = if x i then 2 else 1 := by
  have hcount (j : Fin n) : (wordPrefix x).count j = if x j then 1 else 0 := by
    by_cases hj : x j = true
    · simp only [hj, ite_true]
      exact List.count_eq_one_of_mem (nodup_toList _) (by simp [wordPrefix, hj])
    · simp only [hj]
      exact List.count_eq_zero_of_not_mem (by simp [wordPrefix, hj])
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    rw [List.count_append, hcount, List.count_singleton]
    by_cases hij : i = j
    · subst j
      cases x i <;> simp
    · simp only [beq_iff_eq, hij, ite_false, Nat.add_zero]
      split <;> split <;> decide
  · calc
      _ = (wordPrefix x ++ [i]).count i := by
        rw [List.count_append, hcount]
        cases x i <;> simp
      _ ≤ _ := Finset.le_sup (f := (wordPrefix x ++ [i]).count) (mem_univ i)

-- The sum of the log likelihoods of one bit is smallest at the allowed error rate.
private lemma bit_log_bound {R : Type} [Fintype R] (bad : R → Prop) [DecidablePred bad]
    {ε : ℝ} (hε : 0 < ε) (hhalf : ε < 1 / 2)
    (herr : ((univ.filter bad).card : ℝ) ≤ ε * Fintype.card R) :
    -(Fintype.card R : ℝ) * binEntropy ε ≤
      ∑ r, log (if bad r then ε else 1 - ε) := by
  have hs (r : R) : log (if bad r then ε else 1 - ε) =
      log (1 - ε) + (if bad r then 1 else 0) * (log ε - log (1 - ε)) := by
    by_cases h : bad r <;> simp [h]
  simp_rw [hs]
  rw [sum_add_distrib, ← sum_mul, sum_boole, sum_const, card_univ, nsmul_eq_mul,
    binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog_def]
  have hlog := log_le_log hε (show ε ≤ 1 - ε by linarith)
  nlinarith [mul_le_mul_of_nonpos_right herr (sub_nonpos.mpr hlog)]

-- Average over the public seed, for a fixed input word.
private lemma word_weight_bound {n : ℕ} {R : Type} [Fintype R] [Nonempty R]
    (x : Fin n → Bool) (guess : R → Fin n → Bool) {ε : ℝ} (hε : 0 < ε)
    (hhalf : ε < 1 / 2)
    (herr : ∀ i, ((univ.filter fun r => guess r i ≠ x i).card : ℝ) ≤ ε * Fintype.card R) :
    Fintype.card R * exp (-(n : ℝ) * binEntropy ε) ≤
      ∑ r, ∏ i, if guess r i ≠ x i then ε else 1 - ε := by
  let N : ℝ := Fintype.card R
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  let w (r : R) (i : Fin n) := if guess r i ≠ x i then ε else 1 - ε
  have hw (r i) : 0 < w r i := by dsimp [w]; split <;> linarith
  have hsum := sum_le_sum (s := (univ : Finset (Fin n))) fun i _ =>
    bit_log_bound (fun r => guess r i ≠ x i) hε hhalf (herr i)
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, sum_comm] at hsum
  have hmean : -(n : ℝ) * binEntropy ε ≤ (∑ r, ∑ i, log (w r i)) / N := by
    apply (le_div_iff₀ hN).2
    linarith only [hsum]
  have hJ := convexOn_exp.map_sum_le (t := (univ : Finset R)) (w := fun _ => N⁻¹)
    (p := fun r => ∑ i, log (w r i)) (fun _ _ => (inv_pos.mpr hN).le)
    (by simp [N, Fintype.card_ne_zero]) (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul, ← mul_sum, exp_sum, exp_log (hw _ _)] at hJ
  have h : exp (-(n : ℝ) * binEntropy ε) ≤ (∑ r, ∏ i, w r i) / N :=
    (exp_le_exp.mpr hmean).trans (by simpa only [div_eq_inv_mul] using hJ)
  rw [mul_comm (Fintype.card R : ℝ)]
  exact (le_div_iff₀ hN).mp h

-- For a fixed seed every state predicts one word. The product weights around each word sum to one.
private lemma state_weight_bound {n s : ℕ} (encode : (Fin n → Bool) → Fin (2 ^ s))
    (guess : Fin (2 ^ s) → Fin n → Bool) {ε : ℝ} (hε : 0 < ε) (hhalf : ε < 1 / 2) :
    (∑ x : Fin n → Bool, ∏ i, if guess (encode x) i ≠ x i then ε else 1 - ε) ≤
      (2 : ℝ) ^ s := by
  let w (m : Fin (2 ^ s)) (i : Fin n) (b : Bool) := if guess m i ≠ b then ε else 1 - ε
  have hw (m i b) : 0 ≤ w m i b := by dsimp [w]; split <;> linarith
  have htotal (m : Fin (2 ^ s)) : (∑ x : Fin n → Bool, ∏ i, w m i (x i)) = 1 := by
    rw [← Fintype.prod_sum (w m)]
    apply prod_eq_one
    intro i _
    cases h : guess m i <;> simp [w, h]
  calc
    _ ≤ ∑ x : Fin n → Bool, ∑ m, ∏ i, w m i (x i) :=
      sum_le_sum fun x _ => single_le_sum (fun m _ => prod_nonneg fun i _ => hw m i (x i))
        (mem_univ (encode x))
    _ = _ := by rw [sum_comm]; simp [htotal]

/-- **Linear space for approximating the largest multiplicity.** For every fixed `0 < ε < 1/2`
there is `c > 0` such that every randomized streaming algorithm over `Fin n` with `s` bits of
memory that, on every nonempty stream of length at most `2n`, outputs `Y` with
`|Y - F*_∞| ≥ F*_∞ / 3` with probability less than `ε` uses `s ≥ c n` bits (N. Alon, Y. Matias and
M. Szegedy, J. Comput. System Sci. 58 (1999), Proposition 3.1). The source does not exclude the
empty stream; it is excluded here because there `F*_∞ = 0` and no output meets the strict
accuracy requirement; the source's proof only uses streams with `F*_∞ ∈ {1, 2}`.

Proof (the source's, in the public-randomness model): Alice and Bob share the seed as a public
coin. Alice runs the algorithm on the elements of `x` and sends the `s`-bit memory content. Bob
answers "disjoint" at once if `y = ∅`; otherwise the stream `x` followed by `y` is nonempty, and
he finishes the run on `y` and answers "intersect" iff the output is at least `4/3`. Since
`(2/3, 4/3)` and `(4/3, 8/3)` are disjoint, this is a public-coin protocol of cost `s + O(1)` with
error less than `ε`. So `s + O(1) ≥ randComplexity (disjFn n) ε = Ω(n)`
(`randComplexity_disjFn_ge`), and `s ≥ 1` for `n ≥ 1`, because one memory state cannot separate
the streams `[0]` and `[0, 0]`. -/
theorem space_lower_bound_maxFreq :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ c : ℝ, 0 < c ∧
      ∀ (n s : ℕ) (R : Type) [Fintype R] [Nonempty R] (A : StreamingAlgorithm (Fin n) R s),
        (∀ l : List (Fin n), l ≠ [] → l.length ≤ 2 * n →
          A.failProb (fun l y => |y - maxFreq l| < (maxFreq l : ℝ) / 3) l < ε) →
        c * n ≤ s := by
  classical
  intro ε hε hhalf
  have htwo : 0 < log 2 := log_pos (by norm_num)
  have hent : binEntropy ε < log 2 := binEntropy_lt_log_two.mpr (by linarith)
  refine ⟨(log 2 - binEntropy ε) / log 2, div_pos (sub_pos.mpr hent) htwo, ?_⟩
  intro n s R _ _ A hA
  let encode (r : R) (x : Fin n → Bool) := (wordPrefix x).foldl (A.step r) (A.init r)
  let guess (r : R) (m : Fin (2 ^ s)) (i : Fin n) :=
    decide (4 / 3 ≤ A.out r (A.step r m i))
  have herr (x : Fin n → Bool) (i : Fin n) :
      ((univ.filter fun r => guess r (encode r x) i ≠ x i).card : ℝ) ≤ ε * Fintype.card R := by
    let l := wordPrefix x ++ [i]
    have hlen : l.length ≤ 2 * n := by
      have h := (univ.filter fun j => x j).card_le_univ
      simp only [Fintype.card_fin] at h
      simp only [l, List.length_append, wordPrefix, length_toList, List.length_singleton]
      have := i.isLt
      omega
    have hfail := hA l (List.append_ne_nil_of_right_ne_nil _ (by simp)) hlen
    rw [StreamingAlgorithm.failProb, div_lt_iff₀ (by exact_mod_cast Fintype.card_pos)] at hfail
    apply le_trans _ hfail.le
    refine Nat.cast_le.mpr (card_le_card ?_)
    intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr ⊢
    intro hgood
    apply hr
    have hout : A.output r l = A.out r (A.step r (encode r x) i) := by
      simp [l, StreamingAlgorithm.output, List.foldl_append, encode]
    rw [hout, show maxFreq l = _ from maxFreq_query x i] at hgood
    cases hi : x i <;> simp [hi, abs_lt] at hgood <;> simp [guess] <;> linarith
  let weight (r : R) (x : Fin n → Bool) :=
    ∏ i, if guess r (encode r x) i ≠ x i then ε else 1 - ε
  have hlower (x : Fin n → Bool) :
      Fintype.card R * exp (-(n : ℝ) * binEntropy ε) ≤ ∑ r, weight r x :=
    word_weight_bound x (fun r => guess r (encode r x)) hε hhalf (herr x)
  have hupper (r : R) : (∑ x, weight r x) ≤ (2 : ℝ) ^ s :=
    state_weight_bound (encode r) (guess r) hε hhalf
  have h := sum_le_sum (s := univ) (fun x _ => hlower x)
  rw [sum_comm] at h
  have hcard := h.trans (sum_le_sum (s := univ) fun r _ => hupper r)
  simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hcard
  rw [mul_left_comm] at hcard
  have hsize := (le_of_mul_le_mul_left hcard (by exact_mod_cast Fintype.card_pos))
  have hlog := log_le_log (by positivity) hsize
  rw [log_mul (by positivity) (exp_pos _).ne', log_pow, log_exp, log_pow] at hlog
  rw [div_mul_eq_mul_div, div_le_iff₀ htwo]
  linarith

end MathlibExt.Probability.Streaming
