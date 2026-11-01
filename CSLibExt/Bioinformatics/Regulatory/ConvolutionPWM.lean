/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Fin.Basic

/-!
# A convolution filter with global max pooling is a position weight matrix scan

A first convolutional layer of a DNA-binding model (DeepBind, Alipanahi et al. 2015; the
architectures compared by Zeng et al. 2016) slides a filter `W : Fin w → σ → ℝ` (width `w`, one
row per letter of the alphabet `σ`) along the one-hot encoding of a sequence `x`, and a global max
pooling layer keeps the largest response. We prove that this computes a position weight matrix
(PWM) scan exactly.

Sequences are indexed by `ℕ` (`x : ℕ → σ`); a sequence of length `m + w` has the `m + 1`
windows starting at `0, …, m`, and only positions `< m + w` are read.

## Main results

* `conv_eq_pwmScore`: the response at window `i` is the PWM score
  `∑ k, W k (x (i + k))` of the window.
* `pwmScore_logOdds`: for a log-odds filter `W k b = log (P k b / q b)` the score is the log
  likelihood ratio of the window under the motif model `P` against the background `q`.
* `le_maxPool`, `exists_eq_maxPool`: max pooling returns the best PWM hit over all windows;
  `maxPool_relu`: with a bias and a ReLU before pooling, the output is
  `max (maxPool + β) 0`.
* `conv_shift`: translation equivariance, `conv W (x ∘ (· + 1)) i = conv W x (i + 1)`.
* `conv_rcFilter`, `maxPool_rcFilter`: the reverse-complement filter on `x` gives the responses
  of `W` on the reverse complement of `x`, in reverse order; `bothStrands_rcSeq`: the score that
  pools `W` and its reverse complement (scanning both strands of double-stranded DNA) is
  invariant under reverse complementing the sequence.

## References

* B. Alipanahi, A. Delong, M. T. Weirauch, B. J. Frey, *Predicting the sequence specificities of
  DNA- and RNA-binding proteins by deep learning*, Nat. Biotechnol. 33 (2015), 831–838.
* H. Zeng, M. D. Edwards, G. Liu, D. K. Gifford, *Convolutional neural network architectures for
  predicting DNA–protein binding*, Bioinformatics 32 (2016), i121–i127.
* G. D. Stormo, *DNA binding sites: representation and discovery*, Bioinformatics 16 (2000),
  16–23 (position weight matrices).
-/

@[expose] public section

namespace Cslib.Bioinformatics.Regulatory.ConvolutionPWM

open Finset Real

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {w : ℕ}

/-- The one-hot encoding of a letter: `oneHot a b = 1` if `b = a` and `0` otherwise. -/
def oneHot (a : σ) (b : σ) : ℝ := if a = b then 1 else 0

/-- The response of a convolution (cross-correlation) filter `W` of width `w` on the one-hot
encoded sequence `x` at the window starting at `i`:
`∑ k, ∑ b, W k b * oneHot (x (i + k)) b`. -/
def conv (W : Fin w → σ → ℝ) (x : ℕ → σ) (i : ℕ) : ℝ :=
  ∑ k : Fin w, ∑ b, W k b * oneHot (x (i + k)) b

/-- The position weight matrix score `∑ k, W k (u k)` of a word `u` of length `w`. -/
def pwmScore (W : Fin w → σ → ℝ) (u : Fin w → σ) : ℝ := ∑ k, W k (u k)

/-- The window of length `w` of `x` starting at `i`. -/
def window (x : ℕ → σ) (i : ℕ) : Fin w → σ := fun k => x (i + k)

/-- **The convolution response is the PWM score of the window.** -/
theorem conv_eq_pwmScore (W : Fin w → σ → ℝ) (x : ℕ → σ) (i : ℕ) :
    conv W x i = pwmScore W (window x i) := by
  simp [conv, pwmScore, window, oneHot]

omit [Fintype σ] [DecidableEq σ] in
/-- **A log-odds filter scores the log likelihood ratio**: if `W k b = log (P k b / q b)` with
positive motif probabilities `P` and background probabilities `q`, the PWM score of a word `u` is
`log (∏ k, P k (u k) / ∏ k, q (u k))`. -/
theorem pwmScore_logOdds {P : Fin w → σ → ℝ} {q : σ → ℝ} (hP : ∀ k b, 0 < P k b)
    (hq : ∀ b, 0 < q b) (u : Fin w → σ) :
    pwmScore (fun k b => log (P k b / q b)) u = log ((∏ k, P k (u k)) / ∏ k, q (u k)) := by
  rw [log_div (prod_pos fun k _ => hP k (u k)).ne' (prod_pos fun k _ => hq (u k)).ne',
    log_prod (fun k _ => (hP k (u k)).ne'), log_prod (fun k _ => (hq (u k)).ne'),
    pwmScore, ← sum_sub_distrib]
  exact sum_congr rfl fun k _ => log_div (hP k (u k)).ne' (hq (u k)).ne'

/-- **Global max pooling** over the `m + 1` windows of a sequence of length `m + w`. -/
def maxPool (W : Fin w → σ → ℝ) (x : ℕ → σ) (m : ℕ) : ℝ :=
  (range (m + 1)).sup' nonempty_range_add_one (conv W x)

/-- Every window's PWM score is at most the max-pooled output. -/
theorem le_maxPool (W : Fin w → σ → ℝ) (x : ℕ → σ) {m i : ℕ} (hi : i ≤ m) :
    pwmScore W (window x i) ≤ maxPool W x m := by
  rw [← conv_eq_pwmScore]
  exact le_sup' (conv W x) (mem_range.2 (Nat.lt_succ_of_le hi))

/-- **Max pooling returns the best PWM hit**: some window attains the max-pooled output. -/
theorem exists_eq_maxPool (W : Fin w → σ → ℝ) (x : ℕ → σ) (m : ℕ) :
    ∃ i ≤ m, pwmScore W (window x i) = maxPool W x m := by
  obtain ⟨i, hi, h⟩ := exists_mem_eq_sup' (nonempty_range_add_one (n := m)) (conv W x)
  exact ⟨i, Nat.lt_succ_iff.1 (mem_range.1 hi), by rw [← conv_eq_pwmScore, maxPool, h]⟩

/-- **Bias and ReLU commute with max pooling**: pooling `max (conv + β) 0` over the windows
gives `max (maxPool + β) 0`. -/
theorem maxPool_relu (W : Fin w → σ → ℝ) (x : ℕ → σ) (m : ℕ) (β : ℝ) :
    (range (m + 1)).sup' nonempty_range_add_one (fun i => max (conv W x i + β) 0) =
      max (maxPool W x m + β) 0 := by
  apply le_antisymm
  · refine sup'_le _ _ fun i hi => max_le_max ?_ le_rfl
    have := le_sup' (conv W x) hi
    unfold maxPool
    linarith
  · obtain ⟨i, hi, h⟩ := exists_mem_eq_sup' (nonempty_range_add_one (n := m)) (conv W x)
    rw [maxPool, h]
    exact le_sup' (fun i => max (conv W x i + β) 0) hi

/-- **Translation equivariance**: dropping the first letter shifts the responses by one
window. -/
theorem conv_shift (W : Fin w → σ → ℝ) (x : ℕ → σ) (i : ℕ) :
    conv W (fun j => x (j + 1)) i = conv W x (i + 1) := by
  simp only [conv]
  refine sum_congr rfl fun k _ => ?_
  rw [show i + (k : ℕ) + 1 = i + 1 + k by omega]

/-! ## Reverse complement -/

variable (comp : σ → σ)

/-- The reverse complement of the length-`L` prefix of `x`: position `j < L` holds the complement
of `x (L - 1 - j)`. -/
def rcSeq (L : ℕ) (x : ℕ → σ) (j : ℕ) : σ := comp (x (L - 1 - j))

/-- The reverse-complement filter: `rcFilter W k b = W (Fin.rev k) (comp b)`. -/
def rcFilter (W : Fin w → σ → ℝ) (k : Fin w) (b : σ) : ℝ := W k.rev (comp b)

/-- **The reverse-complement filter scans the other strand**: on a sequence of length `m + w`,
its response at window `i ≤ m` is the response of `W` on the reverse complement at window
`m - i`. -/
theorem conv_rcFilter (W : Fin w → σ → ℝ) (x : ℕ → σ) {m i : ℕ} (hi : i ≤ m) :
    conv (rcFilter comp W) x i = conv W (rcSeq comp (m + w) x) (m - i) := by
  rw [conv_eq_pwmScore, conv_eq_pwmScore]
  simp only [pwmScore, window, rcFilter, rcSeq]
  rw [← Equiv.sum_comp (Fin.revPerm (n := w))]
  refine sum_congr rfl fun k _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  congr 3
  omega

/-- **Max pooling the reverse-complement filter equals max pooling `W` on the reverse
complement.** -/
theorem maxPool_rcFilter (W : Fin w → σ → ℝ) (x : ℕ → σ) (m : ℕ) :
    maxPool (rcFilter comp W) x m = maxPool W (rcSeq comp (m + w) x) m := by
  apply le_antisymm
  · refine sup'_le _ _ fun i hi => ?_
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (mem_range.1 hi)
    rw [conv_rcFilter comp W x hi']
    exact le_sup' _ (mem_range.2 (by omega))
  · refine sup'_le _ _ fun i hi => ?_
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (mem_range.1 hi)
    have h := conv_rcFilter comp W x (Nat.sub_le m i)
    rw [Nat.sub_sub_self hi'] at h
    rw [← h]
    exact le_sup' _ (mem_range.2 (by omega))

/-- The responses only read the positions `< m + w` of a sequence of length `m + w`. -/
theorem maxPool_congr (W : Fin w → σ → ℝ) {x y : ℕ → σ} {m : ℕ}
    (hxy : ∀ j < m + w, x j = y j) : maxPool W x m = maxPool W y m := by
  unfold maxPool
  refine sup'_congr _ rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.1 (mem_range.1 hi)
  simp only [conv]
  refine sum_congr rfl fun k _ => ?_
  rw [hxy (i + k) (by omega)]

/-- The both-strand score: the larger of the max-pooled responses of `W` and of its reverse
complement. -/
def bothStrands (W : Fin w → σ → ℝ) (x : ℕ → σ) (m : ℕ) : ℝ :=
  max (maxPool W x m) (maxPool (rcFilter comp W) x m)

/-- **The both-strand score is invariant under reverse complementing the sequence**, for an
involutive complement. -/
theorem bothStrands_rcSeq (hcomp : Function.Involutive comp) (W : Fin w → σ → ℝ)
    (x : ℕ → σ) (m : ℕ) :
    bothStrands comp W (rcSeq comp (m + w) x) m = bothStrands comp W x m := by
  have hrr : maxPool W (rcSeq comp (m + w) (rcSeq comp (m + w) x)) m = maxPool W x m :=
    maxPool_congr W fun j hj => by
      simp only [rcSeq, hcomp _]
      congr 1
      omega
  unfold bothStrands
  rw [maxPool_rcFilter, maxPool_rcFilter, hrr, max_comm]

end Cslib.Bioinformatics.Regulatory.ConvolutionPWM
