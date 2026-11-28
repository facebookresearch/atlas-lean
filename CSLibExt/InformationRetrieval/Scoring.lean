/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Monotone.Basic

import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# BM25 term scoring

This file formalizes one BM25 term score with an already chosen nonnegative
inverse-document-frequency weight. The length-normalization factor is carried
explicitly, and the saturation and monotonicity theorems assume that factor is
positive. Monotonicity is stated on nonnegative term frequencies, the actual
BM25 domain.

The definitions themselves are total algebraic extensions to arbitrary real
parameters (Lean totalizes division by zero). They are intended as BM25 scores
only on the standard domain: average document length positive, document
length and term frequency nonnegative, `k1 > 0`, `b ∈ [0, 1]`, and the
resulting length-normalization factor positive. Outside that domain, values
such as those obtained from `avgLen = 0` are artifacts of the total extension,
not BM25 scores; the BM25-facing theorems below state the needed positivity
and domain hypotheses explicitly.

## References

* Stephen Robertson and Hugo Zaragoza, "The Probabilistic Relevance
  Framework: BM25 and Beyond" (2009), for the BM25 term-weight formula with
  saturation parameter `k1`, length-normalization parameter `b`, document
  length, and average document length. This file does not formalize an IDF
  estimator: `idf` is an input, and the theorems assume the common
  nonnegative-IDF convention `0 ≤ idf`. In particular, the raw Robertson IDF
  variant, which can be negative for terms occurring in more than half the
  documents, is outside the stated convention.

## Main declarations

* `bm25LengthNorm`: document-length normalization factor.
* `bm25TermScore`: one-term BM25 score.
* `bm25TermScore_zero_tf`: zero term frequency scores zero.
* `bm25TermScore_nonneg_le_saturation`: nonnegativity and saturation bound.
* `bm25TermScore_mono_tf`: monotonicity on nonnegative term frequencies.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.InformationRetrieval

/-- BM25 document-length normalization factor, as a total real-algebra
extension.

With length-normalization parameter `b`, document length `docLen`, and average
document length `avgLen`, this is `(1 - b) + b * docLen / avgLen` on the
standard BM25 domain (`avgLen > 0`, `b ∈ [0, 1]`). Outside that domain the
value is still the displayed totalized real expression, not a BM25 quantity. -/
noncomputable def bm25LengthNorm (b docLen avgLen : ℝ) : ℝ :=
  (1 - b) + b * (docLen / avgLen)

/-- One BM25 term score under a nonnegative-IDF convention, as a total
real-algebra extension.

`idf` is the already chosen nonnegative inverse-document-frequency weight;
this definition does not use the raw Robertson IDF variant, which can be
negative. `tf` is term frequency and `k1` is the BM25 saturation parameter.
The displayed formula is the BM25 score on the standard domain described in
the module documentation; at parameter values making a denominator zero it
uses Lean's totalized division. -/
noncomputable def bm25TermScore (idf tf k1 b docLen avgLen : ℝ) : ℝ :=
  idf * (tf * (k1 + 1) / (tf + k1 * bm25LengthNorm b docLen avgLen))

/-- A BM25 term score at zero term frequency is zero. -/
theorem bm25TermScore_zero_tf (idf k1 b docLen avgLen : ℝ) :
    bm25TermScore idf 0 k1 b docLen avgLen = 0 := by
  simp [bm25TermScore]

/-- With `idf ≥ 0`, `tf ≥ 0`, `k1 > 0` and a positive length-normalization factor, a BM25 term
score is nonnegative and at most `idf * (k1 + 1)`. -/
theorem bm25TermScore_nonneg_le_saturation {idf tf k1 b docLen avgLen : ℝ}
    (hidf : 0 ≤ idf) (htf : 0 ≤ tf) (hk1 : 0 < k1)
    (hnorm : 0 < bm25LengthNorm b docLen avgLen) :
    0 ≤ bm25TermScore idf tf k1 b docLen avgLen ∧
      bm25TermScore idf tf k1 b docLen avgLen ≤ idf * (k1 + 1) := by
  have hC : 0 < k1 * bm25LengthNorm b docLen avgLen := mul_pos hk1 hnorm
  have hden : 0 < tf + k1 * bm25LengthNorm b docLen avgLen :=
    add_pos_of_nonneg_of_pos htf hC
  have hk1' : 0 ≤ k1 + 1 := by linarith
  constructor
  · unfold bm25TermScore
    exact mul_nonneg hidf (div_nonneg (mul_nonneg htf hk1') (le_of_lt hden))
  · unfold bm25TermScore
    apply mul_le_mul_of_nonneg_left _ hidf
    rw [div_le_iff₀ hden]
    have hnn : 0 ≤ (k1 + 1) * (k1 * bm25LengthNorm b docLen avgLen) :=
      mul_nonneg hk1' (le_of_lt hC)
    calc tf * (k1 + 1) = (k1 + 1) * tf := mul_comm _ _
      _ ≤ (k1 + 1) * tf + (k1 + 1) * (k1 * bm25LengthNorm b docLen avgLen) :=
        le_add_of_nonneg_right hnn
      _ = (k1 + 1) * (tf + k1 * bm25LengthNorm b docLen avgLen) := by ring

/-- With a nonnegative IDF, `k1 > 0` and a positive length-normalization factor, a BM25 term
score is monotone on nonnegative term frequencies. -/
theorem bm25TermScore_mono_tf {idf k1 b docLen avgLen : ℝ}
    (hidf : 0 ≤ idf) (hk1 : 0 < k1)
    (hnorm : 0 < bm25LengthNorm b docLen avgLen) :
    MonotoneOn (fun tf => bm25TermScore idf tf k1 b docLen avgLen) (Set.Ici 0) := by
  have hC : 0 < k1 * bm25LengthNorm b docLen avgLen := mul_pos hk1 hnorm
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := Set.mem_Ici.mp hx
  have hy0 : 0 ≤ y := Set.mem_Ici.mp hy
  have hdx : 0 < x + k1 * bm25LengthNorm b docLen avgLen :=
    add_pos_of_nonneg_of_pos hx0 hC
  have hdy : 0 < y + k1 * bm25LengthNorm b docLen avgLen :=
    add_pos_of_nonneg_of_pos hy0 hC
  unfold bm25TermScore
  apply mul_le_mul_of_nonneg_left _ hidf
  rw [div_le_div_iff₀ hdx hdy]
  have hk1' : 0 ≤ k1 + 1 := by linarith
  have hprod : 0 ≤ (k1 + 1) * (k1 * bm25LengthNorm b docLen avgLen) * (y - x) :=
    mul_nonneg (mul_nonneg hk1' (le_of_lt hC)) (sub_nonneg.mpr hxy)
  linear_combination hprod

end Cslib.InformationRetrieval
