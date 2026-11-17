/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Sign.Basic

/-!
# Certified enclosures for accumulated log-likelihoods

If each computed site log-likelihood `lhat i` differs from the exact value
`l i` by at most a supplied bound `δ i`, and an accumulated value `S` differs
from the exact sum of the computed values by at most `E`, then `S` differs
from the exact total by at most `E + ∑ i, δ i`.

Consequently, if two computed totals enclose their exact log-likelihoods and
their difference is larger than the sum of the enclosure widths, then the
exact log-likelihood difference has the same sign as the computed difference.

These are the elementary real-number steps. The instantiation of `E` by the
rounded recursive-summation bound is in
`CSLibExt.Bioinformatics.PopulationGenetics.FloatLoglik`, because the rounded
sum is defined in `CSLibExt`.

## Main results

* `abs_sub_sum_le_enclosure`: the enclosure of one total.
* `sign_sub_eq_of_enclosure`: the certified sign of a likelihood difference.

## References

* N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
  SIAM (2002), ch. 2.
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Inference.Numerics

/-- **Certified enclosure of a total log-likelihood.** The site log-likelihoods `l i` are
evaluated with per-site errors `|lhat i - l i| ≤ δ i` (supplied separately), and the computed
values are accumulated into `S` with `|S - ∑ i, lhat i| ≤ E` (for rounded recursive summation,
`E = ((1 + u) ^ n - 1) * ∑ i, |lhat i|`). Then `S` lies within `E + ∑ i, δ i` of the exact
total `∑ i, l i`. -/
theorem abs_sub_sum_le_enclosure {n : ℕ} (l lhat δ : Fin n → ℝ) (S E : ℝ)
    (hsite : ∀ i, |lhat i - l i| ≤ δ i) (hsum : |S - ∑ i, lhat i| ≤ E) :
    |S - ∑ i, l i| ≤ E + ∑ i, δ i := by
  have hdecomp : S - ∑ i, l i = (S - ∑ i, lhat i) + (∑ i, (lhat i - l i)) := by
    rw [Finset.sum_sub_distrib]
    grind
  calc |S - ∑ i, l i|
      = |(S - ∑ i, lhat i) + (∑ i, (lhat i - l i))| := by rw [hdecomp]
    _ ≤ |S - ∑ i, lhat i| + |∑ i, (lhat i - l i)| := abs_add_le _ _
    _ ≤ E + ∑ i, |lhat i - l i| := add_le_add hsum (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ E + ∑ i, δ i := add_le_add le_rfl (Finset.sum_le_sum (fun i _ => hsite i))

/-- **Certified likelihood comparison.** If the computed totals `S₁`, `S₂` enclose the exact
log-likelihoods `L₁`, `L₂` within `w₁`, `w₂`, and the computed difference exceeds the sum of the
enclosure widths, `w₁ + w₂ < |S₁ - S₂|`, then the exact difference has the computed sign. -/
theorem sign_sub_eq_of_enclosure (S₁ S₂ L₁ L₂ w₁ w₂ : ℝ)
    (h₁ : |S₁ - L₁| ≤ w₁) (h₂ : |S₂ - L₂| ≤ w₂) (hgap : w₁ + w₂ < |S₁ - S₂|) :
    SignType.sign (L₁ - L₂) = SignType.sign (S₁ - S₂) := by
  have hbound : |(L₁ - L₂) - (S₁ - S₂)| ≤ w₁ + w₂ := by grind
  have hlt : |(L₁ - L₂) - (S₁ - S₂)| < |S₁ - S₂| := lt_of_le_of_lt hbound hgap
  cases hS : lt_trichotomy (S₁ - S₂) 0 with
  | inl hneg =>
    have hLneg : L₁ - L₂ < 0 := by
      by_cases h : L₁ - L₂ < 0
      · exact h
      · have hle : 0 ≤ L₁ - L₂ := le_of_not_gt h
        have hfalse : False := by grind
        exact False.elim hfalse
    rw [sign_neg hLneg, sign_neg hneg]
  | inr h2 =>
    cases h2 with
    | inl heq =>
      have hfalse : False := by grind
      exact False.elim hfalse
    | inr hpos =>
      have hLpos : 0 < L₁ - L₂ := by
        by_cases h : 0 < L₁ - L₂
        · exact h
        · have hle : L₁ - L₂ ≤ 0 := le_of_not_gt h
          have hfalse : False := by grind
          exact False.elim hfalse
      rw [sign_pos hLpos, sign_pos hpos]

end MathlibExt.Biology.PopulationGenetics.Inference.Numerics
