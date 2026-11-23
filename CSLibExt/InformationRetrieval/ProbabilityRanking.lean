/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.InformationRetrieval.DiscountedGain
public import CSLibExt.InformationRetrieval.PrecisionAt
public import Mathlib.Data.Fintype.Pi

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Probability ranking principle for expected precision

The probability ranking principle (Robertson) says that ranking documents by
decreasing probability of relevance is optimal. This file proves its
fixed-cutoff, expected-precision form: for each cutoff `k`, a ranked prefix
sorted by marginal relevance maximizes expected precision at `k` among
injective ranked prefixes.

For a finite candidate universe `Fin N`, a joint relevance law is modeled by
real weights `μ` on full relevance vectors `Fin N → Bool`. The marginal
relevance of a document is the total weight of relevance vectors in which
that document is relevant. Expected precision at a cutoff is the `μ`-weighted
sum of `precisionAt` over those relevance vectors. When `μ` is a probability
mass function, these are the marginal relevance probabilities and the
expectation of `precisionAt`.

The main identity is finite linearity: expected precision is the average of
the selected marginal relevances. No independence between documents is
assumed, and the weights need not be nonnegative. Therefore a prefix sorted by
marginal relevance maximizes expected precision among injective ranked
prefixes.

## Main declarations

* `relevanceMarginal`: marginal relevance under joint relevance weights.
* `expectedPrecisionAt`: expected precision under a joint law.
* `expectedPrecisionAt_eq_average_marginals`: expected precision is the
  average selected marginal.
* `expectedPrecisionAt_le_sortedPrefix`: the marginal-sorted prefix is optimal.
* `exists_sorted_expectedPrecisionAt`: an optimal marginal-sorted ranking exists.

## References

* S. E. Robertson, *The probability ranking principle in IR*, Journal of
  Documentation 33(4), 1977.
* C. D. Manning, P. Raghavan and H. Schütze, *Introduction to Information
  Retrieval*, Cambridge University Press, 2008, Section 11.2.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.InformationRetrieval

/-- The marginal relevance of document `i` under finite joint relevance
weights `μ`: the total weight of the relevance vectors with `rel i = true`.

`μ rel` is the weight of the full relevance vector `rel : Fin N → Bool`.
No independence assumption is made: `μ` may be any joint law. When `μ` is a
probability mass function, this is the probability that `i` is relevant. -/
noncomputable def relevanceMarginal {N : ℕ} (μ : (Fin N → Bool) → ℝ)
    (i : Fin N) : ℝ :=
  ∑ rel, μ rel * (if rel i then 1 else 0)

/-- Expected precision at cutoff `k` under a finite joint relevance law `μ`.

For a relevance vector `rel`, the relevance predicate is `fun i => rel i = true`.
When `μ` is nonnegative with total weight `1`, this is the expectation of
`precisionAt` under `μ`; the identity below is just finite linearity and uses
no independence. -/
noncomputable def expectedPrecisionAt {N k : ℕ} (μ : (Fin N → Bool) → ℝ)
    (r : Fin k → Fin N) : ℝ :=
  ∑ rel, μ rel * precisionAt (fun i => rel i = true) r

/-- Expected precision is the average of the selected marginal relevances. This
is linearity of expectation for a finite joint law; no independence between
documents is assumed. -/
theorem expectedPrecisionAt_eq_average_marginals {N k : ℕ}
    (μ : (Fin N → Bool) → ℝ) (r : Fin k → Fin N) (hk : k ≠ 0) :
    expectedPrecisionAt μ r =
      (∑ j, relevanceMarginal μ (r j)) / (k : ℝ) := by
  have hcard : ∀ rel : Fin N → Bool,
      ((((Finset.univ.filter fun i => rel (r i) = true).card : ℕ)) : ℝ)
        = ∑ j, (if rel (r j) = true then (1 : ℝ) else 0) := by
    intro rel
    exact (Finset.sum_boole _ _).symm
  unfold expectedPrecisionAt relevanceMarginal precisionAt
  simp only [hk, ite_false]
  have hterm : ∀ rel : Fin N → Bool,
      μ rel * (((((Finset.univ.filter fun i => rel (r i) = true).card : ℕ)) : ℝ) / (k : ℝ))
        = (∑ j, μ rel * (if rel (r j) then (1 : ℝ) else 0)) / (k : ℝ) := by
    intro rel
    rw [hcard rel, ← mul_div_assoc, Finset.mul_sum]
  have hLHS : (∑ rel : Fin N → Bool, μ rel *
      (((((Finset.univ.filter fun i => rel (r i) = true).card : ℕ)) : ℝ) / (k : ℝ)))
      = ∑ rel : Fin N → Bool,
        (∑ j, μ rel * (if rel (r j) then (1 : ℝ) else 0)) / (k : ℝ) :=
    Finset.sum_congr rfl (fun rel _ => hterm rel)
  rw [hLHS, ← Finset.sum_div, Finset.sum_comm]

/-- Probability ranking principle for expected precision at a fixed cutoff: for
any real joint relevance weights, every injective ranked prefix has expected
precision at most the sorted-by-marginal prefix. Neither independence nor
nonnegativity of the weights is used. -/
theorem expectedPrecisionAt_le_sortedPrefix {N k : ℕ} (hk : k ≤ N)
    {μ : (Fin N → Bool) → ℝ}
    {r : Fin k → Fin N} (hr : Function.Injective r)
    (s : {s : Equiv.Perm (Fin N) // Antitone (relevanceMarginal μ ∘ s)}) :
    expectedPrecisionAt μ r ≤
      expectedPrecisionAt μ (fun i => s.1 (Fin.castLE hk i)) := by
  by_cases hk0 : k = 0
  · subst hk0
    have h0 : ∀ r' : Fin 0 → Fin N, expectedPrecisionAt μ r' = 0 := by
      intro r'
      simp [expectedPrecisionAt, precisionAt]
    simp [h0]
  · rw [expectedPrecisionAt_eq_average_marginals μ r hk0,
        expectedPrecisionAt_eq_average_marginals μ _ hk0]
    have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
    rw [div_le_div_iff_of_pos_right hkpos]
    have hdcg := dcgAt_le_idealDCGAt hk (fun _ => zero_le_one) antitone_const hr s.2
    simpa [dcgAt, idealDCGAt] using hdcg

/-- There is a marginal-sorted ranking whose prefix maximizes expected
precision among injective ranked prefixes. -/
theorem exists_sorted_expectedPrecisionAt {N k : ℕ} (hk : k ≤ N)
    (μ : (Fin N → Bool) → ℝ) :
    ∃ s : {s : Equiv.Perm (Fin N) // Antitone (relevanceMarginal μ ∘ s)},
      ∀ r : Fin k → Fin N, Function.Injective r →
        expectedPrecisionAt μ r ≤
          expectedPrecisionAt μ (fun i => s.1 (Fin.castLE hk i)) := by
  obtain ⟨s, hs⟩ := exists_sortedPerm (relevanceMarginal μ)
  exact ⟨⟨s, hs⟩, fun r hr => expectedPrecisionAt_le_sortedPrefix hk hr ⟨s, hs⟩⟩

end Cslib.InformationRetrieval
