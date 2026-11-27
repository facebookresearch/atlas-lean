/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.RussoInfluence

/-!
# Russo's formula in covariance form for arbitrary events

`StatMech.BeffaraDC.russoFormula` states the covariance form of Russo's formula for increasing
events, deduced from the pivotal form. The covariance form holds for every event on a finite
product space, increasing or not: differentiating the polynomial `p ↦ ℙ_p(A)` gives
`d/dp ℙ_p(A) = (p(1 - p))⁻¹ ∑_e Cov_p(1_A, ω_e)` for `0 < p < 1`, where
`Cov_p(1_A, ω_e) = ℙ_p(A ∩ {ω_e = 1}) - ℙ_p(ω_e = 1) ℙ_p(A)`. This is Proposition 2.6 of
H. Duminil-Copin, *Introduction to Bernoulli percolation*; Proposition 2.7 there (the pivotal form
for increasing events) is `StatMech.hasDerivAt_prob_eq_sum_pivotalProb`.

## Main results

* `StatMech.BeffaraDC.cov_openEdge_eq`: `Cov_p(1_A, ω_e) = p(1 - p)(S⁺_e - S⁻_e)`.
* `StatMech.BeffaraDC.hasDerivAt_prob_eq_sum_cov`: the formula for an arbitrary event.

## References

* H. Duminil-Copin, *Introduction to Bernoulli percolation*, lecture notes, IHÉS (version of
  7 October 2018), Proposition 2.6 and equation (2.2).
* G. A. Margulis, *Probabilistic characteristics of graphs with large connectivity*, Problemy
  Peredači Informacii 10 (1974), 101–108.
* L. Russo, *On the critical percolation probabilities*, Z. Wahrsch. Verw. Gebiete 56 (1981),
  229–237.
-/

@[expose] public section

namespace StatMech

namespace BeffaraDC

open ConfigSpace Function Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **Covariance with one coordinate, for an arbitrary event.** For every event `A` (not
necessarily increasing), the covariance of `1_A` with the state of the coordinate `e` is
`p(1 - p)` times the difference between the weights of `A` with `e` open and with `e` closed,
computed with the product of the weights of the other coordinates. -/
theorem cov_openEdge_eq (p : ℝ) (A : Set (ConfigSpace E)) (e : E) :
    prob p (A ∩ openEdge e) - prob p (openEdge e) * prob p A
      = p * (1 - p) *
        ((∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω *
            (if ω e then (1 : ℝ) else 0))
          - ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω *
            (if ω e then (0 : ℝ) else 1)) := by
  rw [prob_inter_openEdge p A e, prob_openEdge p e, prob_decompose p A e]
  ring

/-- **Russo's formula, covariance form, for an arbitrary event** (H. Duminil-Copin, *Introduction
to Bernoulli percolation*, lecture notes, 2018, Proposition 2.6; Margulis 1974, Russo 1981). For a
finite set of coordinates `E`, every event `A ⊆ {0, 1}^E` and every `p ∉ {0, 1}`,
`d/dp ℙ_p(A) = (p(1 - p))⁻¹ ∑_e (ℙ_p(A ∩ {ω_e = 1}) - ℙ_p(ω_e = 1) ℙ_p(A))`.
Unlike `StatMech.BeffaraDC.russoFormula`, `A` need not be increasing. -/
theorem hasDerivAt_prob_eq_sum_cov (A : Set (ConfigSpace E)) {p : ℝ} (hp0 : p ≠ 0)
    (hp1 : p ≠ 1) :
    HasDerivAt (fun p => prob p A)
      ((1 / (p * (1 - p)))
        * ∑ e, (prob p (A ∩ openEdge e) - prob p (openEdge e) * prob p A)) p := by
  have hne : p * (1 - p) ≠ 0 := mul_ne_zero hp0 (by intro h; exact hp1 (by linarith))
  convert hasDerivAt_prob A p using 1
  have hsum : ∀ e, prob p (A ∩ openEdge e) - prob p (openEdge e) * prob p A
      = p * (1 - p) * ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω *
          (weightOff p e ω * (if ω e then (1 : ℝ) else -1)) := by
    intro e
    rw [cov_openEdge_eq p A e, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : ω e <;> simp [h]
  rw [Finset.sum_congr rfl (fun e _ => hsum e), ← Finset.mul_sum, ← mul_assoc, one_div,
    inv_mul_cancel₀ hne, one_mul, Finset.sum_comm]
  simp_rw [Finset.mul_sum]

end BeffaraDC

end StatMech
