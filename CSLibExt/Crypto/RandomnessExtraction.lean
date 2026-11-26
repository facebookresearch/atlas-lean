/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Security.QuantitativeInformationFlow

/-!
# Min-entropy and collisions of a finite source

The best fixed guess succeeds with probability `vulnerability p`. Its negative binary logarithm
is the min-entropy. In contrast, a second independent draw guesses each outcome with its own
probability, so its chance of matching the first draw is the sum of the squared masses.

## References

* D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, v0.4, §8.10.4, p. 329
  (guessing probability).
* S. Vadhan, *Pseudorandomness*, Definition 4.7, p. 85 (independent collisions and the sum of
  squares); Definitions 6.7 and 6.9, pp. 171, 173 (bits and point-mass thresholds).
-/

@[expose] public section

namespace Cslib.Crypto.RandomnessExtraction

open Cslib.Security.QuantitativeInformationFlow

variable {α : Type*}

/-- **Min-entropy in bits.** For a probability mass function $p$ on a nonempty finite set,
let $\gamma=\max_x p(x)$ be its guessing probability. Its min-entropy is
$H_\infty(p)=-\log_2\gamma$. -/
noncomputable def minEntropy [Fintype α] [Nonempty α] (p : PMF α) : ℝ :=
  -Real.logb 2 (vulnerability p)

/-- **Point-mass threshold for min-entropy.** For a probability mass function $p$ on a nonempty
finite set and any real $k$, $H_\infty(p)\ge k$ if and only if $p(x)\le 2^{-k}$ for every
outcome $x$, including those of mass zero. -/
theorem le_minEntropy_iff [Fintype α] [Nonempty α] (p : PMF α) (k : ℝ) :
    k ≤ minEntropy p ↔ ∀ x, (p x).toReal ≤ (2 : ℝ) ^ (-k) := by
  obtain ⟨a, ha⟩ := p.support_nonempty
  have hpos : 0 < vulnerability p :=
    (ENNReal.toReal_pos ((p.mem_support_iff a).mp ha) (p.apply_ne_top a)).trans_le
      (Finset.le_sup' (fun x => (p x).toReal) (Finset.mem_univ a))
  rw [minEntropy, ← neg_le_neg_iff, neg_neg, Real.logb_le_iff_le_rpow (by norm_num) hpos,
    vulnerability]
  simp only [Finset.sup'_le_iff, Finset.mem_univ, forall_const]

/-- **Collision probability.** Independently draw two outcomes with probability mass function $p$.
Their collision probability is the probability of the diagonal event: the two outcomes are equal. -/
noncomputable def collisionProbability (p : PMF α) : ℝ :=
  ((p.bind fun x => p.map (Prod.mk x)).toOuterMeasure (Set.diagonal α)).toReal

/-- **Collision probability as a sum of squares.** For a probability mass function $p$ on a
finite set, the probability that two independent draws agree is $\sum_x p(x)^2$. -/
theorem collisionProbability_eq_sum_sq [Fintype α] (p : PMF α) :
    collisionProbability p = ∑ x, (p x).toReal ^ 2 := by
  have hfiber (x : α) : Prod.mk x ⁻¹' Set.diagonal α = {x} := by
    ext y
    exact eq_comm
  simp only [collisionProbability, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply,
    hfiber, PMF.toOuterMeasure_apply_singleton, tsum_fintype, ← sq]
  rw [ENNReal.toReal_sum fun x _ => ENNReal.pow_ne_top (p.apply_ne_top x)]
  simp only [ENNReal.toReal_pow]

end Cslib.Crypto.RandomnessExtraction
