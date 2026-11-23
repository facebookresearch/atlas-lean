/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.CorrelationInequalities.Reimer

/-!
# Reimer's inequality

Reimer's inequality (the van den Berg–Kesten conjecture): for every product probability measure
on `{0, 1}^n` and all events `A`, `B`, the probability that `A` and `B` occur disjointly is at
most `P(A) P(B)`. The BK inequality is the case of two increasing events.

The ported library states this as the proposition `StatMech.ReimerWprobCore` and proves only
its reductions and monotone cases (`StatMech.reimer_inequality_of_core`,
`StatMech.bk_inequality_decreasing`). A proof of `reimer_inequality` below discharges
`ReimerWprobCore` (`reimer_wprob_core`), and `StatMech.reimer_inequality_of_core` then gives the
inequality for every Bernoulli product measure on a finite set.

## Main statements

* `reimer_inequality`: `wprob φ (A □ B) ≤ wprob φ A * wprob φ B` for every product probability
  weight `φ` on `Fin n` and all events `A`, `B`.
* `reimer_wprob_core`: the same statement in the form `StatMech.ReimerWprobCore`.

## References

* D. Reimer, *Proof of the van den Berg–Kesten conjecture*, Combin. Probab. Comput. 9 (2000),
  27–32.
* J. van den Berg, H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985), 556–569.
-/

@[expose] public section

namespace MathlibExt.Probability.ReimerInequalityWanted

open StatMech

/-- **Reimer's inequality** (van den Berg–Kesten conjecture). For every `n`, every product
probability weight `φ` on `{0, 1}^n` (`φ i b ≥ 0`, `φ i false + φ i true = 1`) and all events
`A`, `B ⊆ {0, 1}^n`, `P(A □ B) ≤ P(A) P(B)`, where `A □ B` is the event that `A` and `B` occur on
disjoint sets of coordinates.

Source: D. Reimer, *Proof of the van den Berg–Kesten conjecture*, Combin. Probab. Comput. 9
(2000), 27–32. -/
public theorem_wanted reimer_inequality :
    ∀ (n : ℕ) (φ : Fin n → Bool → ℝ),
      (∀ i b, 0 ≤ φ i b) → (∀ i, φ i false + φ i true = 1) →
      ∀ (A B : Set (ConfigSpace (Fin n))),
        wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B

/-- Reimer's inequality in the form of the ported hypothesis `StatMech.ReimerWprobCore`
(definitionally `reimer_inequality`).

Source: D. Reimer, *Proof of the van den Berg–Kesten conjecture*, Combin. Probab. Comput. 9
(2000), 27–32. -/
public theorem_wanted reimer_wprob_core : ReimerWprobCore

end MathlibExt.Probability.ReimerInequalityWanted
