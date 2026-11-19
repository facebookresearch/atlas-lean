/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.GameTheory.MeanFieldEquilibrium

/-!
# Wanted: existence of mean field equilibria on a finite state space

Existence of a mean field equilibrium for a Lipschitz cost on a finite state space, obtained in
Lions' lectures as a limit of symmetric mixed Nash equilibria of `N`-player games. The proof
needs Nash's theorem (Kakutani's or Brouwer's fixed point theorem), which pinned Mathlib does not
provide.

## References

* P. Cardaliaguet, *Notes on Mean Field Games (from P.-L. Lions' lectures at Collège de France)*,
  version of 27 September 2013, §2.3 (Theorem 2.7, Remark 2.8).
-/

@[expose] public section

namespace MathlibExt.GameTheory.MeanFieldEquilibriumWanted

open MathlibExt.GameTheory.MeanFieldEquilibrium

/-- **Existence of mean field equilibria** (Lasry–Lions; Cardaliaguet, *Notes on Mean Field
Games*, Theorem 2.7 and Remark 2.8, for a finite state space `Q`). If `Q` is a nonempty finite
set and the cost is Lipschitz in the population distribution, `|F m₁ y - F m₂ y| ≤ K ∑ |m₁ - m₂|`
for probability vectors `m₁, m₂` (on a finite set the Kantorovich–Rubinstein distance `d₁` of the
source is equivalent to the `ℓ¹` distance), then a mean field equilibrium exists. -/
theorem_wanted exists_isMeanFieldEquilibrium {Q : Type*} [Fintype Q] [Nonempty Q]
    (F : (Q → ℝ) → Q → ℝ) (K : ℝ)
    (hF : ∀ m₁ m₂ : Q → ℝ, ((∀ y, 0 ≤ m₁ y) ∧ ∑ y, m₁ y = 1) →
      ((∀ y, 0 ≤ m₂ y) ∧ ∑ y, m₂ y = 1) → ∀ y, |F m₁ y - F m₂ y| ≤ K * ∑ z, |m₁ z - m₂ z|) :
    ∃ m : Q → ℝ, IsMeanFieldEquilibrium F m

end MathlibExt.GameTheory.MeanFieldEquilibriumWanted
