/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PixtonWeightings

@[expose] public section

/-!
# Polynomial regularization of Pixton graph sums

The remaining request is polynomiality for sufficiently large positive
modulus. Its constant term is uniquely determined by the completed
eventual-polynomial uniqueness lemma. No weighting formula at modulus
zero is asserted.

Source: Janda--Pandharipande--Pixton--Zvonkine, Double ramification cycles
on the moduli spaces of curves, Appendix A, polynomiality of weighting
sums. https://arxiv.org/abs/1602.04705
-/

namespace WantedExt.AlgebraicGeometry.PixtonWeightingPolynomiality

open _root_.MathlibExt.AlgebraicGeometry.UniversalCurveStability
open _root_.MathlibExt.AlgebraicGeometry.PixtonWeightings
open scoped BigOperators

/-- Pixton polynomiality, graph by graph, with true finite weighting domain. -/
public theorem_wanted pixton_polynomiality
    (g n : ℕ) (G : StableGraph g n) (a : Fin n → ℤ) (ha : ∑ i, a i = 0)
    (k : Fin G.edges → ℕ) :
    ∃ p : Polynomial ℚ, ∃ N : ℕ, 0 < N ∧
      ∀ (r : ℕ) (hr : 0 < r), N ≤ r →
        normalizedSum G a k r hr = p.eval (r : ℚ)

end WantedExt.AlgebraicGeometry.PixtonWeightingPolynomiality
