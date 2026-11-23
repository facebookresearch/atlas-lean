/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.KatzBettiBounds
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public noncomputable section

/-!
# Katz's bound for the sum of compact Betti numbers of an affine scheme

Let `k` be algebraically closed, `N > 1`, and `V ⊆ 𝔸^N_k` the closed subscheme cut out by `r ≥ 1`
polynomials of degree at most `d`. For every prime `ℓ` invertible in `k`, the compactly supported
`ℓ`-adic cohomology groups of `V` are finite-dimensional and the sum of their dimensions is at most
`6 · 2^r · (3 + r d)^(N + 1)`.

Author of the mathematical source: Nicholas M. Katz.
Source: Sums of Betti numbers in arbitrary characteristic,
Corollary of Theorem 1, p. 4,
https://web.math.princeton.edu/~nmk/BettiSum14.pdf.
-/

namespace WantedExt.AlgebraicGeometry.KatzBettiBounds

open CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.ContinuousAdicCompactSupports
open MathlibExt.AlgebraicGeometry.KatzBettiBounds
open scoped BigOperators

universe u

/-- Katz's bound: the compact `ℓ`-adic cohomology of the affine scheme cut out by `F` is
finite-dimensional in each degree, and every finite sum of its dimensions is at most
`katzBound N r d`. -/
public theorem_wanted katz_affine_compact_betti_bound
    (N r d : ℕ) (hN : 1 < N) (hr : 0 < r)
    (k : Type u) [Field k] [IsAlgClosed k]
    (F : Fin r → MvPolynomial (Fin N) k) (degreeBound : ∀ j, (F j).totalDegree ≤ d)
    (ell : ℕ) [Fact ell.Prime] (ellInvertible : (ell : k) ≠ 0)
    (c : ClosedCompactification (affineVariety F)) :
    (∀ n : ℕ, Module.Finite ℚ_[ell] (CompactAdicCohomology ell c n)) ∧
      ∀ I : Finset ℕ,
        (∑ n ∈ I, Module.finrank ℚ_[ell] (CompactAdicCohomology ell c n)) ≤ katzBound N r d

end WantedExt.AlgebraicGeometry.KatzBettiBounds
