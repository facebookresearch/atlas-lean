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
# A uniform equation-degree bound for genuine adic compact Betti numbers

Authors: Nicholas M. Katz.
Source: Sums of Betti numbers in arbitrary characteristic,
Corollary of Theorem 1, p. 4,
https://web.math.princeton.edu/~nmk/BettiSum14.pdf.

The scope is the displayed N>1, r>=1 affine closed-scheme statement,
with ell invertible. Compactification and finite-dimensionality are
actual geometric/canonical class data. The conclusion bounds every
finite sum of actual cohomology ranks, so it uses no guessed truncation
or fake total-Betti carrier. General adic finiteness/trace are existing
toolbox, and are not re-requested here.
-/

namespace WantedExt.AlgebraicGeometry.KatzBettiBounds

open CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.ContinuousAdicCompactSupports
open MathlibExt.AlgebraicGeometry.KatzBettiBounds
open scoped BigOperators

universe u

/-- Katz's explicit compact-Betti estimate on the actual closed affine zero scheme. -/
public theorem_wanted katz_affine_compact_betti_bound
    (N r d : ℕ) (hN : 1 < N) (hr : 0 < r)
    (k : Type u) [Field k] [IsAlgClosed k]
    (F : Fin r → MvPolynomial (Fin N) k) (degreeBound : ∀ j, (F j).totalDegree ≤ d)
    (ell : ℕ) [Fact ell.Prime] (ellInvertible : (ell : k) ≠ 0)
    (c : ClosedCompactification (affineVariety F))
    [∀ n : ℕ, Module.Finite ℚ_[ell] (CompactAdicCohomology ell c n)] (I : Finset ℕ) :
    (∑ n ∈ I, Module.finrank ℚ_[ell] (CompactAdicCohomology ell c n)) ≤ katzBound N r d

end WantedExt.AlgebraicGeometry.KatzBettiBounds
