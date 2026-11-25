/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.Convex.TotalDualIntegrality
public import Mathlib.Analysis.Convex.Extreme

/-!
# The Edmonds-Giles theorem (wanted)

A totally dual integral system with integral right-hand side defines an integral polyhedron.

Source: M. X. Goemans, MIT 18.438 Advanced Combinatorial Optimization, Lecture 6 (2009),
Theorem 2; J. Edmonds and R. Giles, "A min-max relation for submodular functions on graphs",
Ann. Discrete Math. 1 (1977), 185-204.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.EdmondsGilesWanted

open MathlibExt.Analysis.Convex.TotalDualIntegrality Matrix

/-- **Edmonds-Giles theorem.** If `A x ≤ b` is a TDI system with rational `A` and integral `b`,
then every extreme point of the polyhedron `{x : A x ≤ b}` is integral (Goemans, MIT 18.438,
Lecture 6, 2009, Theorem 2, where "integral" means that all extreme points are integral). -/
theorem_wanted extremePoints_integral_of_isTDI {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (hA : ∀ i j, ∃ q : ℚ, A i j = q) (hb : ∀ i, ∃ z : ℤ, b i = z)
    (hTDI : IsTDI A b) :
    ∀ x ∈ Set.extremePoints ℝ {x : Fin n → ℝ | A *ᵥ x ≤ b}, ∀ j, ∃ z : ℤ, x j = z

end MathlibExt.Analysis.Convex.EdmondsGilesWanted
