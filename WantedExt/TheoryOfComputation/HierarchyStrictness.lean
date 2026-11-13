/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Decidability.ArithmeticalHierarchy

@[expose] public section

set_option autoImplicit false

namespace Cslib.HierarchyStrictnessWanted

/-- **The arithmetical hierarchy is strict**: at every level there is a
`Σₙ₊₁` set that is not `Σₙ` (diagonalisation against the `Σₙ` sets).
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I,
Theorem 4.6; Rogers, *Theory of Recursive Functions and Effective
Computability*, §13.5. -/
theorem_wanted hierarchy_strict :
  ∀ n : ℕ, ∃ P : ℕ → Prop,
    Cslib.Decidability.IsSigma (n + 1) P ∧ ¬ Cslib.Decidability.IsSigma n P

end Cslib.HierarchyStrictnessWanted
