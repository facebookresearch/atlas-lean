/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# The Bhattacharyya coefficient

The Bhattacharyya coefficient `∑ x, √(p x * q x)` of two nonnegative vectors on a finite type.
This small module lets information-theoretic and quantum developments share the definition
without importing each other. The definition keeps the name
`MathlibExt.Quantum.ClassicalFuchsVanDeGraaf.bhattacharyyaCoeff`, which
`MathlibExt.Quantum.ClassicalFuchsVanDeGraaf` re-exports.
-/

@[expose] public section

namespace MathlibExt.Quantum.ClassicalFuchsVanDeGraaf

/-- The Bhattacharyya coefficient `∑ x, √(p x * q x)` of two nonnegative vectors on a finite
type: the unsquared classical (root) fidelity of two probability vectors. -/
noncomputable def bhattacharyyaCoeff {S : Type*} [Fintype S] (p q : S → ℝ) : ℝ :=
  ∑ x, Real.sqrt (p x * q x)

end MathlibExt.Quantum.ClassicalFuchsVanDeGraaf

end
