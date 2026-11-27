/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SpoofLehmerFactorizationLehmerEquationSolutionsFinite

/-!
# Tests for finiteness of solutions of the Lehmer equation

The solutions with two variables and multiplier two form a finite set.
-/

namespace MathlibExtTest.NumberTheory.SpoofLehmerFactorizationLehmerEquationSolutionsFinite

example : {x : Fin 2 → ℕ | (∀ i, 2 ≤ x i) ∧
    (2 : ℤ) * ∏ i, ((x i : ℤ) - 1) = ∏ i, (x i : ℤ) - 1}.Finite := by
  have h := MetaMathlibExt.lehmerEquation_solutions_finite 2 (by decide)
  apply (h.image Prod.snd).subset
  intro x hx
  exact ⟨(2, x), ⟨show (0 : ℤ) < 2 from by decide, hx⟩, rfl⟩

end MathlibExtTest.NumberTheory.SpoofLehmerFactorizationLehmerEquationSolutionsFinite
