/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.IAAutomorphismsLinearKourovka15Problem10
import Mathlib.Algebra.Field.ZMod

namespace MathlibExtTest.GroupTheory.IAAutomorphismsLinearKourovka15Problem10

open MathlibExt.GroupTheory.IAAutomorphismsLinearKourovka15Problem10Wanted

example (g : FreeGroup (Fin 3)) : MulAut.conj g ∈ iaAut 3 := by
  change ∀ x, Group.Abelianization.of (MulAut.conj g x) = Group.Abelianization.of x
  intro x
  simp

example (m : ℕ) (ρ : iaAut 3 →* Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) :
    ¬ Function.Injective ρ :=
  fun hρ => iaAutLinear_refuted ⟨3, le_rfl, ZMod 2, inferInstance, m, ρ, hρ⟩

end MathlibExtTest.GroupTheory.IAAutomorphismsLinearKourovka15Problem10
