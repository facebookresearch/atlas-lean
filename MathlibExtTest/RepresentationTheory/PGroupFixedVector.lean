/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RepresentationTheory.PGroupFixedVector

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Common

namespace MathlibExtTest.RepresentationTheory.PGroupFixedVector

/-- Consumer with the original binders, checking the restated theorem
applies exactly as stated. -/
theorem exactSource
    {k : Type*} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G)
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    {v : V} (hv : v ≠ 0) :
    ∃ w : V, w ≠ 0 ∧ ∀ g : G, ρ g w = w :=
  Representation.exists_ne_zero_forall_apply_eq_of_isPGroup hG ρ hv

/-- The same statement in higher universes. -/
theorem exactSource_higherUniverse
    {k : Type 1} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
    {G : Type 2} [Group G] [Finite G] (hG : IsPGroup p G)
    {V : Type 3} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    {v : V} (hv : v ≠ 0) :
    ∃ w : V, w ≠ 0 ∧ ∀ g : G, ρ g w = w :=
  Representation.exists_ne_zero_forall_apply_eq_of_isPGroup hG ρ hv

/-- The nonzero-vector hypothesis matters: in the zero module there is no
nonzero vector at all, fixed or otherwise. -/
theorem zero_module_has_no_nonzero_vector :
    ¬ ∃ w : (⊥ : Submodule (ZMod 2) (ZMod 2)), w ≠ 0 := by
  rintro ⟨w, hw⟩
  exact hw (Subsingleton.elim w 0)

end MathlibExtTest.RepresentationTheory.PGroupFixedVector
