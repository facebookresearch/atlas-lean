/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Logics.Modal.ReflectionCalculusCompleteness

/-! # Tests for Kripke completeness of RC -/

namespace Cslib.Modal.RC.ReflectionCalculusCompletenessTests

-- A higher successor can witness the conjunction with a diamond at a lower index.
example {Atom : Type*} (A B : Formula Atom) {m n : ℕ} (hnm : n < m) :
    Derives (.and (.dia m A) (.dia n B)) (.dia m (.and (.dia n B) A)) := by
  apply (derives_iff_forall_frame _ _).mpr
  rintro W R V hR x ⟨⟨y, hxy, hy⟩, ⟨z, hxz, hz⟩⟩
  exact ⟨y, hxy, ⟨z, hR.condJ hnm hxy hxz, hz⟩, hy⟩

-- Even with no atoms, underivability yields a world with a one-step path but no two-step path.
example : ∃ (W : Type) (R : ℕ → W → W → Prop) (V : W → Empty → Prop), IsFrame R ∧
    ∃ x, Satisfies R V x (.dia 0 .top) ∧ ¬ Satisfies R V x (.dia 0 (.dia 0 .top)) := by
  by_contra h
  apply not_wormLt_zero_zero (Atom := Empty)
  apply (derives_iff_forall_frame _ _).mpr
  intro W R V hR x hx
  by_contra hx'
  exact h ⟨W, R, V, hR, x, hx, hx'⟩

end Cslib.Modal.RC.ReflectionCalculusCompletenessTests
