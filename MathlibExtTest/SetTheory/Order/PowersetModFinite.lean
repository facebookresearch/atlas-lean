/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import MathlibExt.SetTheory.Order.PowersetModFinite
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

namespace MathlibExtTest.SetTheory.Order.PowersetModFinite

open MetaMathlibExt

-- Logic 351: Equal mod finite

theorem eqModFinite_refl (A : Set ℕ) : EqModFinite A A := by
  simp [EqModFinite]

theorem eqModFinite_symm {A B : Set ℕ} (h : EqModFinite A B) : EqModFinite B A := by
  rwa [EqModFinite, symmDiff_comm]

theorem eqModFinite_trans {A B C : Set ℕ} (hab : EqModFinite A B) (hbc : EqModFinite B C) :
    EqModFinite A C :=
  Set.Finite.subset (hab.union hbc) (symmDiff_triangle A B C)

-- Logic 352: $P(\omega)\slash \textrm{fin}$ automorphism

/-- **Proper, via `compl`**: the constant-`∅` map satisfies `respects` and `inter` but is not an
automorphism, since `Φ ∅ᶜ = ∅` while `(Φ ∅)ᶜ = Set.univ`. -/

theorem not_isPowModFiniteAutomorphism_const_empty :
    ¬ IsPowModFiniteAutomorphism (fun _ : Set ℕ => (∅ : Set ℕ)) := by
  intro hΦ
  have h := hΦ.compl ∅
  simp only [EqModFinite, Set.compl_empty] at h
  have hu : symmDiff (∅ : Set ℕ) (Set.univ : Set ℕ) = Set.univ := by
    ext n; simp [Set.mem_symmDiff]
  rw [hu] at h
  exact Set.infinite_univ h

end MathlibExtTest.SetTheory.Order.PowersetModFinite

end
