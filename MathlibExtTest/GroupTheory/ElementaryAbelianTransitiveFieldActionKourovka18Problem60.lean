/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ElementaryAbelianTransitiveFieldActionKourovka18Problem60
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic

/-! # Tests for `MathlibExt.GroupTheory.ElementaryAbelianTransitiveFieldActionKourovka18Problem60` -/

namespace MathlibExtTest.GroupTheory.ElementaryAbelianTransitiveFieldActionKourovka18Problem60

open MathlibExt.GroupTheory.ElementaryAbelianTransitiveFieldActionKourovka18Problem60Wanted

/-- The finitely supported functions `ℕ →₀ ZMod 2` form a countably infinite
elementary abelian `2`-group, so the theorem rules out a field-like transitive
automorphism group there. -/
example : ¬ ∃ G : Subgroup (Equiv.Perm (ℕ →₀ ZMod 2)),
    (∀ g ∈ G, ∀ a b : ℕ →₀ ZMod 2, g (a + b) = g a + g b) ∧
    (∀ u w : ℕ →₀ ZMod 2, u ≠ 0 → w ≠ 0 → ∃ g ∈ G, g u = w) ∧
    ∀ v : ℕ →₀ ZMod 2, v ≠ 0 → ∃ (W : AddSubgroup (ℕ →₀ ZMod 2)) (P : Type) (_ : Field P),
      CharP P 2 ∧ IsLocallyFiniteField P ∧ IsCompl (AddSubgroup.zmultiples v) W ∧
      (∀ g ∈ G, g v = v → ∀ w ∈ W, g w ∈ W) ∧
      ∃ (ψ : ↥(G ⊓ MulAction.stabilizer (Equiv.Perm (ℕ →₀ ZMod 2)) v) ≃* Pˣ)
        (θ : (ℕ →₀ ZMod 2) → P),
        Set.BijOn θ (W : Set (ℕ →₀ ZMod 2)) Set.univ ∧
        ∀ h : ↥(G ⊓ MulAction.stabilizer (Equiv.Perm (ℕ →₀ ZMod 2)) v), ∀ w ∈ W,
          θ ((h : Equiv.Perm (ℕ →₀ ZMod 2)) w) = (ψ h : P) * θ w :=
  noTransitiveFieldLikeAutomorphismGroup_holds (ℕ →₀ ZMod 2) inferInstance inferInstance
    (fun v => by
      ext a
      exact CharTwo.add_self_eq_zero (v a))

/-- The field `ZMod 2` is locally finite: every finitely generated subfield is finite. -/
example (_ : Fact (Nat.Prime 2)) : IsLocallyFiniteField (ZMod 2) := by
  intro s
  infer_instance

end MathlibExtTest.GroupTheory.ElementaryAbelianTransitiveFieldActionKourovka18Problem60
