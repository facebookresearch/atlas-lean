/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
Canonical stabilizers, orbit quotients and permutation conjugacy. Cycle partitions include fixed
points; cycleType alone does not.
-/

set_option autoImplicit false
noncomputable section

variable {G X : Type*} [Group G] [MulAction G X]

example (g : G) (x : X) : g ∈ MulAction.stabilizer G x ↔ g • x = x := Iff.rfl

example (x : X) : MulAction.orbit G x ≃ G ⧸ MulAction.stabilizer G x :=
  MulAction.orbitEquivQuotientStabilizer G x

example (x : X) : (MulAction.stabilizer G x).index = (MulAction.orbit G x).ncard :=
  MulAction.index_stabilizer G x

example : X ≃ Σ ω : MulAction.orbitRel.Quotient G X, ω.orbit :=
  MulAction.selfEquivSigmaOrbits' G X

example {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    IsConj σ τ ↔ σ.cycleType = τ.cycleType := Equiv.Perm.isConj_iff_cycleType_eq

example : (1 : Equiv.Perm (Fin 3)).cycleType = 0 := Equiv.Perm.cycleType_one
example {n : ℕ} (σ : Equiv.Perm (Fin n)) : 1 ∉ σ.cycleType := by
  intro h
  exact (Nat.lt_irrefl 1) (Equiv.Perm.one_lt_of_mem_cycleType h)

#print axioms MulAction.stabilizer
#print axioms MulAction.orbitEquivQuotientStabilizer
#print axioms MulAction.index_stabilizer
#print axioms MulAction.selfEquivSigmaOrbits'
#print axioms Equiv.Perm.cycleType
#print axioms Equiv.Perm.isConj_iff_cycleType_eq
#print axioms Equiv.Perm.cycleType_one
#print axioms Equiv.Perm.one_lt_of_mem_cycleType

example (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    σ.partition.parts = σ.cycleType + Multiset.replicate (n - σ.support.card) 1 :=
  by simpa only [Fintype.card_fin] using (Equiv.Perm.parts_partition (σ := σ))

example : (1 : Equiv.Perm (Fin 3)).partition.parts = Multiset.replicate 3 1 := by
  simp [Equiv.Perm.parts_partition]

example (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (σ.partition.parts.filter fun k => 2 ≤ k) = σ.cycleType :=
  Equiv.Perm.filter_parts_partition_eq_cycleType

example (n : ℕ) (σ τ : Equiv.Perm (Fin n)) : IsConj σ τ ↔ σ.partition = τ.partition :=
  Equiv.Perm.partition_eq_of_isConj

#print axioms Equiv.Perm.partition
#print axioms Equiv.Perm.parts_partition
#print axioms Equiv.Perm.filter_parts_partition_eq_cycleType
#print axioms Equiv.Perm.partition_eq_of_isConj

end
