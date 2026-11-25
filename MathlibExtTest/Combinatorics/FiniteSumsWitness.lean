/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.FiniteSumsWitness

/-! # Tests for finite sums witnesses on the positive integers -/

namespace MetaMathlibExt.finiteSums_witness_iff_mem_closure_idempotents

attribute [local instance] Ultrafilter.add

-- A singleton basic neighbourhood excludes every principal ultrafilter from the closure.
example (n : ℕ+) :
    (pure n : Ultrafilter ℕ+) ∉ closure {V : Ultrafilter ℕ+ | V + V = V} := by
  intro h
  obtain ⟨X, hX, hs⟩ := (finiteSums_witness_iff_mem_closure_idempotents _).2 h
    {n} (Ultrafilter.mem_pure.mpr rfl)
  apply hX
  apply (Set.finite_singleton n).subset
  intro x hx
  obtain ⟨y, hy, heq⟩ := hs {x} (Finset.singleton_nonempty _) (by simpa using hx)
  exact (show y = x by simpa using heq) ▸ hy

-- A member of an idempotent contains two distinct summands and their sum.
example (V : Ultrafilter ℕ+) (hid : V + V = V) (A : Set ℕ+) (hA : A ∈ V) :
    ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ a + b ∈ A := by
  obtain ⟨X, hX, hs⟩ := (finiteSums_witness_iff_mem_closure_idempotents V).2
    (subset_closure hid) A hA
  have hXA : X ⊆ A := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := hs {x} (Finset.singleton_nonempty _) (by simpa using hx)
    exact (show y = x by simpa using heq) ▸ hy
  obtain ⟨a, ha, b, hb, hab⟩ := hX.nontrivial
  have hpair : (↑({a, b} : Finset ℕ+) : Set ℕ+) ⊆ X := by
    simpa only [Finset.coe_insert, Finset.coe_singleton, Set.insert_subset_iff,
      Set.singleton_subset_iff] using And.intro ha hb
  obtain ⟨y, hy, heq⟩ := hs {a, b} (Finset.insert_nonempty ..) hpair
  refine ⟨a, hXA ha, b, hXA hb, hab, ?_⟩
  have hsum : (y : ℕ) = (a : ℕ) + (b : ℕ) := by simpa [hab] using heq
  exact (Subtype.ext hsum : y = a + b) ▸ hy

end MetaMathlibExt.finiteSums_witness_iff_mem_closure_idempotents
