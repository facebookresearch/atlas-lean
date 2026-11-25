/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SidonIsolatedSums

open MathlibExt.Combinatorics.ErdosSidonIsolatedSumsWanted

example : ∀ M : ℕ, 1 ≤ M → ∃ K : ℕ, ∀ A : Finset ℕ,
    IsSidon A → K ≤ A.card → M ≤ IsolatedCount (Sumset A) :=
  conjecture_holds

example : IsSidon ({0, 2} : Finset ℕ) := by
  intro a ha b hb c hc d hd he
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
  omega

example : Sumset ({0, 2} : Finset ℕ) = {0, 2, 4} := by decide
example : IsIsolated ({0, 2, 4} : Finset ℕ) 0 := by unfold IsIsolated; decide
example : IsolatedCount (Sumset ({0, 2} : Finset ℕ)) = 3 := by decide

example : ¬ IsIsolated ({0, 1, 2} : Finset ℕ) 0 := by unfold IsIsolated; decide
example : IsolatedCount (Sumset ({0, 1} : Finset ℕ)) = 0 := by decide
example : IsolatedCount ({0, 2, 3} : Finset ℕ) = 1 := by decide
example : IsolatedCount ∅ = 0 := by decide
