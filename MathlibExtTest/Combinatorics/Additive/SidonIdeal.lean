/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SidonIdeal

open MetaMathlibExt

-- The empty union is available even when there are no generators.
example : (∅ : Set ℕ) ∈ generatedIdeal (fun _ => False) :=
  ⟨0, Fin.elim0, Fin.elim0, Set.empty_subset _⟩

-- A singleton belongs to the lacunary ideal although it is finite.
example (k : ℕ) : ({k} : Set ℕ) ∈ generatedIdeal IsGapLacunarySet ∧
    ¬ IsGapLacunarySet {k} := by
  refine ⟨sidonIdeal_subset_lacunaryIdeal (mem_generatedIdeal ?_), fun h => ?_⟩
  · rintro a rfl b rfl c rfl d rfl _
    exact Or.inl ⟨rfl, rfl⟩
  · exact h.infinite (Set.finite_singleton k)

-- Two Sidon generators can cover three consecutive points, whose pair sums repeat.
example : ({0, 1, 2} : Set ℕ) ∈ generatedIdeal IsGapLacunarySet := by
  have h01 : ({0, 1} : Set ℕ).IsSidon := by
    intro a ha b hb c hc d hd heq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc hd
    omega
  have h2 : ({2} : Set ℕ).IsSidon := by
    rintro a rfl b rfl c rfl d rfl _
    exact Or.inl ⟨rfl, rfl⟩
  apply sidonIdeal_subset_lacunaryIdeal
  simpa only [Set.insert_union, Set.singleton_union] using
    union_mem_generatedIdeal (mem_generatedIdeal h01) (mem_generatedIdeal h2)

-- Infinitude alone does not suffice: the gaps in ℕ are constantly one.
example : ¬ IsGapLacunarySet (Set.univ : Set ℕ) := by
  intro h
  have hev := h.2.eventually (Filter.eventually_ge_atTop 2)
  obtain ⟨n, hn⟩ := hev.exists
  simp at hn
