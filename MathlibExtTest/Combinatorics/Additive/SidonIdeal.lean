/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SidonIdeal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

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

-- This almost thin set starts at zero, which must not be placed in a doubling tail.
example : Set.range (fun n : ℕ => 2 ^ n - 1) ∈ sidonIdeal := by
  let f (n : ℕ) := 2 ^ n - 1
  have hpow (n : ℕ) : 0 < (2 : ℕ) ^ n := pow_pos (by decide) n
  have hsucc (n : ℕ) : f (n + 1) = 2 * f n + 1 := by
    dsimp [f]
    rw [pow_succ]
    have hp := hpow n
    omega
  have hf : StrictMono f := strictMono_nat_of_lt_succ fun n => by
    rw [hsucc]
    omega
  have hinf := Set.infinite_range_of_injective hf.injective
  have hnth : Nat.nth (· ∈ Set.range f) = f :=
    ((Nat.nth_strictMono hinf).range_inj_of_wellFoundedLT hf).mp (Nat.range_nth_of_infinite hinf)
  apply almostThinIdeal_subset_sidonIdeal (mem_generatedIdeal (A := Set.range f) ?_)
  refine ⟨hinf, 1 / 2, by norm_num, Filter.Eventually.of_forall fun n => ?_⟩
  rw [hnth, hsucc]
  push_cast
  apply (div_le_iff₀ (by positivity)).2
  linarith

-- An empty system of almost-thin generators also gives a Sidon cover.
example : (∅ : Set ℕ) ∈ sidonIdeal :=
  almostThinIdeal_subset_sidonIdeal ⟨0, Fin.elim0, fun i => Fin.elim0 i, Set.empty_subset _⟩
