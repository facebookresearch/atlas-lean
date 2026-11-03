/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.SetTheory.ZFC.PSet
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Infinite unions over finite index sets

An infinite union of finitely many sets has an infinite member.

## i. Overview

These are the contrapositive forms of `Set.Finite.biUnion` and `Set.finite_iUnion` in Mathlib, for
finite index sets, `Finset`s and finite families of sets. They are used to find an infinite arm
among the finitely many branches at a site.

## ii. Key results

- `bc4_finite_biUnion_infinite` : the indexed form over a finite set
- `bc4_finite_sUnion_infinite` : the form for a finite family of sets

## iii. Table of contents

- A. Results

## iv. References

- Mathlib: `Set.Finite.biUnion`, `Set.finite_iUnion`, `Set.Finite.sUnion`.
-/

@[expose] public section

open Set

namespace StatMech

namespace Walls

/-! ## A. Results -/

lemma bc4_finite_biUnion_infinite {α ι : Type*} {S : Set ι} (hS : S.Finite)
    {f : ι → Set α} (hinf : (⋃ i ∈ S, f i).Infinite) :
    ∃ i ∈ S, (f i).Infinite := by
  by_contra hcon
  simp only [not_exists, not_and, Set.not_infinite] at hcon
  exact hinf (Set.Finite.biUnion hS (fun i hi => hcon i hi))

lemma bc4_finite_iUnion_infinite {α ι : Type*} [Finite ι] {f : ι → Set α}
    (hinf : (⋃ i, f i).Infinite) : ∃ i, (f i).Infinite := by
  by_contra hcon
  simp only [not_exists, Set.not_infinite] at hcon
  exact hinf (Set.finite_iUnion hcon)

lemma bc4_finset_biUnion_infinite {α ι : Type*} (s : Finset ι) {f : ι → Set α}
    (hinf : (⋃ i ∈ s, f i).Infinite) : ∃ i ∈ s, (f i).Infinite := by
  have hset : (⋃ i ∈ (s : Set ι), f i) = (⋃ i ∈ s, f i) := by
    ext x; simp
  rw [← hset] at hinf
  obtain ⟨i, hi, hfi⟩ := bc4_finite_biUnion_infinite s.finite_toSet hinf
  exact ⟨i, hi, hfi⟩

lemma bc4_finite_sUnion_infinite {α : Type*} {C : Set (Set α)} (hC : C.Finite)
    (hinf : (⋃₀ C).Infinite) : ∃ t ∈ C, Set.Infinite t := by
  by_contra hcon
  simp only [not_exists, not_and, Set.not_infinite] at hcon
  exact hinf (Set.Finite.sUnion hC (fun t ht => hcon t ht))

end Walls

end StatMech
