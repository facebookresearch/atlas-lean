/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.LineIncidenceSetsCountErdosProblem607

@[expose] public section

namespace MathlibExt.Combinatorics.LineIncidenceSetsCountErdosProblem607Wanted

open Classical in
/-- The empty point set determines no lines. -/
example : lineIncidenceSet (∅ : Finset (ℝ × ℝ)) = ∅ := by
  simp [lineIncidenceSet]

open Classical in
/-- A single point determines no lines. -/
example (p : ℝ × ℝ) : lineIncidenceSet {p} = ∅ := by
  simp [lineIncidenceSet]

open Classical in
/-- Two distinct points determine one line, containing exactly those two points. -/
example {p q : ℝ × ℝ} (hpq : p ≠ q) : lineIncidenceSet {p, q} = {2} := by
  have hfilter : ∀ pq ∈ ({p, q} : Finset (ℝ × ℝ)).offDiag,
      (({p, q} : Finset (ℝ × ℝ)).filter fun r => r ∈ line[ℝ, pq.1, pq.2]) = {p, q} := by
    intro pq hpqmem
    rw [Finset.mem_offDiag] at hpqmem
    obtain ⟨hpq1, hpq2, hpqne⟩ := hpqmem
    rw [Finset.mem_insert, Finset.mem_singleton] at hpq1 hpq2
    ext r
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      exact h.1
    · intro hr
      refine ⟨hr, ?_⟩
      rcases hpq1 with h1 | h1 <;> rcases hpq2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hpqne
      · rcases hr with rfl | rfl
        · rw [h1]
          exact left_mem_affineSpan_pair _ _ _
        · rw [h2]
          exact right_mem_affineSpan_pair _ _ _
      · rcases hr with rfl | rfl
        · rw [h2]
          exact right_mem_affineSpan_pair _ _ _
        · rw [h1]
          exact left_mem_affineSpan_pair _ _ _
      · exact absurd (h1.trans h2.symm) hpqne
  rw [lineIncidenceSet]
  ext k
  simp only [Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨pq, hpqmem, hcard⟩
    rw [hfilter pq hpqmem] at hcard
    rw [← hcard]
    simp [Finset.card_pair hpq]
  · intro hk
    rw [hk]
    refine ⟨(p, q), ?_, ?_⟩
    · rw [Finset.mem_offDiag]
      exact ⟨by simp, by simp, hpq⟩
    · rw [hfilter (p, q) (by
        rw [Finset.mem_offDiag]
        exact ⟨by simp, by simp, hpq⟩)]
      simp [Finset.card_pair hpq]

open Classical in
/-- There is exactly one line-incidence set for `n = 0`, namely the empty set. -/
example : lineIncidenceSetCount 0 = 1 := by
  have hempty : lineIncidenceSet (∅ : Finset (ℝ × ℝ)) = ∅ := by
    simp [lineIncidenceSet]
  have hset : ((Finset.range (0 + 1)).powerset.filter fun A =>
      ∃ P : Finset (ℝ × ℝ), P.card = 0 ∧ lineIncidenceSet P = A) = {∅} := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · rintro ⟨-, P, hPc, hPA⟩
      have hP : P = ∅ := Finset.card_eq_zero.mp hPc
      subst hP
      rw [hempty] at hPA
      exact hPA.symm
    · intro h
      rw [h]
      exact ⟨Finset.empty_subset _, ∅, by simp, hempty⟩
  unfold lineIncidenceSetCount
  rw [hset]
  simp

/-- The Szemerédi–Trotter bound holds as stated. -/
example : lineIncidenceSetCountSubexponential :=
  lineIncidenceSetCountSubexponential_holds

end MathlibExt.Combinatorics.LineIncidenceSetsCountErdosProblem607Wanted
