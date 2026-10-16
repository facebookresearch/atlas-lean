/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Mark Sepanski
-/
module

public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Finsupp.Pointwise
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 485, Combinatorics 486, Combinatorics 487, Combinatorics 488

-- Combinatorics 485: Möbius Algebra Product
noncomputable def moebiusAlgebraMul {L R : Type*} [Lattice L]
    [CommSemiring R] (f g : L →₀ R) : L →₀ R :=
  f.sum fun s a => g.sum fun t b =>
    Finsupp.single (s ⊓ t) (a * b)

-- Combinatorics 486: Flag f-Vector
def flagFVector (P : Type*) [PartialOrder P] [Fintype P]
    [DecidableEq P] [DecidableLE P] [GradeMinOrder ℕ P]
    (S : Finset ℕ) : ℕ :=
  (Finset.univ.filter fun c : Finset P =>
    (∀ t ∈ c, grade ℕ t ∈ S) ∧
      (∀ x ∈ c, ∀ y ∈ c, x ≤ y ∨ y ≤ x) ∧
      ∀ t, grade ℕ t ∈ S → t ∉ c →
        ∃ x ∈ c, ¬(x ≤ t ∨ t ≤ x)).card

-- Combinatorics 487: Flag h-Vector
def flagHVector (P : Type*) [PartialOrder P] [Fintype P]
    [DecidableEq P] [DecidableLE P] [GradeMinOrder ℕ P]
    (S : Finset ℕ) : ℤ :=
  ∑ T ∈ S.powerset, (-1) ^ (S \ T).card * (flagFVector P T : ℤ)

-- Combinatorics 488: Hyperplane Arrangement
def IsHyperplaneArrangement {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : AffineSubspace K V) (A : Set (AffineSubspace K V)) :
    Prop :=
  A.Finite ∧ ∀ H ∈ A, H ≤ E ∧ (H : Set V).Nonempty ∧
    Module.finrank K H.direction + 1 =
      Module.finrank K E.direction

-- Combinatorics 485: Möbius Algebra Product (sanity check)
theorem moebiusAlgebraMul_values :
    moebiusAlgebraMul
        (Finsupp.single (0 : Fin 3) (1 : ℤ) + Finsupp.single 2 1)
        (Finsupp.single 1 1) =
      Finsupp.single 0 1 + Finsupp.single 1 1 ∧
    moebiusAlgebraMul (Finsupp.single (true, false) (2 : ℤ))
        (Finsupp.single (false, true) 3) =
      Finsupp.single (false, false) 6 := by
  constructor
  · rw [moebiusAlgebraMul, Finsupp.sum_add_index' (by simp)
      (fun _ _ _ => by simp [add_mul, Finsupp.single_add])]
    simp [-Finsupp.single_mul]
  · simp [moebiusAlgebraMul, -Finsupp.single_mul]

-- Combinatorics 486: Flag f-Vector (sanity check)
theorem flagFVector_boolean :
    flagFVector (Finset (Fin 2)) {0, 1, 2} = 2 ∧
      flagFVector (Finset (Fin 2)) {1} = 2 ∧
      flagFVector (Finset (Fin 2)) {0, 2} = 1 ∧
      flagFVector (Finset (Fin 2)) ∅ = 1 ∧
      flagFVector (Finset (Fin 3)) {1, 2} = 6 := by
  decide

-- Combinatorics 487: Flag h-Vector (sanity check)
theorem flagHVector_boolean :
    flagHVector (Finset (Fin 2)) ∅ = 1 ∧
      flagHVector (Finset (Fin 2)) {0} = 0 ∧
      flagHVector (Finset (Fin 3)) {1} = 2 ∧
      flagHVector (Finset (Fin 3)) {1, 2} = 1 := by
  decide

-- Combinatorics 488: Hyperplane Arrangement (sanity check)
theorem isHyperplaneArrangement_points :
    IsHyperplaneArrangement (⊤ : AffineSubspace ℚ ℚ)
        {AffineSubspace.mk' (0 : ℚ) ⊥,
          AffineSubspace.mk' (1 : ℚ) ⊥} ∧
      ¬ IsHyperplaneArrangement
        (⊤ : AffineSubspace ℚ ℚ) {⊥} ∧
      ¬ IsHyperplaneArrangement
        (AffineSubspace.mk' (0 : Fin 2 → ℚ)
          (Submodule.span ℚ {(Pi.single 0 1 : Fin 2 → ℚ)}))
        {AffineSubspace.mk' (Pi.single 1 1 : Fin 2 → ℚ) ⊥} ∧
      ¬ IsHyperplaneArrangement
        (⊤ : AffineSubspace ℚ (Fin 2 → ℚ)) {⊤} := by
  refine ⟨?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · refine ⟨(Set.finite_singleton _).insert _, fun H hH => ?_⟩
    rcases hH with rfl | rfl <;>
      exact ⟨le_top, ⟨_, AffineSubspace.self_mem_mk' _ _⟩,
        by rw [AffineSubspace.direction_mk',
          AffineSubspace.direction_top]; simp⟩
  · obtain ⟨x, hx⟩ := (h.2 ⊥ rfl).2.1
    simp at hx
  · have hm := (h.2 _ rfl).1 (AffineSubspace.self_mem_mk' _ _)
    rw [AffineSubspace.mem_mk',
      Submodule.mem_span_singleton] at hm
    obtain ⟨c, hc⟩ := hm
    have := congrFun hc 1
    simp at this
  · have := (h.2 ⊤ rfl).2.2
    omega

end
