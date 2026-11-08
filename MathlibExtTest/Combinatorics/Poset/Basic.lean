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

public import MathlibExt.Combinatorics.Poset.Basic
public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Finsupp.Pointwise
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace MathlibExtTest.Combinatorics.Poset.Basic

open MetaMathlibExt

-- Combinatorics 485: Möbius Algebra Product

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

-- Combinatorics 486: Flag f-Vector


theorem flagFVector_boolean :
    flagFVector (Finset (Fin 2)) {0, 1, 2} = 2 ∧
      flagFVector (Finset (Fin 2)) {1} = 2 ∧
      flagFVector (Finset (Fin 2)) {0, 2} = 1 ∧
      flagFVector (Finset (Fin 2)) ∅ = 1 ∧
      flagFVector (Finset (Fin 3)) {1, 2} = 6 := by
  decide

-- Combinatorics 487: Flag h-Vector


theorem flagHVector_boolean :
    flagHVector (Finset (Fin 2)) ∅ = 1 ∧
      flagHVector (Finset (Fin 2)) {0} = 0 ∧
      flagHVector (Finset (Fin 3)) {1} = 2 ∧
      flagHVector (Finset (Fin 3)) {1, 2} = 1 := by
  decide

-- Combinatorics 488: Hyperplane Arrangement


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

end MathlibExtTest.Combinatorics.Poset.Basic

end
