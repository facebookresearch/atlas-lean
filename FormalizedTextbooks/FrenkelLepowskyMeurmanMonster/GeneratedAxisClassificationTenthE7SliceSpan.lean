/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SliceProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2XiTransitions
public import Mathlib.LinearAlgebra.Span.Basic

/-! Sixteen genuine roots in the projection-three slice span its entire enclosing E8 section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- The physical coordinate section on the actual transported octad. -/
def generatedTenthE8CoordinateSection : Submodule ℝ (Fin 24 → ℝ) where
  carrier := {x | ∀ i, i ∉ generatedTenthE7OctadSupport → x i = 0}
  zero_mem' := by intro i _; rfl
  add_mem' := by
    intro x y hx hy i hi
    change x i + y i = 0
    rw [hx i hi, hy i hi, add_zero]
  smul_mem' := by intro a x hx i hi; change a * x i = 0; rw [hx i hi, mul_zero]

/-- The real span of all genuine norm-four roots with projection square three. -/
def generatedTenthE7SliceSpan : Submodule ℝ (Fin 24 → ℝ) :=
  Submodule.span ℝ ((fun u : Fin 24 → ℤ => fun i => (u i : ℝ)) ''
    generatedTenthE7SliceIntegral)

private def octadCoordinate : Fin 8 → Fin 24 := ![5, 6, 12, 15, 16, 17, 21, 23]
private def pairLeft : Fin 8 → Fin 24 := ![5, 6, 12, 15, 5, 16, 5, 16]
private def pairRight : Fin 8 → Fin 24 := ![16, 16, 16, 16, 16, 17, 21, 23]
private def pairRoot (j : Fin 8) (s : Fin 2) (i : Fin 24) : ℤ :=
  4 * (if i = pairLeft j then 1 else 0) +
    (if s = 0 then -4 else 4) * (if i = pairRight j then 1 else 0)

private theorem pair_order : ∀ j : Fin 8, pairLeft j < pairRight j := by decide

private theorem pair_mem (j : Fin 8) (s : Fin 2) : pairRoot j s ∈ leechIntegral :=
  leechRootedA2_pair_mem (pairLeft j) (pairRight j) (pair_order j) s

private theorem pair_squares : ∀ (j : Fin 8) (s : Fin 2),
    leechSquareSum (pairRoot j s) = 32 ∧
      leechSquareSum (generatedTenthE7ProjectionInteger *ᵥ pairRoot j s) = 96 := by
  decide +kernel

private theorem pair_slice (j : Fin 8) (s : Fin 2) :
    pairRoot j s ∈ generatedTenthE7SliceIntegral :=
  ⟨pair_mem j s, (pair_squares j s).1, (pair_squares j s).2⟩

private theorem pair_span (j : Fin 8) (s : Fin 2) :
    (fun i => (pairRoot j s i : ℝ)) ∈ generatedTenthE7SliceSpan :=
  Submodule.subset_span ⟨pairRoot j s, pair_slice j s, rfl⟩

private theorem pair_coordinate_certificate : ∀ (j : Fin 8) (i : Fin 24),
    pairRoot j 1 i + (if j.val < 4 then pairRoot j 0 i else -pairRoot j 0 i) =
      8 * (if i = octadCoordinate j then 1 else 0) := by decide +kernel

private theorem coordinate_mem_span (j : Fin 8) :
    (fun i => if i = octadCoordinate j then (1 : ℝ) else 0) ∈
      generatedTenthE7SliceSpan := by
  have h : (fun i => (pairRoot j 1 i : ℝ) +
      (if j.val < 4 then (pairRoot j 0 i : ℝ) else -(pairRoot j 0 i : ℝ))) ∈
        generatedTenthE7SliceSpan := by
    by_cases hj : j.val < 4
    · simp only [hj, ite_true]
      have he : ((fun i => (pairRoot j 1 i : ℝ)) +
          (fun i => (pairRoot j 0 i : ℝ))) =
          (fun i => (pairRoot j 1 i : ℝ) + (pairRoot j 0 i : ℝ)) := by
        funext i
        rfl
      exact he ▸ generatedTenthE7SliceSpan.add_mem (pair_span j 1) (pair_span j 0)
    · simp only [hj, ite_false]
      have he : ((fun i => (pairRoot j 1 i : ℝ)) +
          -(fun i => (pairRoot j 0 i : ℝ))) =
          (fun i => (pairRoot j 1 i : ℝ) + -(pairRoot j 0 i : ℝ)) := by
        funext i
        rfl
      exact he ▸ generatedTenthE7SliceSpan.add_mem (pair_span j 1)
        (generatedTenthE7SliceSpan.neg_mem (pair_span j 0))
  have hs := generatedTenthE7SliceSpan.smul_mem (1 / 8 : ℝ) h
  have he : (1 / 8 : ℝ) • (fun i => (pairRoot j 1 i : ℝ) +
      (if j.val < 4 then (pairRoot j 0 i : ℝ) else -(pairRoot j 0 i : ℝ))) =
        (fun i => if i = octadCoordinate j then (1 : ℝ) else 0) := by
    funext i
    have hh := congrArg (Int.castRingHom ℝ) (pair_coordinate_certificate j i)
    change ((pairRoot j 1 i +
      (if j.val < 4 then pairRoot j 0 i else -pairRoot j 0 i) : ℤ) : ℝ) =
        ((8 * (if i = octadCoordinate j then 1 else 0) : ℤ) : ℝ) at hh
    push_cast at hh
    change (1 / 8 : ℝ) * ((pairRoot j 1 i : ℝ) +
      (if j.val < 4 then (pairRoot j 0 i : ℝ) else -(pairRoot j 0 i : ℝ))) = _
    rw [hh]
    ring
  exact he ▸ hs

/-- Every projection-three root lies in the actual enclosing physical octad section. -/
theorem generatedTenth_e7_slice_span_le :
    generatedTenthE7SliceSpan ≤ generatedTenthE8CoordinateSection := by
  apply Submodule.span_le.mpr
  rintro x ⟨u, hu, rfl⟩ i hi
  change (u i : ℝ) = 0
  rw [generatedTenth_e7_slice_supported u hu i hi, Int.cast_zero]

/-- The entire enclosing E8 coordinate section is spanned by genuine projection-three roots. -/
theorem generatedTenth_e7_slice_span_eq :
    generatedTenthE7SliceSpan = generatedTenthE8CoordinateSection := by
  apply le_antisymm generatedTenth_e7_slice_span_le
  intro x hx
  have hcoord : ∀ i : Fin 24, i ∈ generatedTenthE7OctadSupport →
      ∃ j : Fin 8, octadCoordinate j = i := by decide
  have hsum : x = ∑ i : Fin 24, x i • (fun k => if k = i then (1 : ℝ) else 0) := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp
  rw [hsum]
  apply generatedTenthE7SliceSpan.sum_mem
  intro i _
  by_cases hi : i ∈ generatedTenthE7OctadSupport
  · obtain ⟨j, hj⟩ := hcoord i hi
    rw [← hj]
    exact generatedTenthE7SliceSpan.smul_mem _ (coordinate_mem_span j)
  · rw [hx i hi, zero_smul]
    exact generatedTenthE7SliceSpan.zero_mem

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
