/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Order.Kleene
import Mathlib.Computability.Language

/-!
# Kleene simulation and absorption consumers

The abstract sliding/zero/identity consumers are reused from this project's
Meta program-verification development. Concrete languages and their existing
product Kleene algebra supply noninvertible simulators and proper nonzero
subidentities.

The original consumers are preserved in
`docs/provenance/kleene/AlgebraTests.lean.txt`, lines 228-237. The adjacent
`manifest.json` records their origin path/revision and exact SHA-256 receipts;
the snapshots are documentation, not compiled test dependencies.
-/

open scoped Computability

namespace MathlibExtTest.Algebra.Order.Kleene

/-- Sliding uses simulation without an invertibility premise. -/
example {K : Type*} [KleeneAlgebra K] (a : K) : a * a∗ ≤ a∗ * a :=
  KleeneAlgebra.star_simulation (p := a) (a := a) (b := a) le_rfl

example {K : Type*} [KleeneAlgebra K] (a : K) :
    (0 : K) * a∗ = (0 : K) * a∗ * 0 :=
  KleeneAlgebra.test_star_absorption (by simp) (by simp) (by simp)

example {K : Type*} [KleeneAlgebra K] (a : K) :
    (1 : K) * a∗ = (1 : K) * a∗ * 1 :=
  KleeneAlgebra.test_star_absorption le_rfl (by simp) (by simp)

private def letter (n : Nat) : Language Nat := {[n]}

/-- The singleton-word simulator has no right inverse. -/
private theorem letter_no_right_inverse (q : Language Nat) :
    letter 0 * q ≠ 1 := by
  intro h
  have hnil : [] ∈ letter 0 * q := h.symm ▸ Language.nil_mem_one
  obtain ⟨u, hu, v, _, huv⟩ := Language.mem_mul.mp hnil
  have hu0 : u = [0] := hu
  subst u
  cases huv

/-- A strict simulation of the zero language still includes zero steps. -/
example : letter 0 * (0 : Language Nat)∗ ≤ (letter 1)∗ * letter 0 :=
  KleeneAlgebra.star_simulation (by simp)

/-- The lifted inequality cannot be replaced by equality. -/
example : ¬ (letter 1)∗ * letter 0 ≤ letter 0 * (0 : Language Nat)∗ := by
  intro h
  have hw : [1, 0] ∈ (letter 1)∗ * letter 0 :=
    Language.append_mem_mul
      ((show letter 1 ≤ (letter 1)∗ from le_kstar) rfl) rfl
  have hbad := h hw
  simp only [kstar_zero, mul_one] at hbad
  change [1, 0] = [0] at hbad
  cases hbad

private theorem three_mem_star : [0, 0, 0] ∈ (letter 0)∗ := by
  refine ⟨[[0], [0], [0]], rfl, ?_⟩
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl <;> rfl

/-- A real multi-step word transports through a noninvertible simulator. -/
example : [0, 0, 0, 0] ∈ (letter 0)∗ * letter 0 ∧
    ∀ q : Language Nat, letter 0 * q ≠ 1 := by
  constructor
  · have h := KleeneAlgebra.star_simulation
      (p := letter 0) (a := letter 0) (b := letter 0) le_rfl
    exact h (Language.append_mem_mul (show [0] ∈ letter 0 from rfl)
      three_mem_star)
  · exact letter_no_right_inverse

private def projection : Language Nat × Language Nat := (1, 0)

/-- An existing product carrier supplies a proper, nonzero subidentity. -/
private theorem projection_proper : projection < 1 ∧ projection ≠ 0 := by
  constructor
  · apply lt_of_le_of_ne
    · exact ⟨le_rfl, zero_le⟩
    · intro h
      have hzero : (0 : Language Nat) = 1 := congrArg Prod.snd h
      have hnil : [] ∈ (0 : Language Nat) := hzero.symm ▸ Language.nil_mem_one
      exact hnil
  · intro h
    have hzero : (1 : Language Nat) = 0 := congrArg Prod.fst h
    have hnil : [] ∈ (0 : Language Nat) := hzero ▸ Language.nil_mem_one
    exact hnil

/-- Projection absorption holds for arbitrary, possibly nonidentity steps. -/
private theorem projection_absorption (a : Language Nat × Language Nat) :
    projection * a∗ = projection * a∗ * projection := by
  apply KleeneAlgebra.test_star_absorption
  · exact ⟨le_rfl, zero_le⟩
  · apply Prod.ext <;> simp [projection]
  · apply Prod.ext <;> simp [projection]

example : projection < 1 ∧ projection ≠ 0 := projection_proper

example : projection * (letter 0, letter 1)∗ =
    projection * (letter 0, letter 1)∗ * projection :=
  projection_absorption _

/-- Three iterations survive in the first component after absorption. -/
example : [0, 0, 0] ∈
    (projection * (letter 0, letter 1)∗ * projection).1 := by
  rw [← projection_absorption]
  simpa [projection] using three_mem_star

/-- The other component is blocked, including the empty-word boundary. -/
example : ([] : List Nat) ∉
    (projection * (letter 0, letter 1)∗ * projection).2 := by
  simp [projection]

example : projection * (0 : Language Nat × Language Nat)∗ =
    projection * (0 : Language Nat × Language Nat)∗ * projection :=
  projection_absorption _

/-- Star cannot be replaced by a single step: zero iterations matter. -/
example : projection * (letter 0, letter 1)∗ ≠
    projection * (letter 0, letter 1) := by
  intro h
  have heq := congrArg (fun x => x.1) h
  have hnil : [] ∈ (projection * (letter 0, letter 1)∗).1 := by
    simpa [projection] using Language.nil_mem_kstar (letter 0)
  rw [heq] at hnil
  change [] ∈ (1 : Language Nat) * letter 0 at hnil
  rw [one_mul] at hnil
  change [] = [0] at hnil
  cases hnil

/-- Dropping the simulation premise admits an explicit rejected word. -/
example : ¬ (1 : Language Nat) * (letter 0)∗ ≤ (0 : Language Nat)∗ * 1 := by
  intro h
  have hmem : [0] ∈ (letter 0)∗ :=
    (show letter 0 ≤ (letter 0)∗ from le_kstar) rfl
  have hw : [0] ∈ (1 : Language Nat) * (letter 0)∗ := by
    simpa only [one_mul] using hmem
  have hbad := h hw
  simp only [kstar_zero, mul_one] at hbad
  change [0] = [] at hbad
  cases hbad

end MathlibExtTest.Algebra.Order.Kleene
