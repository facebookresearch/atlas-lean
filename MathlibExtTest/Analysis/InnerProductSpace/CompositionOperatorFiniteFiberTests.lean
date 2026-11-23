/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.CompositionOperator

import MathlibExtTest.Analysis.InnerProductSpace.CompositionOperatorTests
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Finite-domain regressions for composition-operator fiber APIs

The count API requires finiteness of the queried fiber. The real supremum
requires uniformly bounded finite fibers. The `fail_if_success` examples are
compile-type rejection checks: a numeric call without the required domain
evidence must fail to elaborate. Other examples check actual finite values,
independence from evidence, and concrete composition-operator values.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.InnerProductSpace.CompositionOperatorFiniteFiberTests

open Set
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal
open MathlibExt.Analysis.InnerProductSpace.CompositionOperator
open MathlibExtTest.Analysis.InnerProductSpace.CompositionOperatorTests

private theorem sqrt_fiber_eq (m : ℕ) :
    Nat.sqrt ⁻¹' {m} = Ico (m * m) ((m + 1) * (m + 1)) := by
  ext n
  simp only [mem_preimage, mem_singleton_iff, mem_Ico]
  exact eq_comm.trans Nat.eq_sqrt

private theorem sqrt_fiber_finite (m : ℕ) : (Nat.sqrt ⁻¹' {m}).Finite := by
  rw [sqrt_fiber_eq]
  exact finite_Ico _ _

private theorem sqrt_fiber_ncard (m : ℕ) : (Nat.sqrt ⁻¹' {m}).ncard = 2 * m + 1 := by
  rw [sqrt_fiber_eq, ncard_Ico_nat]
  have h : (m + 1) * (m + 1) = m * m + (2 * m + 1) := by ring
  rw [h, Nat.add_sub_cancel_left]

private theorem constant_one_fiber_eq_empty : (fun _ : ℕ => 0) ⁻¹' {1} = ∅ := by
  ext n
  simp

private theorem constant_one_fiber_finite : ((fun _ : ℕ => 0) ⁻¹' {1}).Finite := by
  rw [constant_one_fiber_eq_empty]
  exact finite_empty

/-- The constant symbol's zero fiber is infinite, so it has no natural count input. -/
example : ¬ ((fun _ : ℕ => 0) ⁻¹' {0}).Finite := by
  have hset : (fun _ : ℕ => 0) ⁻¹' {0} = univ := by
    ext n
    simp
  rw [hset]
  exact infinite_univ.not_finite

/-- Compile-type rejection: the infinite zero fiber cannot have a numeric count. -/
example : True := by
  fail_if_success
    have invalid : ℕ := fiberCard (fun _ : ℕ => 0) 0
  trivial

/-- Compile-type rejection: the constant symbol cannot have a numeric real supremum. -/
example : True := by
  fail_if_success
    have invalid : ℝ := fiberSup (fun _ : ℕ => 0)
  trivial

/-- Finite individual fibers do not supply a uniform bound. -/
example (M : ℕ) : ¬ HasBoundedFibers Nat.sqrt M := by
  intro h
  have hbound : 2 * M + 1 ≤ M := by
    simpa only [sqrt_fiber_ncard] using (h M).2
  omega

/-- Compile-type rejection: a finite but unbounded family has no real supremum input. -/
example : True := by
  fail_if_success
    have invalid : ℝ := fiberSup Nat.sqrt
  fail_if_success
    have invalid : ℝ := fiberSup Nat.sqrt sqrt_fiber_finite
  trivial

/-- No actual symbol can satisfy a zero bound. -/
example (ψ : ℕ → ℕ) : ¬ HasBoundedFibers ψ 0 := by
  intro h
  have hpos : 0 < (ψ ⁻¹' {ψ 0}).ncard := Nonempty.ncard_pos (h _).1 ⟨0, rfl⟩
  have hbound := (h (ψ 0)).2
  omega

/-- The constant symbol still has the legitimate value zero at its empty one fiber. -/
example : fiberCard (fun _ : ℕ => 0) 1 constant_one_fiber_finite = 0 := by
  rw [fiberCard_eq_ncard, constant_one_fiber_eq_empty, ncard_empty]

/-- Identity fibers have the literal finite count one. -/
example (m : ℕ) :
    fiberCard id m (hasBoundedFibers_of_injective Function.injective_id m).1 = 1 := by
  rw [fiberCard_eq_ncard, preimage_id, ncard_singleton]

/-- Each halving fiber has the literal finite count two. -/
example (m : ℕ) : fiberCard (fun n => n / 2) m (hasBoundedFibers_div_two m).1 = 2 := by
  have hset : (fun n => n / 2) ⁻¹' {m} = {2 * m, 2 * m + 1} := by
    ext n
    simp only [mem_preimage, mem_singleton_iff, mem_insert_iff, mem_singleton_iff]
    omega
  rw [fiberCard_eq_ncard, hset, ncard_pair (by omega : 2 * m ≠ 2 * m + 1)]

/-- Even doubling fibers have the literal finite count one. -/
private theorem fiberCard_double_even (m : ℕ) :
    fiberCard (fun n => 2 * n) (2 * m) (hasBoundedFibers_double (2 * m)).1 = 1 := by
  have hset : (fun n => 2 * n) ⁻¹' {2 * m} = {m} := by
    ext n
    simp only [mem_preimage, mem_singleton_iff]
    omega
  rw [fiberCard_eq_ncard, hset, ncard_singleton]

/-- Odd doubling fibers have the literal finite count zero. -/
example (m : ℕ) :
    fiberCard (fun n => 2 * n) (2 * m + 1) (hasBoundedFibers_double (2 * m + 1)).1 = 0 := by
  have hset : (fun n => 2 * n) ⁻¹' {2 * m + 1} = ∅ := by
    ext n
    simp
    omega
  rw [fiberCard_eq_ncard, hset, ncard_empty]

/-- Counting a finite fiber needs no uniform bound on the other fibers. -/
example (m : ℕ) : fiberCard Nat.sqrt m (sqrt_fiber_finite m) = 2 * m + 1 := by
  rw [fiberCard_eq_ncard, sqrt_fiber_ncard]

/-- A natural count is independent of its finiteness evidence. -/
example (ψ : ℕ → ℕ) (m : ℕ) (h₁ h₂ : (ψ ⁻¹' {m}).Finite) :
    fiberCard ψ m h₁ = fiberCard ψ m h₂ := by
  rfl

/-- The real supremum is independent of the bound and its evidence. -/
example (ψ : ℕ → ℕ) {M₁ M₂ : ℕ}
    (h₁ : HasBoundedFibers ψ M₁) (h₂ : HasBoundedFibers ψ M₂) :
    fiberSup ψ h₁ = fiberSup ψ h₂ := by
  rfl

/-- An injective, nonsurjective doubling symbol has real fiber supremum one. -/
private theorem fiberSup_double : fiberSup (fun n => 2 * n) hasBoundedFibers_double = 1 := by
  have hB : BddAbove (range fun m =>
      (fiberCard (fun n => 2 * n) m (hasBoundedFibers_double m).1 : ℝ)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨m, rfl⟩
    simpa only [fiberCard_eq_ncard, Nat.cast_one] using
      (Nat.cast_le.mpr (hasBoundedFibers_double m).2 :
        (((fun n => 2 * n) ⁻¹' {m}).ncard : ℝ) ≤ (1 : ℕ))
  unfold fiberSup
  apply le_antisymm
  · apply ciSup_le
    intro m
    simpa only [fiberCard_eq_ncard, Nat.cast_one] using
      (Nat.cast_le.mpr (hasBoundedFibers_double m).2 :
        (((fun n => 2 * n) ⁻¹' {m}).ncard : ℝ) ≤ (1 : ℕ))
  · have h0 : fiberCard (fun n => 2 * n) 0 (hasBoundedFibers_double 0).1 = 1 :=
      fiberCard_double_even 0
    simpa only [h0, Nat.cast_one] using le_ciSup hB 0

/-- The doubling composition operator has its original quantitative norm one. -/
example : ‖compCLM (𝕜 := ℂ) (fun n => 2 * n) hasBoundedFibers_double‖ = 1 := by
  rw [norm_compCLM, fiberSup_double, Real.sqrt_one]

/-- Halving copies a nonunit basis coefficient to the first coordinate of its pair. -/
example : compCLM (𝕜 := ℂ) (fun n => n / 2) hasBoundedFibers_div_two
    (lp.single 2 3 (5 : ℂ)) 6 = 5 := by
  norm_num [compCLM_apply, lp.coeFn_single, Pi.single_apply]

/-- Halving copies the same coefficient to the second coordinate of its pair. -/
example : compCLM (𝕜 := ℂ) (fun n => n / 2) hasBoundedFibers_div_two
    (lp.single 2 3 (5 : ℂ)) 7 = 5 := by
  norm_num [compCLM_apply, lp.coeFn_single, Pi.single_apply]

/-- Halving preserves zero at a coordinate outside the selected fiber. -/
example : compCLM (𝕜 := ℂ) (fun n => n / 2) hasBoundedFibers_div_two
    (lp.single 2 3 (5 : ℂ)) 5 = 0 := by
  norm_num [compCLM_apply, lp.coeFn_single, Pi.single_apply]

/-- The actual adjoint adds both nonunit coefficients in a halving fiber. -/
example : (((compCLM (𝕜 := ℂ) (fun n => n / 2) hasBoundedFibers_div_two)†)
    (lp.single 2 6 (7 : ℂ) + lp.single 2 7 (11 : ℂ))) 3 = 18 := by
  rw [adjoint_compCLM_apply]
  have hfin : (hasBoundedFibers_div_two 3).1.toFinset = {6, 7} := by
    ext n
    simp only [Finite.mem_toFinset, mem_preimage, mem_singleton_iff,
      Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hfin, Finset.sum_pair (by decide : (6 : ℕ) ≠ 7)]
  change ((7 : ℂ) + 0) + (0 + 11) = 18
  norm_num

end MathlibExtTest.Analysis.InnerProductSpace.CompositionOperatorFiniteFiberTests
