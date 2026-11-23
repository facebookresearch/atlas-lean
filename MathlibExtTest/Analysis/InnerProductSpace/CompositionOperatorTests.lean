/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.CompositionOperator

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for composition operators on `ℓ²(ℕ, 𝕜)`

* The identity symbol gives the identity operator, with norm `1`.
* The successor symbol gives the backward shift; its adjoint is the
  forward shift (`0` in coordinate `0`, `y (m - 1)` elsewhere).
* The doubling symbol is injective but not surjective, so its composition
  operator is surjective but not injective, and kills `e₁`.
* The halving symbol `n ↦ n / 2` has fibers of size `2`, operator norm
  `√2`, and its composition operator is injective but not surjective.
* The constant symbol has unbounded fibers, so no composition operator.
* The swap permutation gives a unitary operator exchanging `e₀` and `e₁`.
* Composition operators are never compact.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.InnerProductSpace.CompositionOperatorTests

open Set Filter Topology
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal
open MathlibExt.Analysis.InnerProductSpace.CompositionOperator

/-- The successor symbol has fibers of size at most one. -/
theorem hasBoundedFibers_succ : HasBoundedFibers (fun n => n + 1) 1 :=
  hasBoundedFibers_of_injective (fun a b h => by omega)

/-- The doubling symbol has fibers of size at most one. -/
theorem hasBoundedFibers_double : HasBoundedFibers (fun n => 2 * n) 1 :=
  hasBoundedFibers_of_injective (fun a b h => by omega)

/-- The fiber counts of the identity symbol are all `1`, so its supremum is `1`. -/
theorem fiberSup_id :
    fiberSup (id : ℕ → ℕ) (hasBoundedFibers_of_injective Function.injective_id) = 1 := by
  have h : ∀ m : ℕ, (((id : ℕ → ℕ) ⁻¹' {m}).ncard : ℝ) = 1 := by
    intro m
    rw [Set.preimage_id, Set.ncard_singleton]
    norm_cast
  unfold fiberSup
  simp only [fiberCard_eq_ncard, h]
  exact ciSup_const

/-- The fiber counts of the halving symbol are all `2`, so its supremum is `2`. -/
theorem fiberSup_div_two : fiberSup (fun n => n / 2) hasBoundedFibers_div_two = 2 := by
  have h : ∀ m : ℕ, (((fun n => n / 2) ⁻¹' {m}).ncard : ℝ) = 2 := by
    intro m
    have hset : (fun n => n / 2) ⁻¹' {m} = {2 * m, 2 * m + 1} := by
      ext n
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      omega
    rw [hset, Set.ncard_pair (by omega : 2 * m ≠ 2 * m + 1)]
    norm_cast
  unfold fiberSup
  simp only [fiberCard_eq_ncard, h]
  exact ciSup_const

/-- The identity symbol gives the identity operator. -/
example : compCLM (𝕜 := ℂ) id (hasBoundedFibers_of_injective Function.injective_id) = 1 :=
  compCLM_id _

/-- The identity composition operator has norm `1`. -/
example : ‖compCLM (𝕜 := ℂ) id (hasBoundedFibers_of_injective Function.injective_id)‖ = 1 := by
  rw [norm_compCLM, fiberSup_id, Real.sqrt_one]

/-- The adjoint of the identity composition operator is the identity. -/
example (y : ℓ²(ℕ, ℂ)) :
    ((compCLM (𝕜 := ℂ) id (hasBoundedFibers_of_injective Function.injective_id))†) y = y := by
  rw [show compCLM (𝕜 := ℂ) id (hasBoundedFibers_of_injective Function.injective_id) = 1
      from compCLM_id _, ContinuousLinearMap.adjoint_one, one_apply_eq_self]

/-- The successor symbol gives the backward shift. -/
example (x : ℓ²(ℕ, ℂ)) (n : ℕ) :
    compCLM (𝕜 := ℂ) (fun n => n + 1) hasBoundedFibers_succ x n = (x : ℕ → ℂ) (n + 1) :=
  compCLM_apply _ _ _ _

/-- The adjoint of the successor composition operator is the forward shift. -/
example (y : ℓ²(ℕ, ℂ)) (m : ℕ) :
    (((compCLM (𝕜 := ℂ) (fun n => n + 1) hasBoundedFibers_succ)†) y) m
      = if m = 0 then 0 else (y : ℕ → ℂ) (m - 1) := by
  rw [adjoint_compCLM_apply]
  cases m with
  | zero =>
    have hsum : ∑ n ∈ Set.Finite.toFinset (hasBoundedFibers_succ 0).1, (y : ℕ → ℂ) n = 0 := by
      have hfin : Set.Finite.toFinset (hasBoundedFibers_succ 0).1 = ∅ := by
        apply Finset.ext
        intro n
        simp [Set.Finite.mem_toFinset]
      rw [hfin, Finset.sum_empty]
    rw [hsum]
    simp
  | succ m =>
    have hsum : ∑ n ∈ Set.Finite.toFinset (hasBoundedFibers_succ (m + 1)).1,
        (y : ℕ → ℂ) n = (y : ℕ → ℂ) m := by
      have hfin : Set.Finite.toFinset (hasBoundedFibers_succ (m + 1)).1 = {m} := by
        apply Finset.ext
        intro n
        rw [Finset.mem_singleton, Set.Finite.mem_toFinset]
        constructor
        · intro hn
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hn
          omega
        · intro hn
          rw [hn]
          simp
      rw [hfin, Finset.sum_singleton]
    rw [hsum]
    simp

/-- The successor composition operator is not compact. -/
example : ¬ IsCompactOperator
    (compCLM (𝕜 := ℂ) (fun n => n + 1) hasBoundedFibers_succ) :=
  not_isCompactOperator_compCLM _ _

/-- The doubling symbol is not surjective, so its composition operator is
not injective. -/
example : ¬ Function.Injective
    (compCLM (𝕜 := ℂ) (fun n => 2 * n) hasBoundedFibers_double) := by
  rw [injective_compCLM_iff]
  exact fun hsurj => by
    obtain ⟨n, hn⟩ := hsurj 1
    have hn' : 2 * n = 1 := hn
    omega

/-- The doubling symbol is injective, so its composition operator is surjective. -/
example : Function.Surjective
    (compCLM (𝕜 := ℂ) (fun n => 2 * n) hasBoundedFibers_double) :=
  (surjective_compCLM_iff _ _).mpr (fun a b h => by omega)

/-- The doubling composition operator kills `e₁`, since `1` is not in the
range of doubling. -/
example : compCLM (𝕜 := ℂ) (fun n => 2 * n) hasBoundedFibers_double
    (lp.single 2 1 (1 : ℂ)) = 0 := by
  apply lp.ext
  funext n
  have hne : 2 * n ≠ 1 := by omega
  rw [compCLM_apply, lp.coeFn_single, Pi.single_eq_of_ne hne]
  simp

/-- The halving composition operator has norm `√2`. -/
example : ‖compCLM (𝕜 := ℂ) (fun n => n / 2) hasBoundedFibers_div_two‖ = Real.sqrt 2 := by
  rw [norm_compCLM, fiberSup_div_two]

/-- The halving symbol is surjective, so its composition operator is injective. -/
example : Function.Injective
    (compCLM (𝕜 := ℂ) (fun n => n / 2) hasBoundedFibers_div_two) :=
  (injective_compCLM_iff _ _).mpr (fun m => ⟨2 * m, by omega⟩)

/-- The halving symbol is not injective, so its composition operator is
not surjective. -/
example : ¬ Function.Surjective
    (compCLM (𝕜 := ℂ) (fun n => n / 2) hasBoundedFibers_div_two) := by
  rw [surjective_compCLM_iff]
  exact fun hinj => by
    have h01 := hinj (show (0 : ℕ) / 2 = 1 / 2 from rfl)
    exact zero_ne_one h01

/-- The constant symbol has unbounded fibers: its fiber at `0` is all of `ℕ`. -/
example (M : ℕ) : ¬ HasBoundedFibers (fun _ : ℕ => 0) M := by
  intro h
  have huniv : ((fun _ : ℕ => 0) ⁻¹' {0}) = Set.univ := by
    ext n
    simp
  exact Set.infinite_univ.not_finite (huniv ▸ (h 0).1)

/-- The swap permutation gives a unitary composition operator. -/
example : compCLM (𝕜 := ℂ) (Equiv.swap 0 1) (hasBoundedFibers_equiv (Equiv.swap 0 1))
    ∈ unitary (ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)) :=
  compCLM_mem_unitary (Equiv.swap 0 1)

/-- The swap composition operator exchanges `e₀` and `e₁`. -/
example : compCLM (𝕜 := ℂ) (Equiv.swap 0 1) (hasBoundedFibers_equiv (Equiv.swap 0 1))
    (lp.single 2 0 (1 : ℂ)) = lp.single 2 1 (1 : ℂ) := by
  apply lp.ext
  funext n
  rw [compCLM_apply, lp.coeFn_single, lp.coeFn_single, Equiv.swap_apply_def]
  split_ifs with h0 h1
  · rw [h0, Pi.single_eq_of_ne (by norm_num : (1 : ℕ) ≠ 0),
      Pi.single_eq_of_ne (by norm_num : (0 : ℕ) ≠ 1)]
  · rw [h1, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h0, Pi.single_eq_of_ne h1]

/-- Composition of composition operators composes the symbols in the
reversed order: doubling after successor is `n ↦ 2 * (n + 1)`. -/
example : compCLM (𝕜 := ℂ) (fun n => n + 1) hasBoundedFibers_succ ∘L
    compCLM (𝕜 := ℂ) (fun n => 2 * n) hasBoundedFibers_double
      = compCLM (𝕜 := ℂ) (fun n => 2 * (n + 1))
          (hasBoundedFibers_comp hasBoundedFibers_succ hasBoundedFibers_double) :=
  compCLM_comp hasBoundedFibers_succ hasBoundedFibers_double _

end MathlibExtTest.Analysis.InnerProductSpace.CompositionOperatorTests
