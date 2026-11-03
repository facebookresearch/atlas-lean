/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteMarkovChainConvergence

@[expose] public section

/-!
# Tests for the convergence theorem for finite Markov chains
-/

set_option autoImplicit false

open Matrix Filter Topology
open MathlibExt.Probability.MarkovMixing MathlibExt.Probability.FiniteMarkovChainConvergence

namespace MathlibExtTest.Probability.FiniteMarkovChainConvergence

/-- The lazy two-state chain: stay or switch with probability `1/2` each. -/
noncomputable def lazy : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun _ _ => 1 / 2

/-- The uniform distribution on two states. -/
noncomputable def unif : Fin 2 → ℝ := fun _ => 1 / 2

theorem lazy_mem : lazy ∈ rowStochastic ℝ (Fin 2) :=
  mem_rowStochastic_iff_sum.2 ⟨fun _ _ => by norm_num [lazy], fun _ => by
    simp [lazy]⟩

theorem lazy_isPrimitive : lazy.IsPrimitive :=
  ⟨fun _ _ => by norm_num [lazy], 1, one_pos, fun _ _ => by norm_num [lazy]⟩

theorem unif_nonneg : ∀ y, 0 ≤ unif y := fun _ => by norm_num [unif]

theorem unif_sum : ∑ y, unif y = 1 := by simp [unif]

theorem unif_stat : unif ᵥ* lazy = unif := by
  funext y
  simp [vecMul, dotProduct, unif, lazy]

/-- Non-vacuity: the convergence theorem applies to the lazy two-state chain. -/
example : ∃ C α : ℝ, 0 ≤ α ∧ α < 1 ∧
    ∀ (n : ℕ) (x : Fin 2), tvDist (fun y => (lazy ^ n) x y) unif ≤ C * α ^ n :=
  exists_tvDist_pow_le lazy_mem lazy_isPrimitive unif_nonneg unif_sum unif_stat

/-- Doeblin's bound with `r = 1`, `δ = 1`: the lazy chain mixes in one step. -/
example (n : ℕ) (x : Fin 2) : tvDist (fun y => (lazy ^ n) x y) unif ≤ (1 - 1) ^ (n / 1) :=
  tvDist_pow_le_of_minorization lazy_mem unif_nonneg unif_sum unif_stat
    (fun _ _ => by norm_num [unif, lazy]) n x

/-- Rows of powers of the lazy chain converge to the uniform distribution. -/
example (x y : Fin 2) : Tendsto (fun n => (lazy ^ n) x y) atTop (𝓝 (1 / 2)) :=
  tendsto_pow_apply lazy_mem lazy_isPrimitive unif_nonneg unif_sum unif_stat x y

/-- The stationary distribution of the lazy chain has full support. -/
example (y : Fin 2) : 0 < unif y :=
  stationary_pos lazy_isPrimitive unif_nonneg unif_sum unif_stat y

/-- Any stationary vector of total mass `1` of the lazy chain is uniform. -/
example {π : Fin 2 → ℝ} (h1 : ∑ y, π y = 1) (hs : π ᵥ* lazy = π) :
    π = unif :=
  (stationary_unique lazy_mem lazy_isPrimitive unif_nonneg unif_sum unif_stat h1 hs).symm

/-! ### Aperiodicity cannot be dropped -/

/-- The flip chain: always switch states. It is irreducible but periodic. -/
def flip : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem flip_mul_flip : flip * flip = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flip, Matrix.mul_apply, Fin.sum_univ_two]

/-- The uniform distribution is stationary for the flip chain. -/
example : unif ᵥ* flip = unif := by
  funext y
  fin_cases y <;> simp [vecMul, dotProduct, unif, flip, Fin.sum_univ_two]

/-- Boundary case: without aperiodicity there is no convergence. Every even power of the flip
chain is the identity, so the distance of row `0` from the uniform distribution stays `1/2`. -/
example (k : ℕ) : tvDist (fun y => (flip ^ (2 * k)) 0 y) unif = 1 / 2 := by
  rw [pow_mul, sq, flip_mul_flip, one_pow]
  simp [tvDist, unif, Fin.sum_univ_two, Matrix.one_apply]
  norm_num

/-- The flip chain is not primitive. -/
example : ¬ flip.IsPrimitive := by
  rintro ⟨-, k, -, hk⟩
  have h := hk 0 0
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have h1 := hk 0 1
    rw [← two_mul, pow_mul, sq, flip_mul_flip, one_pow] at h1
    simp at h1
  · rw [pow_succ, pow_mul, sq, flip_mul_flip, one_pow, Matrix.one_mul] at h
    simp [flip] at h

end MathlibExtTest.Probability.FiniteMarkovChainConvergence
