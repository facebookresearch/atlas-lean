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

/-- Existence without primitivity: the periodic flip chain still has a stationary
distribution. -/
example : ∃ π : Fin 2 → ℝ, (∀ y, 0 ≤ π y) ∧ ∑ y, π y = 1 ∧
    π ᵥ* !![0, 1; 1, 0] = π :=
  exists_stationary (by
    rw [mem_rowStochastic_iff_sum]
    refine ⟨fun i j => ?_, fun i => ?_⟩ <;> fin_cases i <;> (try fin_cases j) <;> simp)

/-- The smallest primitive case: on `Unit`, the packaged Perron-Frobenius statement holds for
the identity matrix. -/
example : ∃ π : Unit → ℝ, ((∀ y, 0 ≤ π y) ∧ ∑ y, π y = 1 ∧ π ᵥ* (1 : Matrix Unit Unit ℝ) = π) ∧
    (∀ y, 0 < π y) ∧ (∃ C α : ℝ, 0 ≤ α ∧ α < 1 ∧ ∀ (n : ℕ) (x : Unit),
      tvDist (fun y => ((1 : Matrix Unit Unit ℝ) ^ n) x y) π ≤ C * α ^ n) ∧
    (∀ π' : Unit → ℝ, (∑ y, π' y = 1 ∧ π' ᵥ* (1 : Matrix Unit Unit ℝ) = π') → π' = π) :=
  perron_frobenius_primitive (by
      rw [mem_rowStochastic_iff_sum]; exact ⟨fun i j => by simp, fun i => by simp⟩)
    ⟨fun i j => by simp, 1, one_pos, fun i j => by simp⟩

/-- Empty state space boundary: no vector on `Fin 0` sums to `1`, so `[Nonempty S]` is needed. -/
example (π : Fin 0 → ℝ) : ∑ y, π y ≠ 1 := by simp

/-! ### Stationary invariance under repeated transition -/

/-! ### Non-vacuity: a non-symmetric row-stochastic chain with a stationary law -/

/-- A two-state chain whose stationary law `(1/3, 2/3)` is not uniform, so row and column
conventions give different answers. -/
noncomputable def skew : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 1 / 2; 1 / 4, 3 / 4]

/-- Its stationary law. -/
noncomputable def skewLaw : Fin 2 → ℝ := ![1 / 3, 2 / 3]

theorem skew_mem : skew ∈ rowStochastic ℝ (Fin 2) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩ <;> fin_cases i <;> (try fin_cases j) <;>
    norm_num [skew, Fin.sum_univ_two]

theorem skewLaw_nonneg : ∀ y, 0 ≤ skewLaw y := by
  intro y; fin_cases y <;> norm_num [skewLaw]

theorem skewLaw_sum : ∑ y, skewLaw y = 1 := by
  norm_num [skewLaw, Fin.sum_univ_two]

theorem skewLaw_stat : skewLaw ᵥ* skew = skewLaw := by
  funext y
  fin_cases y <;> norm_num [vecMul, dotProduct, skewLaw, skew, Fin.sum_univ_two]

/-- Every model assumption holds for the fixture, and the law is invariant for every `n`. -/
example : skew ∈ rowStochastic ℝ (Fin 2) ∧ (∀ y, 0 ≤ skewLaw y) ∧ ∑ y, skewLaw y = 1 ∧
    ∀ n : ℕ, skewLaw ᵥ* skew ^ n = skewLaw :=
  ⟨skew_mem, skewLaw_nonneg, skewLaw_sum, vecMul_pow_eq_self skewLaw_stat⟩

/-- A concrete consequence: after three steps from the stationary law, state `0` still has
probability `1/3`. -/
example : ∑ x, skewLaw x * (skew ^ 3) x 0 = 1 / 3 := by
  rw [sum_mul_pow_apply_eq_self skewLaw_stat 3 0]
  norm_num [skewLaw]

/-- Zero steps is the identity case. -/
example : skewLaw ᵥ* skew ^ 0 = skewLaw := vecMul_pow_eq_self skewLaw_stat 0

/-! ### Row-versus-column convention -/

/-- Boundary: the column-convention reading `P *ᵥ π = π` fails for the same fixture, so the
shared interface must fix the row convention. -/
example : skew *ᵥ skewLaw ≠ skewLaw := by
  intro h
  have h0 := congrFun h 0
  norm_num [mulVec, dotProduct, skew, skewLaw, Fin.sum_univ_two] at h0

/-- Bridge: a column-stochastic encoding (the transpose) carries the same invariance through
`mulVec_transpose`. -/
example (n : ℕ) : (skew ^ n)ᵀ *ᵥ skewLaw = skewLaw := by
  rw [mulVec_transpose, vecMul_pow_eq_self skewLaw_stat n]

/-! ### Two-state alternating chain: invariance without convergence -/

theorem unif_stat_flip : unif ᵥ* flip = unif := by
  funext y
  fin_cases y <;> simp [vecMul, dotProduct, unif, flip, Fin.sum_univ_two]


/-- The uniform law is invariant under every power of the flip chain, while the row
`Pⁿ(0, ·)` keeps alternating: invariance of `π` does not give convergence of rows. -/
example (k : ℕ) : unif ᵥ* flip ^ (2 * k + 1) = unif ∧ (flip ^ (2 * k + 1)) 0 0 = 0 ∧
    (flip ^ (2 * k)) 0 0 = 1 := by
  refine ⟨vecMul_pow_eq_self unif_stat_flip _, ?_, ?_⟩
  · rw [pow_succ, pow_mul, sq, flip_mul_flip, one_pow, Matrix.one_mul]
    simp [flip]
  · rw [pow_mul, sq, flip_mul_flip, one_pow]
    simp

/-- The stationarity hypothesis cannot be dropped: a point mass is not invariant under the
flip chain. -/
example : (Pi.single 0 1 : Fin 2 → ℝ) ᵥ* flip ^ 1 ≠ Pi.single 0 1 := by
  intro h
  have h0 := congrFun h 0
  simp [vecMul, dotProduct, flip, Fin.sum_univ_two] at h0

/-! ### Absorbing state and zero mass -/

/-- State `0` is absorbing; state `1` leaks into it. -/
noncomputable def absorb : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1 / 2, 1 / 2]

/-- The point mass on the absorbing state. -/
def atAbsorbing : Fin 2 → ℝ := ![1, 0]

theorem atAbsorbing_stat : atAbsorbing ᵥ* absorb = atAbsorbing := by
  funext y
  fin_cases y <;> norm_num [vecMul, dotProduct, atAbsorbing, absorb, Fin.sum_univ_two]

/-- Zero-mass boundary: the transient state keeps probability `0` after every number of steps
from the absorbing stationary law. -/
example (n : ℕ) : ∑ x, atAbsorbing x * (absorb ^ n) x 1 = 0 := by
  rw [sum_mul_pow_apply_eq_self atAbsorbing_stat n 1]
  simp [atAbsorbing]

/-! ### Two closed communicating classes: invariance without uniqueness -/

/-- Classes `{0, 1}` (a flip) and `{2}` (absorbing). -/
def twoClass : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

/-- Uniform on the first class. -/
noncomputable def lawA : Fin 3 → ℝ := ![1 / 2, 1 / 2, 0]

/-- Point mass on the second class. -/
def lawB : Fin 3 → ℝ := ![0, 0, 1]

theorem lawA_stat : lawA ᵥ* twoClass = lawA := by
  funext y
  fin_cases y <;> simp [vecMul, dotProduct, lawA, twoClass, Fin.sum_univ_three]

theorem lawB_stat : lawB ᵥ* twoClass = lawB := by
  funext y
  fin_cases y <;> simp [vecMul, dotProduct, lawB, twoClass, Fin.sum_univ_three]

/-- Two distinct stationary laws are both invariant under every power. -/
example (n : ℕ) : lawA ᵥ* twoClass ^ n = lawA ∧ lawB ᵥ* twoClass ^ n = lawB ∧ lawA ≠ lawB := by
  refine ⟨vecMul_pow_eq_self lawA_stat n, vecMul_pow_eq_self lawB_stat n, fun h => ?_⟩
  have h2 := congrFun h 2
  simp [lawA, lawB] at h2

/-! ### Totalized reading: the identity does not need normalization -/

/-- The zero vector satisfies the stationarity equation for any matrix, and the theorem
applies to it. It is not a probability vector; the identity is algebraic, and probability
normalization is a separate hypothesis that callers keep. -/
example (n : ℕ) : (0 : Fin 2 → ℝ) ᵥ* skew ^ n = 0 :=
  vecMul_pow_eq_self (zero_vecMul skew) n

/-- Semiring generality: the same statement over `ℕ` (counts instead of probabilities). -/
example (n : ℕ) : (![1, 0] : Fin 2 → ℕ) ᵥ* (!![1, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) ^ n =
    ![1, 0] := by
  refine vecMul_pow_eq_self ?_ n
  funext y
  fin_cases y <;> simp [vecMul, dotProduct, Fin.sum_univ_two]

#print axioms exists_stationary
#print axioms perron_frobenius_primitive

end MathlibExtTest.Probability.FiniteMarkovChainConvergence
