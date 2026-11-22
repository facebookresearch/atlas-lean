/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import MathlibExt.Probability.KolmogorovCycleNecessity
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Stationary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Time reversal of a stationary finite Markov chain

For a row-stochastic matrix `P` with stationary probability vector `π`
(`π ᵥ* P = π`), the time-reversed transition matrix is
`P* i j = π j * P j i / π i` on the support of `π`. It is row-stochastic,
the support of `π` is closed under it, and it agrees with `P` on the
support if and only if detailed balance `π i * P i j = π j * P j i` holds.
The full-support case and translations into the detailed-balance
vocabulary of `KolmogorovCycleNecessity` and of the continuous-time
stationary-distribution API are included.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997,
  Sections 1.9 and 3.7.
-/

@[expose] public section

namespace ProbabilityTheory

open Matrix

/-- **Time reversal of a stationary finite Markov chain, general support.** Let `P` be a
row-stochastic matrix on a finite state space `ι` and let `π` be a probability vector that is
stationary for `P` (`π ᵥ* P = π`). Let `Pstar` satisfy `Pstar i j = π j * P j i / π i` on every
row `i` in the support of `π`, and have arbitrary stochastic rows off the support. Then `Pstar` is
row-stochastic, the support of `π` is closed under `Pstar`, and `Pstar` agrees with `P` on every
row in the support of `π` (`P* = P` `π`-almost everywhere) if and only if `π` and `P` are in
detailed balance: `π i * P i j = π j * P j i` for all `i j`. -/
theorem timeReversal_of_vecMul_eq_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Pstar : Matrix ι ι ℝ} {π : ι → ℝ}
    (hP : P ∈ rowStochastic ℝ ι) (hπ : (∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1)
    (hstat : π ᵥ* P = π)
    (hsupp : ∀ i j, π i ≠ 0 → Pstar i j = π j * P j i / π i)
    (hoff : ∀ i, π i = 0 → (∀ j, 0 ≤ Pstar i j) ∧ ∑ j, Pstar i j = 1) :
    Pstar ∈ rowStochastic ℝ ι ∧
      (∀ i j, π i ≠ 0 → Pstar i j ≠ 0 → π j ≠ 0) ∧
      ((∀ i, π i ≠ 0 → ∀ j, Pstar i j = P i j) ↔ ∀ i j, π i * P i j = π j * P j i) := by
  have hP' := Matrix.mem_rowStochastic_iff_sum.mp hP
  have hstat_i : ∀ i, (∑ k, π k * P k i) = π i := fun i => congr_fun hstat i
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mem_rowStochastic_iff_sum]
    constructor
    · intro i j
      by_cases hi : π i = 0
      · exact (hoff i hi).1 j
      · rw [hsupp i j hi]
        exact div_nonneg (mul_nonneg (hπ.1 j) (hP'.1 j i)) (hπ.1 i)
    · intro i
      by_cases hi : π i = 0
      · exact (hoff i hi).2
      · have hsum : ∑ j, Pstar i j = (∑ j, π j * P j i) / π i := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl (fun j _ => hsupp i j hi)
        rw [hsum, hstat_i i, div_self hi]
  · intro i j hi hne hj
    apply hne
    rw [hsupp i j hi, hj]
    simp
  · constructor
    · intro hag i j
      by_cases hi : π i = 0
      · have hsum0 : ∑ k, π k * P k i = 0 := by rw [hstat_i i, hi]
        have hall := (Finset.sum_eq_zero_iff_of_nonneg
          (fun k _ => mul_nonneg (hπ.1 k) (hP'.1 k i))).mp hsum0
        have h0 : π j * P j i = 0 := hall j (Finset.mem_univ j)
        rw [hi, zero_mul]
        exact h0.symm
      · have h1 := hag i hi j
        have h2 := hsupp i j hi
        rw [← h1, h2, ← mul_div_assoc]
        exact mul_div_cancel_left₀ _ hi
    · intro hdb i hi j
      rw [hsupp i j hi, ← hdb i j]
      exact mul_div_cancel_left₀ _ hi

/-- **Time reversal of a stationary finite Markov chain, full support.** If `π` is a stationary
probability vector of the row-stochastic matrix `P` and `π i > 0` for every state `i`, then the
reversed matrix `P* i j = π j * P j i / π i` is row-stochastic, and `P* = P` if and only if `π`
and `P` are in detailed balance: `π i * P i j = π j * P j i` for all `i j`. -/
theorem timeReversal_of_vecMul_eq_self_of_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Matrix ι ι ℝ} {π : ι → ℝ}
    (hP : P ∈ rowStochastic ℝ ι) (hπ : (∀ i, 0 < π i) ∧ ∑ i, π i = 1)
    (hstat : π ᵥ* P = π) :
    Matrix.of (fun i j => π j * P j i / π i) ∈ rowStochastic ℝ ι ∧
      (Matrix.of (fun i j => π j * P j i / π i) = P ↔
        ∀ i j, π i * P i j = π j * P j i) := by
  have hπ' : (∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1 :=
    ⟨fun i => le_of_lt (hπ.1 i), hπ.2⟩
  have hne : ∀ i, π i ≠ 0 := fun i => ne_of_gt (hπ.1 i)
  have hsupp : ∀ i j, π i ≠ 0 →
      Matrix.of (fun i j => π j * P j i / π i) i j = π j * P j i / π i :=
    fun i j _ => rfl
  have hoff : ∀ i, π i = 0 → (∀ j, 0 ≤ Matrix.of (fun i j => π j * P j i / π i) i j) ∧
      ∑ j, Matrix.of (fun i j => π j * P j i / π i) i j = 1 := by
    intro i hi
    exact absurd hi (hne i)
  obtain ⟨hstoch, -, hiff⟩ :=
    timeReversal_of_vecMul_eq_self hP hπ' hstat hsupp hoff
  refine ⟨hstoch, ?_⟩
  constructor
  · intro heq
    exact hiff.mp (fun i _ j => by rw [heq])
  · intro hdb
    apply Matrix.ext
    intro i j
    exact hiff.mpr hdb i (hne i) j

end ProbabilityTheory

namespace ProbabilityTheory

open Matrix

/-- Glue: the full-support time reversal in Atlas's matrix detailed-balance vocabulary
(`ProbabilityTheory.IsDetailedBalance`, CTMC/Stationary.lean). -/
theorem timeReversal_eq_self_iff_isDetailedBalance {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Matrix ι ι ℝ} {π : ι → ℝ} (hP : P ∈ rowStochastic ℝ ι)
    (hπ : (∀ i, 0 < π i) ∧ ∑ i, π i = 1) (hstat : π ᵥ* P = π) :
    Matrix.of (fun i j => π j * P j i / π i) = P ↔ IsDetailedBalance π P :=
  (timeReversal_of_vecMul_eq_self_of_pos hP hπ hstat).2

end ProbabilityTheory

namespace StochasticMatrix

open Matrix

/-- Glue: the same statement for the `Fin (M + 1)` API of KolmogorovCycleNecessity.lean
(`StochasticMatrix`, `Distribution`, `IsStationary`, `DetailedBalance`). -/
theorem timeReversal_eq_iff_detailedBalance {M : ℕ} (P : StochasticMatrix M)
    (π : Distribution M) (hstat : P.IsStationary π) (hpos : ∀ i, 0 < π.val i) :
    Matrix.of (fun i j => π.val j * P.prob j i / π.val i) = Matrix.of P.prob ↔
      P.DetailedBalance π := by
  have hP : Matrix.of P.prob ∈ rowStochastic ℝ (Fin (M + 1)) :=
    mem_rowStochastic_iff_sum.mpr ⟨P.nonneg, P.row_sum⟩
  have hv : π.val ᵥ* Matrix.of P.prob = π.val := funext fun j => by
    simpa [vecMul, dotProduct] using hstat j
  exact (ProbabilityTheory.timeReversal_of_vecMul_eq_self_of_pos hP ⟨hpos, π.sum_one⟩ hv).2

end StochasticMatrix
