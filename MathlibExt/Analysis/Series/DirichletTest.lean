/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Summation by parts for complex series

If the partial sums `A n = a 0 + ⋯ + a n` are bounded, `v n → 0`, and `∑ ‖v n - v (n + 1)‖ < ∞`,
then `∑ a n v n` converges (`Complex.exists_tendsto_sum_range_mul_of_bounded_of_summable_norm_sub`).
Abel summation (`Finset.sum_range_by_parts`) writes the partial sum as
`v n A n + ∑_{i < n} (v i - v (i + 1)) A i`; the first term tends to `0` and the series converges
absolutely.

Mathlib has Dirichlet's test only for monotone real `v`
(`Monotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`).

Code-derived port of `summation_by_parts_convergence` from
`v1/Atlas/ComplexVariables/code/Lecture17.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`, lines 17–56, with the file-wide heartbeat override
dropped. The archived formalization and its original license/provenance remain in `v1/` (the
original license text is `v1/LICENSE`). This records equivalence to the archived Lean statement,
not verification against the printed textbook.
-/

set_option autoImplicit false

open Finset Filter Topology

namespace Complex

/-- **Summation by parts** (Abel's test). If the partial sums `a 0 + ⋯ + a n` are bounded,
`v n → 0` and `∑ ‖v n - v (n + 1)‖ < ∞`, then `∑ a n v n` converges. -/
public theorem exists_tendsto_sum_range_mul_of_bounded_of_summable_norm_sub
    (a v : ℕ → ℂ)
    (hA : ∃ M : ℝ, ∀ n, ‖∑ k ∈ range (n + 1), a k‖ ≤ M)
    (hv : Tendsto v atTop (nhds 0))
    (hvs : Summable (fun n => ‖v n - v (n + 1)‖)) :
    ∃ l, Tendsto (fun N => ∑ i ∈ range N, a i * v i) atTop (nhds l) := by
  set A : ℕ → ℂ := fun n => ∑ k ∈ range (n + 1), a k with hA_def
  obtain ⟨M, hM⟩ := hA
  have hsumm : Summable (fun i => (v i - v (i + 1)) * A i) := by
    apply Summable.of_norm_bounded (g := fun i => M * ‖v i - v (i + 1)‖) (hvs.mul_left M)
    intro i
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM i) (norm_nonneg _)
  have htend : Tendsto (fun n => v n * A n) atTop (nhds 0) := by
    have hbdd : IsBoundedUnder (· ≤ ·) atTop (norm ∘ A) :=
      ⟨M, eventually_map.mpr (Eventually.of_forall fun n => hM n)⟩
    have := NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hv hbdd
    simp only [smul_eq_mul] at this
    exact this
  have habp : ∀ n, ∑ i ∈ range (n + 1), a i * v i =
      v n * A n + ∑ i ∈ range n, (v i - v (i + 1)) * A i := by
    intro n
    have := Finset.sum_range_by_parts v a (n + 1)
    simp only [smul_eq_mul, Nat.add_sub_cancel] at this
    simp_rw [mul_comm (a _) (v _)]
    rw [this, sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    congr 1; ext x; ring
  have hsum_tend : Tendsto (fun n => ∑ i ∈ range n, (v i - v (i + 1)) * A i)
      atTop (nhds (∑' i, (v i - v (i + 1)) * A i)) :=
    hsumm.hasSum.tendsto_sum_nat
  have hcomb : Tendsto (fun n => ∑ i ∈ range (n + 1), a i * v i) atTop
      (nhds (∑' i, (v i - v (i + 1)) * A i)) := by
    simp_rw [habp]
    rw [show (∑' i, (v i - v (i + 1)) * A i) = 0 + ∑' i, (v i - v (i + 1)) * A i
      from (zero_add _).symm]
    exact htend.add hsum_tend
  exact ⟨∑' i, (v i - v (i + 1)) * A i, (tendsto_add_atTop_iff_nat 1).mp hcomb⟩

end Complex

