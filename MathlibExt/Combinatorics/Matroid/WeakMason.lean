/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Matroid.StrongMason

/-!
# Mason's conjecture: log-concavity of independent set numbers

We deduce ordinary log-concavity from `strong_mason_conjecture`. At or beyond the size of
the ground set, the count at the next index vanishes.
-/

namespace MathlibExt.Combinatorics.WeakMasonWanted

open MathlibExt.Combinatorics.StrongMasonWanted.Combinatorics.StrongMason

/-- **Log-concavity of the independent set numbers of a matroid** (Adiprasito, Huh and Katz,
*Hodge theory for combinatorial geometries*, Ann. of Math. 188 (2018), Theorem 9.9 (3),
answering Conjecture 1.2 of Welsh and Mason). For every finite matroid `M` and every `k ≥ 1`,
`f_{k-1}(M) f_{k+1}(M) ≤ f_k(M)^2`, where `f_k(M)` is the number of independent sets of size
`k`. (AHK state `1 ≤ k ≤ r`, where `r + 1` is the rank; for larger `k` the factor
`f_{k+1}(M)` vanishes, so the inequality is trivial.) -/
public theorem independentSetCount_logConcave {α : Type*} (M : _root_.Matroid α) [M.Finite]
    (k : ℕ) (hk : 1 ≤ k) :
    independentSetCount M (k - 1) * independentSetCount M (k + 1) ≤
      independentSetCount M k ^ 2 := by
  by_cases hkn : k < M.E.ncard
  · have hpos : 0 < k * (M.E.ncard - k) := Nat.mul_pos hk (Nat.sub_pos_of_lt hkn)
    have hmul : k * (M.E.ncard - k) ≤ (k + 1) * (M.E.ncard - k + 1) :=
      Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
    apply Nat.le_of_mul_le_mul_right ?_ hpos
    calc
      (independentSetCount M (k - 1) * independentSetCount M (k + 1)) * (k * (M.E.ncard - k)) ≤
          (independentSetCount M (k - 1) * independentSetCount M (k + 1)) *
            ((k + 1) * (M.E.ncard - k + 1)) := Nat.mul_le_mul_left _ hmul
      _ ≤ independentSetCount M k ^ 2 * (k * (M.E.ncard - k)) := by
        simpa only [Nat.mul_assoc] using strong_mason_conjecture M k hk hkn
  · have hempty : {I ∈ Set.powersetCard α (k + 1) | M.Indep I} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro I hI
      obtain ⟨hcard, hIndep⟩ := hI
      have hle := Set.ncard_le_ncard hIndep.subset_ground M.ground_finite
      rw [Set.ncard_coe_finset, Set.powersetCard.mem_iff.mp hcard] at hle
      exact hkn (Nat.lt_of_succ_le hle)
    have hzero : independentSetCount M (k + 1) = 0 := by
      rw [independentSetCount, hempty, Set.ncard_empty]
    simp [hzero]

end MathlibExt.Combinatorics.WeakMasonWanted
