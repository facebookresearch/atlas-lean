/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.Perm.Fin

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Kruskal–Wallis statistic

For a partition of ranked positions into nonempty samples, the Kruskal–Wallis statistic is a
scaled sum of squared deviations of the sample mean ranks from the overall mean rank.
-/

@[expose] public section

namespace WantedExt.Probability.Statistics.KruskalWallisWanted

variable {C N : ℕ}

/-- **Sample size.** The size `n_i` of sample `i` under the assignment `g` of positions to
samples. -/
def sampleSize (g : Fin N → Fin C) (i : Fin C) : ℕ :=
  (Finset.univ.filter fun k => g k = i).card

/-- **Rank sum.** The rank sum `R_i = ∑_{k : g k = i} (σ k + 1)` of sample `i` under the
ranking `σ`. -/
def rankSum (g : Fin N → Fin C) (σ : Equiv.Perm (Fin N)) (i : Fin C) : ℕ :=
  ∑ k ∈ Finset.univ.filter (fun k => g k = i), ((σ k : ℕ) + 1)

/-- **Kruskal–Wallis statistic.** The statistic
`H = 12 / (N (N + 1)) ∑_i R_i² / n_i - 3 (N + 1)`. -/
noncomputable def kruskalWallis (g : Fin N → Fin C) (σ : Equiv.Perm (Fin N)) : ℝ :=
  12 / (N * (N + 1)) * ∑ i, (rankSum g σ i : ℝ) ^ 2 / sampleSize g i - 3 * (N + 1)

-- The fibers of `g` partition the positions.
private theorem sum_sampleSize (g : Fin N → Fin C) : ∑ i, (sampleSize g i : ℝ) = N := by
  have h : ∑ i, sampleSize g i = N := by
    simpa only [sampleSize, ← Finset.card_eq_sum_ones, Finset.card_univ, Fintype.card_fin] using
      (Finset.sum_fiberwise Finset.univ g fun _ => (1 : ℕ))
  exact_mod_cast h

private theorem sum_rankSum (g : Fin N → Fin C) (hN : 0 < N) (σ : Equiv.Perm (Fin N)) :
    ∑ i, (rankSum g σ i : ℝ) = (N : ℝ) * (N + 1) / 2 := by
  -- Reversing the ranks pairs each rank with its complement to `N + 1`.
  have hRanks : ∑ k : Fin N, ((k : ℕ) + 1 : ℝ) = (N : ℝ) * (N + 1) / 2 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    let r : Fin (m + 1) → ℝ := fun k => (k : ℕ) + 1
    change ∑ k, r k = (↑(m + 1) : ℝ) * (↑(m + 1) + 1) / 2
    have hPair (k : Fin (m + 1)) : r k + r (Fin.revPerm k) = (↑(m + 1) : ℝ) + 1 := by
      have h : ((k : ℕ) : ℝ) + (k.rev : ℕ) = m := by
        exact_mod_cast Fin.add_rev_cast k
      change ((k : ℕ) : ℝ) + 1 + ((k.rev : ℕ) + 1) = (↑(m + 1) : ℝ) + 1
      rw [Nat.cast_add, Nat.cast_one]
      calc
        _ = (((k : ℕ) : ℝ) + (k.rev : ℕ)) + 1 + 1 := by ring
        _ = _ := by rw [h]
    apply (eq_div_iff (two_ne_zero : (2 : ℝ) ≠ 0)).2
    calc
      (∑ k, r k) * 2 = (∑ k, r k) + (∑ k, r (Fin.revPerm k)) := by
        rw [Equiv.sum_comp Fin.revPerm r, mul_two]
      _ = ∑ k, (r k + r (Fin.revPerm k)) := Finset.sum_add_distrib.symm
      _ = _ := by simp only [hPair, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
  calc
    ∑ i, (rankSum g σ i : ℝ) = ∑ k : Fin N, ((σ k : ℕ) + 1 : ℝ) := by
      simpa only [rankSum, Nat.cast_sum, Nat.cast_add, Nat.cast_one] using
        (Finset.sum_fiberwise Finset.univ g fun k => ((σ k : ℕ) + 1 : ℝ))
    _ = ∑ k : Fin N, ((k : ℕ) + 1 : ℝ) := Equiv.sum_comp σ fun k => ((k : ℕ) + 1 : ℝ)
    _ = _ := hRanks

/-- **The two forms of `H`.** For an assignment `g` of `N ≥ 1` positions to
`C` samples, each of size `n_i ≥ 1`, and every ranking `σ`,
`H = 12 / (N (N + 1)) ∑_i n_i (R_i / n_i - (N + 1)/2)²`.

Sources: W. H. Kruskal, "A nonparametric test for the several sample problem", Ann. Math. Statist.
23 (1952) 525–540, p. 526. -/
theorem kruskalWallis_eq_sum_sq (g : Fin N → Fin C) (hN : 0 < N)
    (hn : ∀ i, 0 < sampleSize g i) (σ : Equiv.Perm (Fin N)) :
    kruskalWallis g σ = 12 / (N * (N + 1)) *
      ∑ i, (sampleSize g i : ℝ) * ((rankSum g σ i : ℝ) / sampleSize g i - (N + 1) / 2) ^ 2 := by
  have hExpand (i : Fin C) :
      (sampleSize g i : ℝ) * ((rankSum g σ i : ℝ) / sampleSize g i - (N + 1) / 2) ^ 2 =
        (rankSum g σ i : ℝ) ^ 2 / sampleSize g i - (N + 1) * (rankSum g σ i : ℝ) +
          ((N + 1) / 2) ^ 2 * (sampleSize g i : ℝ) := by
    have hi : (sampleSize g i : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hn i)).ne'
    field_simp
    ring
  simp only [kruskalWallis, hExpand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_rankSum g hN σ, sum_sampleSize g]
  have hN₀ : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have hN₁ : (N : ℝ) + 1 ≠ 0 := (add_pos (Nat.cast_pos.mpr hN) zero_lt_one).ne'
  field_simp
  ring

/-- **Two samples.** For an assignment `g` of `N` positions to two samples
of sizes `n₀, n₁ ≥ 1` and every ranking `σ`,
`H = 12 (R_0 - n_0 (N + 1)/2)² / ((N + 1) n_0 (N - n_0))`.

Sources: W. H. Kruskal, "A nonparametric test for the several sample problem", Ann. Math. Statist.
23 (1952) 525–540, p. 526. -/
theorem kruskalWallis_two_samples (g : Fin N → Fin 2)
    (hn : ∀ i, 0 < sampleSize g i) (σ : Equiv.Perm (Fin N)) :
    kruskalWallis g σ = 12 * ((rankSum g σ 0 : ℝ) - sampleSize g 0 * (N + 1) / 2) ^ 2 /
      ((N + 1) * sampleSize g 0 * (N - sampleSize g 0)) := by
  have hSize : (sampleSize g 0 : ℝ) + sampleSize g 1 = N := by
    simpa only [Fin.sum_univ_two] using sum_sampleSize g
  have hPos (i : Fin 2) : 0 < (sampleSize g i : ℝ) := Nat.cast_pos.mpr (hn i)
  have hNPos : 0 < (N : ℝ) := hSize ▸ add_pos (hPos 0) (hPos 1)
  have hN : 0 < N := Nat.cast_pos.mp hNPos
  have hRanks : (rankSum g σ 0 : ℝ) + rankSum g σ 1 = (N : ℝ) * (N + 1) / 2 := by
    simpa only [Fin.sum_univ_two] using sum_rankSum g hN σ
  have hComplement : (N : ℝ) - sampleSize g 0 = sampleSize g 1 := by
    rw [← hSize]
    ring
  let d (i : Fin 2) : ℝ := (rankSum g σ i : ℝ) - sampleSize g i * (N + 1) / 2
  -- The centered rank sums add to zero because the fibers exhaust all positions.
  have hOpp : d 1 = -d 0 := by
    calc
      d 1 = ((rankSum g σ 0 : ℝ) + rankSum g σ 1) -
          ((sampleSize g 0 : ℝ) + sampleSize g 1) * (N + 1) / 2 - d 0 := by
        dsimp [d]
        ring
      _ = -d 0 := by rw [hRanks, hSize, sub_self, zero_sub]
  have hCenter (i : Fin 2) :
      (sampleSize g i : ℝ) * ((rankSum g σ i : ℝ) / sampleSize g i - (N + 1) / 2) ^ 2 =
        d i ^ 2 / sampleSize g i := by
    dsimp [d]
    field_simp [(hPos i).ne']
  change kruskalWallis g σ = 12 * d 0 ^ 2 / ((N + 1) * sampleSize g 0 * (N - sampleSize g 0))
  rw [kruskalWallis_eq_sum_sq g hN hn σ, Fin.sum_univ_two, hCenter 0, hCenter 1, hOpp,
    neg_sq, hComplement]
  field_simp [(hPos 0).ne', (hPos 1).ne', hNPos.ne', (add_pos hNPos zero_lt_one).ne']
  rw [← hSize]
  ring

end WantedExt.Probability.Statistics.KruskalWallisWanted
