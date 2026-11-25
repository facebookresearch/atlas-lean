/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GPYMaynardSieveReduction
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Tests for the GPY–Maynard positivity reduction
-/

namespace MathlibExtTest.NumberTheory.GPYMaynardSieveReduction

open Filter Topology MathlibExt.NumberTheory.GPYMaynard

example : primeShiftCount {0, 2} 3 = 2 := by decide

/-- `5, 7, 11, 13, 17` are all prime. -/
example : primeShiftCount {0, 2, 6, 8, 12} 5 = 5 := by decide

/-- The finite detector at `n = 3` with the twin-prime shifts `{0, 2}` and `ρ = 1`. -/
example : ∃ n ∈ ({3} : Finset ℕ), (1 : ℝ) < primeShiftCount {0, 2} n := by
  refine exists_lt_primeShiftCount_of_sum_pos {0, 2} {3} (fun _ => 1) (by simp) 1 ?_
  have : primeShiftCount {0, 2} 3 = 2 := by decide
  simp [this]

private theorem primeShiftCount_zero (n : ℕ) :
    (primeShiftCount {0} n : ℝ) = if n.Prime then 1 else 0 := by
  unfold primeShiftCount
  by_cases h : n.Prime <;> simp [Finset.filter_singleton, h]

/-- The hypotheses of the limiting step are jointly satisfiable in a non-degenerate way: with the
single shift `H = {0}`, weights `w_N(n) = 1_ℙ(n)` and `B(N) = S₁(N)`, both ratios are eventually
`1`, Bertrand's postulate gives `B(N) > 0`, and the conclusion is the infinitude of primes. -/
example : {n : ℕ | (1 / 2 : ℝ) < primeShiftCount {0} n}.Infinite := by
  let w : ℕ → ℕ → ℝ := fun _ n => if n.Prime then 1 else 0
  let B : ℕ → ℝ := fun N => ∑ n ∈ Finset.Ico N (2 * N), w N n
  have hB : ∀ᶠ N in atTop, 0 < B N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    obtain ⟨p, hp, hNp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul N (by omega)
    have hp2' : p < 2 * N := by
      rcases lt_or_eq_of_le hp2 with h | h
      · exact h
      · exfalso
        rw [h] at hp
        exact (Nat.not_prime_mul (by norm_num) (by omega)) hp
    have hmem : p ∈ Finset.Ico N (2 * N) := Finset.mem_Ico.mpr ⟨hNp.le, hp2'⟩
    refine lt_of_lt_of_le (by simp [w, hp] : (0 : ℝ) < w N p) ?_
    exact Finset.single_le_sum (f := w N) (fun n _ => by positivity) hmem
  have hone : Tendsto (fun N => (∑ n ∈ Finset.Ico N (2 * N), w N n) / B N) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hB] with N hN
    exact (div_self hN.ne').symm
  have hone' : Tendsto (fun N => (∑ n ∈ Finset.Ico N (2 * N),
      (primeShiftCount {0} n : ℝ) * w N n) / B N) atTop (𝓝 1) := by
    refine hone.congr' (Eventually.of_forall fun N => ?_)
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [primeShiftCount_zero]
    by_cases h : n.Prime <;> simp [w, h]
  exact infinite_lt_primeShiftCount_of_tendsto {0} w (fun N n => by positivity) B hB 1 1 _
    hone hone' (by norm_num)

/-- The one-profile reduction specialised to `ρ = m`: `m < (θ/2)(J/I)` suffices. -/
example (H : Finset ℕ) (m : ℕ) (θ I J : ℝ) (hI : 0 < I) (hm : (m : ℝ) < θ / 2 * (J / I))
    (hasym : ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ (w : ℕ → ℕ → ℝ) (B : ℕ → ℝ),
      (∀ N n, 0 ≤ w N n) ∧ (∀ᶠ N in atTop, 0 < B N) ∧
      Tendsto (fun N => (∑ n ∈ Finset.Ico N (2 * N), w N n) / B N) atTop (𝓝 I) ∧
      Tendsto (fun N => (∑ n ∈ Finset.Ico N (2 * N),
        (primeShiftCount H n : ℝ) * w N n) / B N) atTop (𝓝 ((θ / 2 - δ) * J))) :
    {n : ℕ | (m : ℝ) < primeShiftCount H n}.Infinite :=
  infinite_lt_primeShiftCount_of_maynard_asymptotics H θ m I J hI hm 1 one_pos hasym

/-- Maynard's route to `lim inf (p_{n+1} - p_n) ≤ 12`: two primes among `n + {0, 2, 6, 8, 12}` for
infinitely many `n` give consecutive primes at distance at most `12` infinitely often. -/
example (h : {n : ℕ | ((1 : ℕ) : ℝ) < primeShiftCount {0, 2, 6, 8, 12} n}.Infinite) :
    ∃ᶠ j in atTop, Nat.nth Nat.Prime (j + 1) - Nat.nth Nat.Prime j ≤ 12 :=
  frequently_nth_prime_add_sub_le_of_infinite {0, 2, 6, 8, 12} 1 12 (by decide) h

/-- The bridge with `m = 0` and the single shift `{0}`: infinitely many primes give the
trivial bound `p_j - p_j ≤ 0` frequently. -/
example : ∃ᶠ j in atTop, Nat.nth Nat.Prime (j + 0) - Nat.nth Nat.Prime j ≤ 0 := by
  refine frequently_nth_prime_add_sub_le_of_infinite {0} 0 0 (by decide) ?_
  refine (Nat.infinite_setOfPred_prime).mono fun n hn => ?_
  have hn' : n.Prime := hn
  show ((0 : ℕ) : ℝ) < primeShiftCount {0} n
  rw [primeShiftCount_zero]
  simp [hn']

/-- The set of ratios defining `M_k` is nonempty for every `k`, including `k = 0` and `k = 1`. -/
example (k : ℕ) : (maynardRatio k '' {F | IsMaynardProfile k F}).Nonempty := by
  obtain ⟨F, hF⟩ := exists_isMaynardProfile k
  exact ⟨_, F, hF, rfl⟩

example : ∃ F, IsMaynardProfile 0 F := exists_isMaynardProfile 0

end MathlibExtTest.NumberTheory.GPYMaynardSieveReduction
