/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.SidonSubsetCount
import all MathlibExt.Combinatorics.Additive.SidonSubsetCount
import Mathlib.NumberTheory.LSeries.WeakPNT

/-!
# The number of Sidon subsets of an interval relative to its maximum Sidon size

If `A(N)` counts the Sidon subsets of `{1, …, N}` and `f(N)` is their maximum size,
then `A(N) / 2 ^ f(N)` tends to infinity. For every sufficiently large interval, a prime just below
`√(N / 3)` supplies a Singer difference set whose lifts give the required lower bound.

Source: T. F. Bloom, Erdős Problems, Problem #861, https://www.erdosproblems.com/861 (status
SOLVED). UnsolvedMath record UM-30007063 (`EP-861`), dataset ulamai/UnsolvedMath v1.8.0.

Sidon is `MathlibExt`'s `Set.IsSidon`; `A(N)` counts all Sidon subsets, including the empty set and
singletons. `A(N) = 2^{(1 + o(1)) f(N)}` is `log₂ A(N) / f(N) → 1`. formal-conjectures has no
statement of this problem.
-/

public section

namespace MathlibExt.Combinatorics.SidonSubsetCountErdosProblem861Wanted

open Filter

/-- A set counted in a shorter interval is also counted in every longer interval. -/
private theorem sidonSubsetsUpTo_mono : Monotone sidonSubsetsUpTo := by
  classical
  intro m n h s hs
  obtain ⟨hsub, hSidon⟩ := Finset.mem_filter.mp hs
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr <|
    (Finset.mem_powerset.mp hsub).trans (Finset.Icc_subset_Icc_right h), hSidon⟩

/--
**Erdős Problem 861, first question: positive answer.** Let $A(N)$ be the number of Sidon
subsets of $\{1, \dots, N\}$, including the empty set and the singletons, and let $f(N)$ be the
largest size of a Sidon subset of $\{1, \dots, N\}$. Then $A(N) / 2^{f(N)} \to \infty$ as
$N \to \infty$.

Saxton and Thomason proved $A(N) \ge 2^{(1.16 + o(1)) \sqrt{N}}$ (Theorem 2.11), and
$f(N) \sim \sqrt{N}$, so $A(N) / 2^{f(N)} \ge 2^{(0.16 + o(1)) \sqrt{N}} \to \infty$.

Source: T. F. Bloom, Erdős Problems, Problem #861,
https://www.erdosproblems.com/861 (status SOLVED); resolution: D. Saxton and A. Thomason, Hypergraph
containers, Invent. Math. (2015), 925-992, arXiv:1204.6595 (lower bound); Y. Kohayakawa, S. J. Lee,
V. Rödl and W. Samotij, The number of Sidon sets and the maximum size of Sidon sets contained in a
sparse random set of integers, Random Structures Algorithms (2015), 1-25 (upper bound),
Saxton-Thomason Theorem 2.11: there are between 2^{(1.16 + o(1)) √n} and 2^{(55 + o(1)) √n} Sidon
subsets of [n], the lower bound answering negatively whether there are only 2^{(1 + o(1)) √n};
erdosproblems.com/861: f(N) ∼ N^{1/2}, both questions are settled, the first positively and the
second negatively, and 2^{1.16 f(N)} ≤ A(N) ≤ 2^{6.442 f(N)} for large N,
https://arxiv.org/abs/1204.6595.
-/
public theorem sidonCountOverTwoPowMaxDiverges_holds : sidonCountOverTwoPowMaxDiverges := by
  refine tendsto_atTop_atTop.mpr fun b ↦ ?_
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt b (by norm_num : (1 : ℝ) < 2)
  obtain ⟨K, hK⟩ := eventually_atTop.mp <| tendsto_natCast_atTop_atTop.eventually
    (Nat.eventually_exists_prime_mem_Ioc_sub (by norm_num : (0 : ℝ) < 1 / 50))
  let L := max K (200 + 20 * t)
  refine ⟨3 * (L + 1) ^ 2, fun N hN ↦ ?_⟩
  -- The three Singer blocks fit below N when p ≤ k, and N ≤ 3(k + 2)².
  let k := (N / 3).sqrt - 1
  have hroot : L + 1 ≤ (N / 3).sqrt := Nat.le_sqrt'.mpr (by omega)
  have hk : L ≤ k := by dsimp [k]; omega
  have hk_large := (le_max_right K (200 + 20 * t)).trans hk
  obtain ⟨p, hp, hlo, hhi⟩ := hK k ((le_max_left ..).trans hk)
  have hp_lo : 49 * k < 50 * p := by
    exact_mod_cast (show 49 * (k : ℝ) < 50 * p by linarith)
  have hp_hi : p ≤ k := by exact_mod_cast hhi
  have hroot_eq : (N / 3).sqrt = k + 1 := by dsimp [k]; omega
  have hlen : 3 * (p ^ 2 + p + 1) ≤ N := by
    have hs := Nat.sqrt_le' (N / 3)
    rw [hroot_eq] at hs
    have hsq := Nat.pow_le_pow_left hp_hi 2
    nlinarith [Nat.div_mul_le_self N 3]
  have hcount := (singer_count_bound hp).trans (Finset.card_le_card (sidonSubsetsUpTo_mono hlen))
  have hmax := max_size_bound (k := k + 2) (by omega) (N := N) (by
    have hs := Nat.lt_succ_sqrt' (N / 3)
    rw [hroot_eq] at hs
    have : N / 3 < (k + 2) ^ 2 := hs
    rw [show 3 * (k + 2) * (k + 2) = 3 * (k + 2) ^ 2 by ring]
    omega)
  -- The count exponent exceeds 1.96k, while the maximum size is at most 1.9(k + 2).
  have hgap : t + maxSidonSize N ≤ 2 * (p + 1) := by omega
  refine ht.le.trans ((le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ maxSidonSize N)).mpr ?_)
  rw [← pow_add]
  exact_mod_cast (Nat.pow_le_pow_right (by decide : 0 < 2) hgap).trans hcount

end MathlibExt.Combinatorics.SidonSubsetCountErdosProblem861Wanted
