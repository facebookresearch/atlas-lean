/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.AlmostPrime
public import Mathlib.Data.Nat.Nth
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.PrimeCounting
public import MathlibExt.NumberTheory.PrimeCounting.LandauAlmostPrimeAsymptotic
public import WantedExt.NumberTheory.PrimeCounting.DusartMertensReciprocalSumWanted

/-!
# Almost primes of almost prime index

Statements from Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime
Index*, INTEGERS 24 (2024), Article A99.

A `k`-almost prime is a positive integer with exactly `k` prime factors counted with
multiplicity (Mathlib's `Nat.IsAlmostPrime k`). `N_{j,k}` is the set of `j`-almost primes whose
index in the increasing enumeration of the `j`-almost primes is a `k`-almost prime, and
`N_{k_1 k_2 ⋯ k_m}` iterates this: its elements are the `k_1`-almost primes whose index is in
`N_{k_2 ⋯ k_m}`. Indices are `1`-based as in the paper, so the `i`th `k`-almost prime is
`Nat.nth (Nat.IsAlmostPrime k) (i - 1)`, and the `n`th prime `p_n` is `Nat.nth Nat.Prime (n - 1)`.

The counting function `N_{k_1 ⋯ k_m}(x)` is the number of members of `N_{k_1 ⋯ k_m}` that are at
most `x`, written `Set.ncard {n | n ∈ almostPrimeIndexSet k_1 [k_2, …, k_m] ∧ (n : ℝ) ≤ x}`;
the count `N_k(x)` of `k`-almost primes up to `x` is the existing
`MetaMathlibExt.almostPrimeCounting k ⌊x⌋₊` (so `N_2(x)` counts the semiprimes). As in the
paper, `log_2 x = log log x` and `log_3 x = log log log x`, while `log^n x` is a power. The
Meissel–Mertens constant
`β = lim_{x → ∞} (∑_{p ≤ x} 1/p - log log x)` is the existing
`MetaMathlibExt.meisselMertensConstant`.
-/

namespace MetaMathlibExt

open Filter Asymptotics Topology

@[expose] public section

/-- `N_{k_1 k_2 ⋯ k_m}` with `k_1 = k` and `[k_2, …, k_m] = L`: for `L = []` the `k`-almost
primes, and otherwise the `k`-almost primes whose (`1`-based) index lies in `N_{k_2 ⋯ k_m}`.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Section 1 (definitions of `N_k`, `N_{j,k}`, and
`N_{k_1 ⋯ k_m}`). -/
public def almostPrimeIndexSet (k : ℕ) : List ℕ → Set ℕ
  | [] => {n | Nat.IsAlmostPrime k n}
  | j :: L => {n | ∃ i ∈ almostPrimeIndexSet j L, 1 ≤ i ∧ n = Nat.nth (Nat.IsAlmostPrime k) (i - 1)}

/-- `N_k` is the set of `k`-almost primes.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Section 1 (definition of `N_k`). -/
public theorem almostPrimeIndexSet_nil (k : ℕ) :
    almostPrimeIndexSet k [] = {n | Nat.IsAlmostPrime k n} := rfl

/-- Membership in `N_{k j ⋯}` unfolds to an index in `N_{j ⋯}`.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Section 1 (definition of `N_{k_1 ⋯ k_m}`). -/
public theorem mem_almostPrimeIndexSet_cons (k j : ℕ) (L : List ℕ) (n : ℕ) :
    n ∈ almostPrimeIndexSet k (j :: L) ↔
      ∃ i ∈ almostPrimeIndexSet j L, 1 ≤ i ∧ n = Nat.nth (Nat.IsAlmostPrime k) (i - 1) :=
  Iff.rfl

/-- Dusart's bounds for the `n`th prime `p_n`: `p_n ≥ n (log n + log log n - 1)` and
`p_n ≥ n (log n + log log n - 1 + (log log n - 2.25) / log n)` for `n ≥ 2`, and
`p_n ≤ n (log n + log log n - 0.9484)` for `n ≥ 39017`.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Lemma 4 (quoting Dusart) (`integers-2024-A99-lem-4`). -/
public theorem_wanted nth_prime_dusart_bounds :
    (∀ n : ℕ, 2 ≤ n →
      (n : ℝ) * (Real.log n + Real.log (Real.log n) - 1) ≤ Nat.nth Nat.Prime (n - 1)) ∧
    (∀ n : ℕ, 2 ≤ n →
      (n : ℝ) * (Real.log n + Real.log (Real.log n) - 1 +
        (Real.log (Real.log n) - 2.25) / Real.log n) ≤ Nat.nth Nat.Prime (n - 1)) ∧
    (∀ n : ℕ, 39017 ≤ n →
      (Nat.nth Nat.Prime (n - 1) : ℝ) ≤ n * (Real.log n + Real.log (Real.log n) - 0.9484))

/-- For positive integers `j, k`, the sum of reciprocals of the `j`-almost primes of
`k`-almost prime index converges; the same holds for `N_{k_1 ⋯ k_m}` for every `m ≥ 2` and
positive `k_1, …, k_m` (here `k_1 = k` and `L = [k_2, …, k_m]` is nonempty).

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 5 (`integers-2024-A99-thm-5`). -/
public theorem_wanted summable_inv_almostPrimeIndexSet {k : ℕ} {L : List ℕ} (hk : 1 ≤ k)
    (hL : L ≠ []) (hpos : ∀ j ∈ L, 1 ≤ j) :
    Summable fun n : almostPrimeIndexSet k L => (1 : ℝ) / n

/-- The sum of reciprocals of the primes of semiprime index satisfies
`0.9910 < ∑_{n ∈ N_{1,2}} 1/n < 0.9915`.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 6 (`integers-2024-A99-thm-6`). -/
public theorem_wanted tsum_inv_primes_of_semiprime_index_bounds :
    0.9910 < ∑' n : almostPrimeIndexSet 1 [2], (1 : ℝ) / n ∧
      ∑' n : almostPrimeIndexSet 1 [2], (1 : ℝ) / n < 0.9915

/-- Crişan–Erban expansion of the semiprime counting function: there are constants `c_n` with
`c_0 = β` and `c_1 = β - 1 - γ - ∑_p log p / (p (p - 1))` such that for every `N ≥ 0`,
`N_2(x) = (x / log x) ∑_{n < N} n! (log log x + c_n) / log^n x + O_N(x log log x / log^{N+1} x)`.
The paper calls the `c_n` explicit but displays only `c_0` and `c_1`; the other constants are
existential here.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Lemma 1 (quoting Crişan and Erban) (`integers-2024-A99-lem-1`). -/
public theorem_wanted semiprime_count_asymptotic_expansion :
    ∃ c : ℕ → ℝ, c 0 = meisselMertensConstant ∧
      c 1 = meisselMertensConstant - 1 - Real.eulerMascheroniConstant -
        ∑' p : Nat.Primes, Real.log (p : ℕ) / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 1)) ∧
      ∀ N : ℕ, (fun x : ℝ => (almostPrimeCounting 2 ⌊x⌋₊ : ℝ) -
          x / Real.log x * ∑ n ∈ Finset.range N,
            (n.factorial : ℝ) * (Real.log (Real.log x) + c n) / Real.log x ^ n) =O[atTop]
        fun x => x * Real.log (Real.log x) / Real.log x ^ (N + 1)

/-- Explicit estimate for the reciprocal sum of the semiprimes: for all `x > 1`,
`∑_{n ∈ N_2, n ≤ x} 1/n = (log log x + β)² / 2 + (P(2) - ζ(2)) / 2 + α₁ / log x + E(x)` with
`|E(x)| < (log x)^{-3/2}`, where `P(2) = ∑_p p^{-2}`, `ζ(2) = π² / 6`, and
`α₁ = γ + ∑_p log p / (p (p - 1))`.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Lemma 2 (quoting Bayless et al.) (`integers-2024-A99-lem-2`). -/
public theorem_wanted semiprime_reciprocal_sum_explicit_estimate {x : ℝ} (hx : 1 < x) :
    |(∑' n : {n : ℕ // Nat.IsAlmostPrime 2 n ∧ (n : ℝ) ≤ x}, (1 : ℝ) / (n : ℕ)) -
      ((Real.log (Real.log x) + meisselMertensConstant) ^ 2 / 2 +
        ((∑' p : Nat.Primes, (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2) - Real.pi ^ 2 / 6) / 2 +
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, Real.log (p : ℕ) / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 1))) /
          Real.log x)| <
      Real.log x ^ (-(3 / 2 : ℝ))

/-- Erdős–Sárközy uniform bound: `N_{k+1}(t) ≪ (k⁴ / 2^k) t log t` for all real `t ≥ 1` and
integers `k ≥ 1`, with an absolute implied constant.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Lemma 3 (quoting Erdős and Sárközy) (`integers-2024-A99-lem-3`). -/
public theorem_wanted almostPrime_count_le_erdos_sarkozy :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ t : ℝ, 1 ≤ t →
      (almostPrimeCounting (k + 1) ⌊t⌋₊ : ℝ) ≤
        C * ((k : ℝ) ^ 4 / 2 ^ k) * t * Real.log t

/-- Expansions of `log π(x)`, `log log π(x)` and `1 / log π(x)` as `x → ∞`:
`log π(x) = log x - log log x + 1/log x + 3/(2 log² x) + O(1/log³ x)`,
`log log π(x) = log log x - log log x / log x - (log log x)² / (2 log² x) + 1/log² x
+ O((log log x)³ / log³ x)`, and
`1/log π(x) = (1/log x)(1 + log log x / log x + ((log log x)² - 1)/log² x
+ (log log x)³/log³ x + O(log log x / log³ x))`; the last error is stated as
`O(log log x / log⁴ x)` after multiplying out the factor `1/log x`.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Lemma 5 (`integers-2024-A99-lem-5`). -/
public theorem_wanted log_primeCounting_asymptotics :
    ((fun x : ℝ => Real.log (Nat.primeCounting ⌊x⌋₊) -
        (Real.log x - Real.log (Real.log x) + 1 / Real.log x + 3 / (2 * Real.log x ^ 2)))
      =O[atTop] fun x => 1 / Real.log x ^ 3) ∧
    ((fun x : ℝ => Real.log (Real.log (Nat.primeCounting ⌊x⌋₊)) -
        (Real.log (Real.log x) - Real.log (Real.log x) / Real.log x -
          Real.log (Real.log x) ^ 2 / (2 * Real.log x ^ 2) + 1 / Real.log x ^ 2))
      =O[atTop] fun x => Real.log (Real.log x) ^ 3 / Real.log x ^ 3) ∧
    ((fun x : ℝ => 1 / Real.log (Nat.primeCounting ⌊x⌋₊) -
        1 / Real.log x * (1 + Real.log (Real.log x) / Real.log x +
          (Real.log (Real.log x) ^ 2 - 1) / Real.log x ^ 2 +
          Real.log (Real.log x) ^ 3 / Real.log x ^ 3))
      =O[atTop] fun x => Real.log (Real.log x) / Real.log x ^ 4)

/-- Expansion of `1 / log N_2(x)`:
`1/log N_2(x) = (1/log x)(1 + log log x / log x - log log log x / log x
- β / (log x log log x) + O(1/((log x)(log log x)²)))`; the error is stated as
`O(1/(log² x (log log x)²))` after multiplying out the factor `1/log x`.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Lemma 6 (`integers-2024-A99-lem-6`). -/
public theorem_wanted inv_log_semiprime_count_asymptotic :
    (fun x : ℝ => 1 / Real.log (almostPrimeCounting 2 ⌊x⌋₊) -
        1 / Real.log x * (1 + Real.log (Real.log x) / Real.log x -
          Real.log (Real.log (Real.log x)) / Real.log x -
          meisselMertensConstant / (Real.log x * Real.log (Real.log x))))
      =O[atTop] fun x => 1 / (Real.log x ^ 2 * Real.log (Real.log x) ^ 2)

/-- Counting function of the primes of semiprime index:
`N_{1,2}(x) = (x / log² x)(log log x + β + ((log log x + β)(log log x + 1) + c₁) / log x)
+ O(x (log log x)³ / log⁴ x)`, with `c₁ = β - 1 - γ - ∑_p log p / (p (p - 1))` from Lemma 1.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 1 (`integers-2024-A99-thm-1`). -/
public theorem_wanted primes_of_semiprime_index_count_asymptotic :
    (fun x : ℝ => (Set.ncard {n : ℕ | n ∈ almostPrimeIndexSet 1 [2] ∧ (n : ℝ) ≤ x} : ℝ) -
        x / Real.log x ^ 2 * (Real.log (Real.log x) + meisselMertensConstant +
          ((Real.log (Real.log x) + meisselMertensConstant) * (Real.log (Real.log x) + 1) +
            (meisselMertensConstant - 1 - Real.eulerMascheroniConstant -
              ∑' p : Nat.Primes, Real.log (p : ℕ) / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 1)))) /
            Real.log x))
      =O[atTop] fun x => x * Real.log (Real.log x) ^ 3 / Real.log x ^ 4

/-- Counting function of the semiprimes of prime index:
`N_{2,1}(x) = (x / log² x)(log log x + β + (log log x)(log log x - log log log x) / log x)
+ O(x log log x / log³ x)`.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 2 (`integers-2024-A99-thm-2`). -/
public theorem_wanted semiprimes_of_prime_index_count_asymptotic :
    (fun x : ℝ => (Set.ncard {n : ℕ | n ∈ almostPrimeIndexSet 2 [1] ∧ (n : ℝ) ≤ x} : ℝ) -
        x / Real.log x ^ 2 * (Real.log (Real.log x) + meisselMertensConstant +
          Real.log (Real.log x) * (Real.log (Real.log x) - Real.log (Real.log (Real.log x))) /
            Real.log x))
      =O[atTop] fun x => x * Real.log (Real.log x) / Real.log x ^ 3

/-- Eventually there are more primes of semiprime index than semiprimes of prime index up to
`x`, and `N_{1,2}(x) - N_{2,1}(x) = (x log log x log log log x / log³ x)(1 + O(1/log log log x))`;
the error is stated as `O(x log log x / log³ x)` after multiplying out the main factor.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Corollary 1 (`integers-2024-A99-cor-1`). -/
public theorem_wanted primes_of_semiprime_index_count_sub_semiprimes_of_prime_index :
    (∀ᶠ x : ℝ in atTop,
      Set.ncard {n : ℕ | n ∈ almostPrimeIndexSet 2 [1] ∧ (n : ℝ) ≤ x} <
        Set.ncard {n : ℕ | n ∈ almostPrimeIndexSet 1 [2] ∧ (n : ℝ) ≤ x}) ∧
    (fun x : ℝ => (Set.ncard {n : ℕ | n ∈ almostPrimeIndexSet 1 [2] ∧ (n : ℝ) ≤ x} : ℝ) -
        Set.ncard {n : ℕ | n ∈ almostPrimeIndexSet 2 [1] ∧ (n : ℝ) ≤ x} -
        x * Real.log (Real.log x) * Real.log (Real.log (Real.log x)) / Real.log x ^ 3)
      =O[atTop] fun x => x * Real.log (Real.log x) / Real.log x ^ 3

/-- For fixed `j, k ≥ 1`, the counting function of the `j`-almost primes of `k`-almost prime
index satisfies `N_{jk}(x) = (x / log² x) (log log x)^{j+k-2} / ((j-1)! (k-1)!) (1 + O(1/log log x))`.
The paper's clause "the same estimate holds for `N_{kj}`" is the instance with `j` and `k`
swapped, since the main term is symmetric.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 3 (`integers-2024-A99-thm-3`). -/
public theorem_wanted almostPrimeIndexSet_pair_count_asymptotic {j k : ℕ} (hj : 1 ≤ j)
    (hk : 1 ≤ k) :
    (fun x : ℝ => (Set.ncard {n : ℕ | n ∈ almostPrimeIndexSet j [k] ∧ (n : ℝ) ≤ x} : ℝ) -
        x / Real.log x ^ 2 * Real.log (Real.log x) ^ (j + k - 2) /
          ((j - 1).factorial * (k - 1).factorial))
      =O[atTop] fun x => x / Real.log x ^ 2 * Real.log (Real.log x) ^ (j + k - 2) /
          ((j - 1).factorial * (k - 1).factorial) / Real.log (Real.log x)

/-- For fixed `n ≥ 1` and positive integers `k_1, …, k_n` (here `k_1 = k` and
`[k_2, …, k_n] = ks`), `N_{k_1 ⋯ k_n}(x) = (x / log^n x) ∏_{i=1}^n (log log x)^{k_i - 1} / (k_i - 1)!
· (1 + O(1/log log x))`. The extracted exponent `k_1 + ⋯ + k_{n-1} k_n - n` is a typo for
`k_1 + ⋯ + k_{n-1} + k_n - n`, as the paper's equivalent product form shows.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 4 (`integers-2024-A99-thm-4`). -/
public theorem_wanted almostPrimeIndexSet_count_asymptotic {k : ℕ} {ks : List ℕ}
    (hpos : ∀ i ∈ k :: ks, 1 ≤ i) :
    (fun x : ℝ => (Set.ncard {n : ℕ | n ∈ almostPrimeIndexSet k ks ∧ (n : ℝ) ≤ x} : ℝ) -
        x / Real.log x ^ (ks.length + 1) *
          ((k :: ks).map fun i => Real.log (Real.log x) ^ (i - 1) / (i - 1).factorial).prod)
      =O[atTop] fun x => x / Real.log x ^ (ks.length + 1) *
          ((k :: ks).map fun i => Real.log (Real.log x) ^ (i - 1) / (i - 1).factorial).prod /
          Real.log (Real.log x)

/-- For fixed `j, k ≥ 1`, the `n`th member `p_{j,k,n}` of `N_{jk}` satisfies
`p_{j,k,n} = n log² n · (j-1)! (k-1)! / (log log n)^{j+k-2} · (1 + O(1/log log n))`.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Corollary 2 (`integers-2024-A99-cor-2`). -/
public theorem_wanted nth_almostPrimeIndexSet_pair_asymptotic {j k : ℕ} (hj : 1 ≤ j)
    (hk : 1 ≤ k) :
    (fun n : ℕ => (Nat.nth (· ∈ almostPrimeIndexSet j [k]) (n - 1) : ℝ) -
        n * Real.log n ^ 2 * ((j - 1).factorial * (k - 1).factorial) /
          Real.log (Real.log n) ^ (j + k - 2))
      =O[atTop] fun n : ℕ => n * Real.log n ^ 2 * ((j - 1).factorial * (k - 1).factorial) /
          Real.log (Real.log n) ^ (j + k - 2) / Real.log (Real.log n)

/-- For fixed positive integers `k_1, …, k_m` (here `k_1 = k` and `[k_2, …, k_m] = ks`), the
`n`th member of `N_{k_1 ⋯ k_m}` satisfies
`p_{k_1,…,k_m,n} = n (log n)^m ∏_{i=1}^m (k_i - 1)! / (log log n)^{k_i - 1} · (1 + O(1/log log n))`.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Corollary 3 (`integers-2024-A99-cor-3`). -/
public theorem_wanted nth_almostPrimeIndexSet_asymptotic {k : ℕ} {ks : List ℕ}
    (hpos : ∀ i ∈ k :: ks, 1 ≤ i) :
    (fun n : ℕ => (Nat.nth (· ∈ almostPrimeIndexSet k ks) (n - 1) : ℝ) -
        n * Real.log n ^ (ks.length + 1) *
          ((k :: ks).map fun i => ((i - 1).factorial : ℝ) / Real.log (Real.log n) ^ (i - 1)).prod)
      =O[atTop] fun n : ℕ => n * Real.log n ^ (ks.length + 1) *
          ((k :: ks).map fun i => ((i - 1).factorial : ℝ) / Real.log (Real.log n) ^ (i - 1)).prod /
          Real.log (Real.log n)

/-- The reciprocal sum of the primes of `k`-almost prime index tends to `1` exponentially fast:
`∑_{n ∈ N_{1k}} 1/n = 1 + O(e^{-k/2})` as `k → ∞`.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 7 (`integers-2024-A99-thm-7`). -/
public theorem_wanted tsum_inv_primes_of_almostPrime_index_sub_one_isBigO :
    (fun k : ℕ => (∑' n : almostPrimeIndexSet 1 [k], (1 : ℝ) / n) - 1)
      =O[atTop] fun k : ℕ => Real.exp (-(k : ℝ) / 2)

/-- For fixed `j ≥ 1`, `∑_{n ∈ N_{jk}} 1/n ≫ k^{j-1}` as `k → ∞`; in particular, for fixed
`j ≥ 2` this reciprocal sum tends to infinity with `k`.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 8 (`integers-2024-A99-thm-8`). -/
public theorem_wanted tsum_inv_almostPrimeIndexSet_pair_lower_bound {j : ℕ} (hj : 1 ≤ j) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      c * (k : ℝ) ^ (j - 1) ≤ ∑' n : almostPrimeIndexSet j [k], (1 : ℝ) / n) ∧
    (2 ≤ j → Tendsto (fun k : ℕ => ∑' n : almostPrimeIndexSet j [k], (1 : ℝ) / n) atTop atTop)

/-- For fixed `k_1, k_2 ≥ 1`, `∑_{n ∈ N_{k_1 k_2 k}} 1/n ≪ e^{-k/2}` as `k → ∞`. This is the case
`m = 2` of the paper's bound `≪ 1/(e^{k/2})^{m-1}`, the only case its proof supports: the proof
bounds the range `2^{k+1} ≤ t ≤ e^{e^{k/1.99}}` by `k^{j+7-m}/2^k`, which is not
`O(e^{-(m-1)k/2})` once `m ≥ 3`. For `m = 3` and `k_1 = k_2 = k_3 = 1` the single term
`1/p_{p_{p_{2^k}}}` with `p_n < n (log n + log log n)` (`n ≥ 6`) is `≫ 2^{-k} k^{-3}`, and
`e^{k} 2^{-k} k^{-3} → ∞`, so the printed bound fails for `m = 3`.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 9, case `m = 2` (`integers-2024-A99-thm-9`). -/
public theorem_wanted tsum_inv_almostPrimeIndexSet_triple_isBigO {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁)
    (hk₂ : 1 ≤ k₂) :
    (fun k : ℕ => ∑' n : almostPrimeIndexSet k₁ [k₂, k], (1 : ℝ) / n)
      =O[atTop] fun k : ℕ => Real.exp (-(k : ℝ) / 2)

/-- For fixed `m ≥ 2` and `k_1, …, k_m ≥ 1` (here `k_1 = k` and `[k_2, …, k_m] = ks ≠ []`), the
reciprocal sum of `N_{k_1 ⋯ k_m k}` tends to `0` as `k → ∞`.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 9, "in particular" clause (`integers-2024-A99-thm-9`). -/
public theorem_wanted tendsto_tsum_inv_almostPrimeIndexSet_append_zero {k : ℕ} {ks : List ℕ}
    (hks : ks ≠ []) (hpos : ∀ i ∈ k :: ks, 1 ≤ i) :
    Tendsto (fun k' : ℕ => ∑' n : almostPrimeIndexSet k (ks ++ [k']), (1 : ℝ) / n) atTop (𝓝 0)

end

end MetaMathlibExt
