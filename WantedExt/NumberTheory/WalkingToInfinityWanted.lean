/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.ExtendedCunninghamChain
public import MathlibExt.NumberTheory.WalkingToInfinity
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace MetaMathlibExt

@[expose] public section

/-- **Walking to infinity on primes by appending decimal digits.** For every prime $p_0$ there is
a sequence of primes $p_0, p_1, p_2, \ldots$ starting at $p_0$ such that for every $i \ge 1$ there
are integers $n_i \ge 1$ and $k_i$ with $0 < k_i < 10^{n_i}$ and $p_i = 10^{n_i} p_{i-1} + k_i$;
that is, each term is obtained from the previous one by appending $n_i$ decimal digits on the
right.

Source: Steven J. Miller, Fei Peng, Tudor Popescu, Joshua M. Siktar, and Nawapan
Wattanawanichkul, *Walking to Infinity Along Some Number Theory Sequences*, INTEGERS 24 (2024),
Article A78, Theorem 2.3. -/
public theorem_wanted exists_prime_walk_appending_decimal_digits (p₀ : ℕ) (hp₀ : p₀.Prime) :
    ∃ p : ℕ → ℕ, p 0 = p₀ ∧ (∀ i, (p i).Prime) ∧
      ∀ i, ∃ n k : ℕ, 0 < n ∧ 0 < k ∧ k < 10 ^ n ∧ p (i + 1) = 10 ^ n * p i + k

/-- **Counting right-truncatable square-free numbers.** For natural numbers $b$ and $k$,
$L_{b,k}$ is the number of right-truncatable square-free numbers with exactly $k$ digits in
base $b$: the number of natural numbers $x$ with $b^{k-1} \le x < b^k$ such that
$\lfloor x / b^{\ell} \rfloor$ is square-free for every $\ell \in \{0, \dots, k-1\}$. When
$k = 0$ the range is empty, so $L_{b,0} = 0$.

Source: Steven J. Miller, Fei Peng, Tudor Popescu, Joshua M. Siktar, and Nawapan
Wattanawanichkul, *Walking to Infinity Along Some Number Theory Sequences*, INTEGERS 24 (2024),
Article A78, Definition 3.6. -/
public def rightTruncSquarefreeCount (b k : ℕ) : ℕ :=
  ((Finset.Ico (b ^ (k - 1)) (b ^ k)).filter
    (fun x => ∀ l ∈ Finset.range k, Squarefree (x / b ^ l))).card

/-- **Small counts of right-truncatable square-free numbers.** Let $L_{b,k}$ denote the number of
right-truncatable square-free numbers with exactly $k$ digits in base $b$. Then $L_{2,1} = 1$,
$L_{2,2} = 2$, $L_{2,3} = 3$, $L_{2,4} = 5$ and $L_{10,1} = 6$.

Source: Miller, Peng, Popescu, Siktar, and Wattanawanichkul, *Walking to Infinity Along Some
Number Theory Sequences*, INTEGERS 24 (2024), Article A78, proofs of Theorems 3.8 and 3.9. -/
public theorem rightTruncSquarefreeCount_small :
    rightTruncSquarefreeCount 2 1 = 1 ∧ rightTruncSquarefreeCount 2 2 = 2 ∧
      rightTruncSquarefreeCount 2 3 = 3 ∧ rightTruncSquarefreeCount 2 4 = 5 ∧
      rightTruncSquarefreeCount 10 1 = 6 := by
  decide +kernel

/-- **Bounds on the binary expected square-free walk length.** Let $L_{2,k}$ denote the number of
right-truncatable square-free numbers with exactly $k$ digits in base $2$. The real series
$E_2 = \sum_{k \ge 1} L_{2,k} / 2^k$ satisfies
$636163720502 / 2^{38} \le E_2 \le 636163930777 / 2^{38}$.

This is the series the proof of Theorem 3.8 uses. The paper's Lemma 3.7 prints the denominators
$b^k - b^{k-1}$, which for $b = 2$ would double the sum.

Source: Steven J. Miller, Fei Peng, Tudor Popescu, Joshua M. Siktar, and Nawapan
Wattanawanichkul, *Walking to Infinity Along Some Number Theory Sequences*, INTEGERS 24 (2024),
Article A78, Theorem 3.8. -/
public theorem_wanted binary_squarefree_walk_expectation_bounds :
    (636163720502 : ℝ) / 2 ^ 38 ≤
        ∑' k : ℕ, (rightTruncSquarefreeCount 2 (k + 1) : ℝ) / 2 ^ (k + 1) ∧
      ∑' k : ℕ, (rightTruncSquarefreeCount 2 (k + 1) : ℝ) / 2 ^ (k + 1) ≤
        (636163930777 : ℝ) / 2 ^ 38

end

end MetaMathlibExt
