/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.WeightedDavenportProd

namespace MetaMathlibExt

/-- At the smallest admissible parameters, both blocks have length one. -/
example : ∃ s : List (ZMod 2 × ZMod 2), s.length = 2 ∧ IsWeightedZeroSumFree {1} s := by
  rw [← Finset.Icc_self (1 : ℕ)]
  exact exists_weightedZeroSumFree_zmod_prod 2 2 1 (by decide) (by decide) (by decide) (by decide)

/-- For weights up to five in the product of orders twelve and twenty-four, the nonintegral
ceiling gives a sequence of length six and hence a strict lower bound on the constant. -/
example : 6 < weightedDavenport (Finset.Icc 1 5) (ZMod 12 × ZMod 24) := by
  obtain ⟨s, hlen, hs⟩ := exists_weightedZeroSumFree_zmod_prod 3 12 2
    (by decide) (by decide) (by decide) (by decide)
  have hbound := lt_weightedDavenport hs
  rw [hlen] at hbound
  exact hbound

/-- For $p = 3$, $e_1 = e_2 = 2$ and $c = 1$ the weight bound is
$\beta = \lceil 9/2 \rceil - 1 = 4$ and each coordinate contributes
$\lceil 9/4 \rceil - 1 = 2$ generators, so the $\{1, \dots, 4\}$-weighted Davenport constant of
$(\mathbb{Z}/9\mathbb{Z})^2$ exceeds four. -/
example : 4 < weightedDavenport (Finset.Icc 1 4) (Fin 2 → ZMod 9) := by
  obtain ⟨s, hlen, hs⟩ := exists_weightedZeroSumFree_pi_zmod_prime_pow 3 2 1 Nat.prime_three
    (by decide) (fun _ => 2) monotone_const le_rfl (by decide)
  have hbound := lt_weightedDavenport hs
  rw [hlen] at hbound
  exact hbound

/-- For the exponents $2 \le 3 \le 4$, $p = 2$ and $c = 1$ the weight bound is $\beta = 3$ and
the blocks have lengths $\lceil 4/3 \rceil - 1 = 1$, $\lceil 8/3 \rceil - 1 = 2$ and
$\lceil 16/3 \rceil - 1 = 5$. -/
example :
    8 < weightedDavenport (Finset.Icc 1 3) ((i : Fin 3) → ZMod (2 ^ ((i : ℕ) + 2))) := by
  obtain ⟨s, hlen, hs⟩ := exists_weightedZeroSumFree_pi_zmod_prime_pow 2 3 1 Nat.prime_two
    (by decide) (fun i => (i : ℕ) + 2) (fun _ _ h => Nat.add_le_add_right h 2) le_rfl
    (by decide)
  have hbound := lt_weightedDavenport hs
  rw [hlen] at hbound
  exact hbound

/-- For $c = e_1$ the weight bound is $\beta = 1$, and the sequence has length
$\sum_i (p^{e_i} - 1)$: here $1 + 3 + 7 = 11$ for
$\mathbb{Z}/2\mathbb{Z} \oplus \mathbb{Z}/4\mathbb{Z} \oplus \mathbb{Z}/8\mathbb{Z}$. -/
example : 11 < weightedDavenport {1} ((i : Fin 3) → ZMod (2 ^ ((i : ℕ) + 1))) := by
  rw [← Finset.Icc_self (1 : ℕ)]
  obtain ⟨s, hlen, hs⟩ := exists_weightedZeroSumFree_pi_zmod_prime_pow 2 3 1 Nat.prime_two
    (by decide) (fun i => (i : ℕ) + 1) (fun _ _ h => Nat.add_le_add_right h 1) le_rfl
    (by decide)
  have hbound := lt_weightedDavenport hs
  rw [hlen] at hbound
  exact hbound

/-- The general construction needs no prime powers: for the moduli $2, 3, 4$ and the weight
bound $\beta = 2$ the blocks have lengths $0$, $1$ and $1$. -/
example : 2 < weightedDavenport (Finset.Icc 1 2) ((i : Fin 3) → ZMod ((i : ℕ) + 2)) := by
  obtain ⟨s, hlen, hs⟩ :=
    exists_weightedZeroSumFree_pi_zmod_prime_pow.exists_weightedZeroSumFree_pi_zmod
      (fun i : Fin 3 => (i : ℕ) + 2) 2
  have hbound := lt_weightedDavenport hs
  rw [hlen] at hbound
  exact hbound

end MetaMathlibExt
