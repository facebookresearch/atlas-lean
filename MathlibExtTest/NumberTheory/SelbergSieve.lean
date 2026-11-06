/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum

open MathlibExt.SelbergSieve

namespace MathlibExtTest.NumberTheory.SelbergSieve

example (s : BoundingSieve) : 1 ∈ levelSet s 1 := by
  simp only [levelSet, Finset.mem_filter, Nat.mem_divisors]
  exact ⟨⟨one_dvd _, BoundingSieve.prodPrimes_ne_zero⟩, le_rfl⟩

example (s : BoundingSieve) (R : ℕ) (hR : 1 ≤ R) :
    0 < levelWeights s R 1 := by
  rw [levelWeights_one s R hR]
  norm_num

example (s : BoundingSieve) (R d : ℕ) (hRd : R < d) :
    levelWeights s R d = 0 := by
  by_contra hd
  exact (not_le_of_gt hRd) (levelWeights_support s R d hd)

example (s : BoundingSieve) (R d : ℕ) (hR : 1 ≤ R) (hd : d ∣ s.prodPrimes) :
    levelWeights s R d ∈ Set.Icc (-1 : ℝ) 1 := by
  simpa only [Set.mem_Icc] using (abs_le.mp (levelWeights_abs_le s R d hR hd))

example (s : BoundingSieve)
    (hnu : ∀ d : ℕ, d ∣ s.prodPrimes → 1 ≤ (d : ℝ) * s.nu d)
    (hrem : ∀ d : ℕ, d ∣ s.prodPrimes → |s.rem d| ≤ (d : ℝ)) :
    s.errSum (BoundingSieve.lambdaSquared (levelWeights s 2)) ≤ 4096 := by
  have h := levelWeights_errSum_le s 2 (by norm_num) hnu hrem
  norm_num at h
  exact h

-- At level `R = 1` only `d = 1` survives, `G(1) = 1`, and Selberg's bound is the trivial bound
-- `S ≤ X + |R_1|`.
example (s : BoundingSieve) : levelSet s 1 = {1} := by
  ext d
  simp only [levelSet, Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hd, -⟩, h1⟩
    have := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero BoundingSieve.prodPrimes_ne_zero)
    omega
  · rintro rfl
    exact ⟨⟨one_dvd _, BoundingSieve.prodPrimes_ne_zero⟩, le_rfl⟩

example (s : BoundingSieve) : levelSum s 1 = 1 := by
  have h : levelSet s 1 = {1} := by
    ext d
    simp only [levelSet, Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hd, -⟩, h1⟩
      have := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero BoundingSieve.prodPrimes_ne_zero)
      omega
    · rintro rfl
      exact ⟨⟨one_dvd _, BoundingSieve.prodPrimes_ne_zero⟩, le_rfl⟩
  rw [levelSum, h, Finset.sum_singleton, BoundingSieve.selbergTerms_apply, s.nu_mult.map_one]
  simp

example (s : BoundingSieve) (R : ℕ) (hR : 1 ≤ R) :
    s.siftedSum ≤ s.totalMass / levelSum s R +
      ∑ d₁ ∈ levelSet s R, ∑ d₂ ∈ levelSet s R, |s.rem (d₁.lcm d₂)| :=
  siftedSum_le_totalMass_div_levelSum_add s R hR

example (s : BoundingSieve) (R : ℕ) (hR : 1 ≤ R) :
    s.errSum (BoundingSieve.lambdaSquared (levelWeights s R)) ≤
      ∑ d₁ ∈ levelSet s R, ∑ d₂ ∈ levelSet s R, |s.rem (d₁.lcm d₂)| :=
  errSum_lambdaSquared_levelWeights_le s R hR

-- The lower bound for `G(R)` at `R = 0` is `0 ≤ G(0)`, an empty sum on the left.
example (s : BoundingSieve) :
    ∑ δ ∈ (Finset.Icc 1 0).filter (fun δ => δ.primeFactors ⊆ s.prodPrimes.primeFactors),
        ∏ p ∈ δ.primeFactors, s.nu p ^ δ.factorization p ≤ levelSum s 0 :=
  sum_prod_nu_pow_le_levelSum s 0

end MathlibExtTest.NumberTheory.SelbergSieve
