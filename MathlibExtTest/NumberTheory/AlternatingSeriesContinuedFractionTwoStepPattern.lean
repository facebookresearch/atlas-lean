/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.AlternatingSeriesContinuedFractionTwoStepPattern

open MetaMathlibExt

-- The first unit partial quotient forced by the two-step pattern is at index 3.
example (x : ℝ) (hirr : Irrational x)
    (u : ℕ → ℕ) (hu : ∀ i, 0 < u i) (hu₀ : u 0 = 1)
    (hsum : HasSum (fun i : ℕ => (-1 : ℝ) ^ i / u i) x)
    (hconv : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i / u i =
      (GenContFract.of x).nums (n + 1) / (GenContFract.of x).dens (n + 1))
    (hdvd : ∀ n : ℕ, u (2 * n + 1) ∣ u (2 * n + 2))
    (hrec : ∀ n : ℕ, (u (2 * n + 3) : ℚ) =
      (∏ j ∈ Finset.range (n + 1), (u (2 * j + 2) : ℚ) / u (2 * j + 1)) ^ 2 + u (2 * n + 2)) :
    (GenContFract.of x).partDens.get? 3 = some 1 :=
  (alternatingSeries_contFract_twoStepPattern x hirr u hu hu₀ hsum hconv hdvd hrec).2.2 1 le_rfl

-- The product formula at the first index.
example (x : ℝ) (hirr : Irrational x)
    (u : ℕ → ℕ) (hu : ∀ i, 0 < u i) (hu₀ : u 0 = 1)
    (hsum : HasSum (fun i : ℕ => (-1 : ℝ) ^ i / u i) x)
    (hconv : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i / u i =
      (GenContFract.of x).nums (n + 1) / (GenContFract.of x).dens (n + 1))
    (hdvd : ∀ n : ℕ, u (2 * n + 1) ∣ u (2 * n + 2))
    (hrec : ∀ n : ℕ, (u (2 * n + 3) : ℚ) =
      (∏ j ∈ Finset.range (n + 1), (u (2 * j + 2) : ℚ) / u (2 * j + 1)) ^ 2 + u (2 * n + 2)) :
    (u 0 : ℝ) = (GenContFract.of x).dens 0 * (GenContFract.of x).dens 1 :=
  (alternatingSeries_contFract_twoStepPattern x hirr u hu hu₀ hsum hconv hdvd hrec).1 0

-- The divisibility conclusion at the first index.
example (x : ℝ) (hirr : Irrational x)
    (u : ℕ → ℕ) (hu : ∀ i, 0 < u i) (hu₀ : u 0 = 1)
    (hsum : HasSum (fun i : ℕ => (-1 : ℝ) ^ i / u i) x)
    (hconv : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i / u i =
      (GenContFract.of x).nums (n + 1) / (GenContFract.of x).dens (n + 1))
    (hdvd : ∀ n : ℕ, u (2 * n + 1) ∣ u (2 * n + 2))
    (hrec : ∀ n : ℕ, (u (2 * n + 3) : ℚ) =
      (∏ j ∈ Finset.range (n + 1), (u (2 * j + 2) : ℚ) / u (2 * j + 1)) ^ 2 + u (2 * n + 2)) :
    ∃ m : ℕ, (GenContFract.of x).partDens.get? 2 =
      some ((GenContFract.of x).dens 1 * m) :=
  (alternatingSeries_contFract_twoStepPattern x hirr u hu hu₀ hsum hconv hdvd hrec).2.1 0
