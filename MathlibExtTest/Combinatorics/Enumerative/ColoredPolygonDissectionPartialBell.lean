/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.ColoredDyckPathPartialBell
import MathlibExt.Combinatorics.Enumerative.ColoredPolygonDissectionPartialBell

open MetaMathlibExt

/-- The partial Bell polynomial commutes with the cast `ℕ → ℚ`. -/
private theorem partialBellPolynomial_natCast (n k : ℕ) (x : ℕ → ℕ) :
    partialBellPolynomial n k (fun j => (x j : ℚ)) = ((partialBellPolynomial n k x : ℕ) : ℚ) := by
  simp [partialBellPolynomial]

-- With one color for every polygon, `decide` evaluates the Lah number
-- `B_{3,2}(1!, 2!, 3!, …) = 6` in `ℕ`, and the formula gives the five dissections of a pentagon
-- into two polygons: `1/4 · 10 · 2!/3! · 6 = 5`.
example : coloredPolygonDissectionCount (fun _ => 1) 3 2 = 5 := by
  have h := coloredPolygonDissectionCount_eq_partialBell (fun _ => 1) (n := 3) (k := 2)
    (by norm_num) (by norm_num)
  have hB : partialBellPolynomial 3 2 (fun j => j.factorial * 1) = 6 := by decide
  have hcast : (fun j : ℕ => (j.factorial : ℚ) * ((1 : ℕ) : ℚ)) =
      fun j => ((j.factorial * 1 : ℕ) : ℚ) := by
    ext j
    push_cast
    rfl
  rw [hcast, partialBellPolynomial_natCast, hB] at h
  norm_num [Nat.choose, Nat.factorial] at h
  exact_mod_cast h

-- With γ₁ = 2, γ₂ = 3 and γ₃ = 5, `decide` evaluates `B_{4,2}(x) = 4 x₁ x₃ + 3 x₂²` at
-- `x_j = j! γ_j`, that is `4 · 2 · 30 + 3 · 6² = 348`, and the formula recovers the 87 colored
-- dissections of a hexagon by one diagonal: `1/5 · 15 · 2!/4! · 348 = 87`.
example : coloredPolygonDissectionCount (fun j => if j = 1 then 2 else if j = 2 then 3
    else if j = 3 then 5 else 0) 4 2 = 87 := by
  have h := coloredPolygonDissectionCount_eq_partialBell (fun j => if j = 1 then 2
    else if j = 2 then 3 else if j = 3 then 5 else 0) (n := 4) (k := 2) (by norm_num) (by norm_num)
  have hB : partialBellPolynomial 4 2 (fun j => j.factorial * (if j = 1 then 2
      else if j = 2 then 3 else if j = 3 then 5 else 0)) = 348 := by decide +kernel
  have hcast : (fun j => (j.factorial : ℚ) * ((fun j => if j = 1 then 2 else if j = 2 then 3
      else if j = 3 then 5 else 0) j : ℕ)) = fun j => ((j.factorial * (if j = 1 then 2
      else if j = 2 then 3 else if j = 3 then 5 else 0) : ℕ) : ℚ) := by
    ext j
    push_cast
    rfl
  rw [hcast, partialBellPolynomial_natCast, hB] at h
  norm_num [Nat.choose, Nat.factorial] at h
  exact_mod_cast h

-- A triangle has no diagonal. For `k = n + 1` the partial Bell polynomial `B_{1,2}` is an empty
-- sum, so the formula says that no triangle is cut into two polygons, whatever the colors.
example (γ : ℕ → ℕ) : coloredPolygonDissectionCount γ 1 2 = 0 := by
  have h := coloredPolygonDissectionCount_eq_partialBell γ (n := 1) (k := 2) le_rfl (by norm_num)
  have hB : partialBellPolynomial 1 2 (fun j => (j.factorial : ℚ) * γ j) = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    simp [Fin.sum_univ_two] at hm
    omega
  rw [hB, mul_zero] at h
  exact_mod_cast h

-- As the source remarks, this formula and the Mansour–Sun formula for Dyck paths give
-- `C(n+k, k) d_{n,k}(γ) = C(n+1, k) p_{n,k}(γ)` for `1 ≤ k ≤ n`.
example (γ : ℕ → ℕ) {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((n + k).choose k : ℚ) * coloredDyckPathCount γ n k =
      ((n + 1).choose k : ℚ) * coloredPolygonDissectionCount γ n k := by
  have hn : 1 ≤ n := hk.trans hkn
  rw [coloredDyckPathCount_eq_partialBell γ hn,
    coloredPolygonDissectionCount_eq_partialBell γ hn hk]
  have hf : ((n + 1).choose k : ℚ) * k.factorial * (n + 1 - k).factorial =
      (n + 1) * n.factorial := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial (by omega : k ≤ n + 1)).trans
      (Nat.factorial_succ n)
  have h₁ : ((n + 1 - k).factorial : ℚ) ≠ 0 := by positivity
  have h₂ : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  linear_combination ((n + k).choose k : ℚ) *
    partialBellPolynomial n k (fun j => (j.factorial : ℚ) * γ j) * hf.symm
