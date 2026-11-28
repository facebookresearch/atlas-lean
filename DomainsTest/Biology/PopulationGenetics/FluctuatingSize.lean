/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.FluctuatingSize

@[expose] public section

open Finset Real
open Domains.Biology.PopulationGenetics.FluctuatingSize

namespace DomainsTest.Biology.PopulationGenetics.FluctuatingSize

/-! ### The genealogy model on small instances -/

/-- One generation of a population of one diploid individual (two gene copies) per generation,
with no identity by descent in generation `0`: of the four parent maps, the two bijections keep
the two gene copies distinct, so `h 1 = 1 / 2 = (1 - 1 / 2) * h 0`. -/
example : nonIdentityProb (fun _ => 1) (fun _ _ => False) 1 = 1 / 2 := by
  unfold nonIdentityProb
  rw [show #{x : Genealogy (fun _ => 1) 1 × Fin (2 * 1) × Fin (2 * 1) |
      x.2.1 ≠ x.2.2 ∧ ¬IdenticalByDescent (fun _ => 1) (fun _ _ => False) x.1 x.2.1 x.2.2} = 4
    from by decide,
    show #{x : Genealogy (fun _ => 1) 1 × Fin (2 * 1) × Fin (2 * 1) | x.2.1 ≠ x.2.2} = 8
    from by decide]
  norm_num

/-- With no identity by descent in generation `0`, `h 0 = 1`, the starting value of
Felsenstein's (VI-39) and (VI-40). -/
theorem nonIdentityProb_zero_bot (N : ℕ → ℕ) (h : 1 ≤ N 0) :
    nonIdentityProb N (fun _ _ => False) 0 = 1 := by
  unfold nonIdentityProb
  rw [filter_congr (q := fun x : Genealogy N 0 × Fin (2 * N 0) × Fin (2 * N 0) => x.2.1 ≠ x.2.2)
    fun x _ => by simp [IdenticalByDescent, ancestor], div_self]
  have hpair : (((), (⟨0, by omega⟩ : Fin (2 * N 0)), (⟨1, by omega⟩ : Fin (2 * N 0))) :
      Genealogy N 0 × Fin (2 * N 0) × Fin (2 * N 0)) ∈
      univ.filter fun x : Genealogy N 0 × Fin (2 * N 0) × Fin (2 * N 0) => x.2.1 ≠ x.2.2 := by
    simp [Fin.ext_iff]
  exact_mod_cast (card_pos.mpr ⟨_, hpair⟩).ne'

/-- With no identity by descent in generation `0`, `h t = Φ t`: Felsenstein's (VI-40). -/
example (N : ℕ → ℕ) (hN : ∀ i, 1 ≤ N i) (t : ℕ) (ht : 1 ≤ t) :
    nonIdentityProb N (fun _ _ => False) t = nonIdentityFactor N t := by
  rw [(effectiveSize_fluctuating hN _ ht).2.1 t, nonIdentityProb_zero_bot N (hN 0), mul_one]

/-- Gene copies of generation `1` with the same parent are identical by descent, whatever the
identity by descent of generation `0`. -/
example (N : ℕ → ℕ) (R : Fin (2 * N 0) → Fin (2 * N 0) → Prop) (g : Genealogy N 1)
    (a b : Fin (2 * N 1)) (h : g.2 a = g.2 b) : IdenticalByDescent N R g a b :=
  Or.inl (by simp [ancestor, h])

/-! ### Constant size -/

/-- In a population of constant size `n`, `Φ t = (1 - 1 / (2 n)) ^ t`: Felsenstein's (VI-39). -/
example (n t : ℕ) : nonIdentityFactor (fun _ => n) t = (1 - 1 / (2 * (n : ℝ))) ^ t := by
  simp [nonIdentityFactor]

/-- The inbreeding effective size of a population of constant size `n ≥ 1` is `n`. -/
example (n t : ℕ) (hn : 1 ≤ n) (ht : 1 ≤ t) : inbreedingEffectiveSize (fun _ => n) t = n := by
  have h :=
    (effectiveSize_fluctuating (N := fun _ => n) (fun _ => hn) (fun _ _ => False) ht).2.2.2.2
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact ((h.1 n (by linarith)).mp (by simp [nonIdentityFactor])).symm

/-- The harmonic mean of a constant size `n` over `t ≥ 1` generations is `n`. -/
example (n t : ℕ) (hn : 1 ≤ n) (ht : 1 ≤ t) : harmonicMeanSize (fun _ => n) t = n := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have ht' : (t : ℝ) ≠ 0 := by positivity
  simp only [harmonicMeanSize, sum_const, card_range, nsmul_eq_mul]
  field_simp

/-! ### One generation and a two-generation bottleneck -/

/-- Over one generation, `N_e = N 0`. -/
example (N : ℕ → ℕ) (hN : ∀ i, 1 ≤ N i) : inbreedingEffectiveSize N 1 = N 0 := by
  have h := (effectiveSize_fluctuating hN (fun _ _ => False) le_rfl).2.2.2.2
  have hN0 : (1 : ℝ) ≤ N 0 := by exact_mod_cast hN 0
  exact ((h.1 (N 0) (by linarith)).mp (by simp [nonIdentityFactor])).symm

/-- Sizes `1` then `3`: the harmonic mean is `3 / 2`, below the geometric mean `√3` and the
arithmetic mean `2`. -/
example : harmonicMeanSize (fun i => if i = 0 then 1 else 3) 2 = 3 / 2 := by
  norm_num [harmonicMeanSize, sum_range_succ]

/-- For sizes `1` then `3`, the factor `Φ 2 = 1 / 2 * 5 / 6` lies between `exp (-E)` and `1`
times `(1 - 1 / (2 N_H)) ^ 2 = (2 / 3) ^ 2`, with `E = 1 / 4 + 1 / 36`. -/
example :
    nonIdentityFactor (fun i => if i = 0 then 1 else 3) 2 / (1 - 1 / (2 * (3 / 2 : ℝ))) ^ 2 ∈
      Set.Icc (exp (-(1 / 4 + 1 / 36))) 1 := by
  have h := (effectiveSize_fluctuating (N := fun i => if i = 0 then 1 else 3)
    (fun i => by split_ifs <;> norm_num) (fun _ _ => False) (t := 2) (by norm_num)).2.2.2.2.2.2.2.1
  have hH : harmonicMeanSize (fun i => if i = 0 then 1 else 3) 2 = 3 / 2 := by
    norm_num [harmonicMeanSize, sum_range_succ]
  rw [hH] at h
  convert h using 3
  norm_num [sum_range_succ]

end DomainsTest.Biology.PopulationGenetics.FluctuatingSize
