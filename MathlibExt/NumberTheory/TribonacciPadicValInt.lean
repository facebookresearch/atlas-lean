/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import MathlibExt.NumberTheory.TribonacciInt
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Ring.Periodic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic.FinCases

/-!
# The 47-adic valuation of Tribonacci numbers near ±1

`tribonacci_padicValInt_fortySeven` determines the valuation on five residue classes
modulo 46 and excludes all other classes.
-/

namespace MetaMathlibExt
namespace tribonacci_padicValInt_fortySeven

open Matrix Polynomial

private abbrev Mat := Matrix (Fin 3) (Fin 3) ℤ

private def companion : Mat := !![0, 1, 0; 0, 0, 1; 1, 1, 1]

private def state (n : ℤ) : Fin 3 → ℤ :=
  ![tribonacciInt n, tribonacciInt (n + 1), tribonacciInt (n + 2)]

private theorem state_step (n : ℤ) : state (n + 1) = companion *ᵥ state n := by
  ext i
  fin_cases i <;> simp [companion, state, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    show n + 1 + 1 = n + 2 by omega, show n + 1 + 2 = n + 3 by omega, tribonacciInt_add_three]
  abel

private theorem state_shift (n : ℤ) (d : ℕ) :
    state (n + d) = companion ^ d *ᵥ state n := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.cast_succ, ← add_assoc, state_step, ih, mulVec_mulVec, pow_succ']

-- The first-order part of the 46-step shift.
private def slopeMatrix : Mat := (companion ^ 46 - 1).map (· / 47)

set_option maxRecDepth 8192 in
private theorem companion_period : companion ^ 46 = 1 + (47 : ℤ) • slopeMatrix := by
  decide

private def slope (n : ℤ) : ℤ := (slopeMatrix *ᵥ state n) 0

-- Lift the period in the commutative polynomial ring, then evaluate at the slope matrix.
private theorem lifted_period (k : ℕ) : ∃ C : Mat,
    (companion ^ 46) ^ (47 ^ k) =
      1 + ((47 : ℤ) ^ (k + 1)) • (slopeMatrix + (47 : ℤ) • C) := by
  obtain ⟨f, hf⟩ := ZMod.exists_one_add_mul_pow_prime_pow_eq (R := ℤ[X])
    (p := 47) (u := 47) (v := 47) (by decide) (dvd_refl _)
    (by
      convert pow_dvd_pow (47 : ℤ[X]) (by decide : 3 ≤ 47) using 1
      norm_num) X k
  refine ⟨aeval slopeMatrix f, ?_⟩
  have h := congrArg (aeval slopeMatrix) hf
  simp only [map_pow, map_add, map_mul, map_ofNat, map_one, aeval_X, Nat.cast_ofNat] at h
  rw [companion_period]
  simpa only [zsmul_eq_mul, Int.cast_ofNat, Int.cast_pow, Int.cast_mul, pow_succ] using h

private theorem state_period_step (n : ℤ) :
    state (n + 46) = state n + (47 : ℤ) • (slopeMatrix *ᵥ state n) := by
  simpa only [Nat.cast_ofNat, companion_period, add_mulVec, one_mulVec, smul_mulVec]
    using state_shift n 46

private theorem value_periodic : Function.Periodic (fun n => tribonacciInt n % 47) 46 := by
  intro n
  have h := congrFun (state_period_step n) 0
  change tribonacciInt (n + 46) = tribonacciInt n + 47 * slope n at h
  simp [h]

private theorem slope_periodic : Function.Periodic (fun n => slope n % 47) 46 := by
  intro n
  simp only [slope, state_period_step, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply]
  simp

private theorem lifted_step (n : ℤ) (k : ℕ) : ∃ z : ℤ,
    tribonacciInt (n + 46 * 47 ^ k) =
      tribonacciInt n + 47 ^ (k + 1) * (slope n + 47 * z) := by
  obtain ⟨C, hC⟩ := lifted_period k
  refine ⟨(C *ᵥ state n) 0, ?_⟩
  have h := state_shift n (46 * 47 ^ k)
  rw [pow_mul, hC, add_mulVec, one_mulVec, smul_mulVec, add_mulVec, smul_mulVec] at h
  push_cast at h
  exact congrFun h 0

-- Subtracting the linear term gives a periodic function of the signed multiplier.
private theorem lifted_multiple (j s : ℤ) (k : ℕ) : ∃ z : ℤ,
    tribonacciInt (46 * (47 ^ k * s) + j) - tribonacciInt j =
      47 ^ (k + 1) * (s * slope j + 47 * z) := by
  let d : ℤ := 46 * 47 ^ k
  let c : ℤ := 47 ^ (k + 1)
  let f (i : ℤ) := (tribonacciInt (j + i * d) - c * i * slope j) % (47 * c)
  have per : Function.Periodic f 1 := by
    intro i
    obtain ⟨z, hz⟩ := lifted_step (j + i * d) k
    change tribonacciInt (j + i * d + d) =
      tribonacciInt (j + i * d) + c * (slope (j + i * d) + 47 * z) at hz
    have hs := slope_periodic.int_mul (i * 47 ^ k) j
    simp only [Int.cast_id] at hs
    rw [show i * 47 ^ k * 46 = i * d by dsimp [d]; ring] at hs
    obtain ⟨w, hw⟩ := Int.modEq_iff_dvd.mp (Int.ModEq.symm hs)
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-(w + z), ?_⟩
    rw [show (i + 1) * d = i * d + d by ring, ← add_assoc, hz]
    linear_combination -c * hw
  have hs := per.int_mul_eq s
  simp only [mul_one, f, zero_mul, mul_zero, sub_zero, add_zero] at hs
  obtain ⟨z, hz⟩ := Int.modEq_iff_dvd.mp (Int.ModEq.symm hs)
  refine ⟨z, ?_⟩
  rw [show 46 * (47 ^ k * s) + j = j + s * d by dsimp [d]; ring]
  change _ = c * _
  linear_combination hz

private abbrev indices : Finset ℤ := {1, 2, -2, -3, -7}

set_option maxRecDepth 8192 in
private theorem slope_unit (j : ℤ) (hj : j ∈ indices) : ¬ (47 : ℤ) ∣ slope j := by
  fin_cases hj <;> decide

private theorem valuation (j : ℤ) (hj : j ∈ indices) (r : ℤ) (hr : r ≠ 0) :
    padicValInt 47 (tribonacciInt (46 * r + j) - tribonacciInt j) =
      1 + padicValInt 47 r := by
  have hp : Fact (Nat.Prime 47) := ⟨by decide⟩
  let k := padicValInt 47 r
  obtain ⟨s, hs⟩ := padicValInt_dvd (p := 47) r
  change r = 47 ^ k * s at hs
  have hu : ¬ (47 : ℤ) ∣ s := by
    rintro ⟨t, ht⟩
    have hd : (47 : ℤ) ^ (k + 1) ∣ r := ⟨t, by rw [hs, ht, pow_succ, mul_assoc]⟩
    have hk := ((padicValInt_dvd_iff_of_ne_one (p := 47) (by decide) _ _).mp hd).resolve_left hr
    exact (Nat.not_succ_le_self k) hk
  obtain ⟨z, hz⟩ := lifted_multiple j s k
  rw [← hs] at hz
  let u := s * slope j + 47 * z
  have hprime : Prime (47 : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hunit : ¬ (47 : ℤ) ∣ u := by
    intro h
    have hd : (47 : ℤ) ∣ s * slope j := (dvd_add_left (dvd_mul_right 47 z)).mp h
    exact (hprime.dvd_or_dvd hd).elim hu (slope_unit j hj)
  change _ = 47 ^ (k + 1) * u at hz
  have hu0 : u ≠ 0 := fun h => hunit (h ▸ dvd_zero _)
  rw [hz, padicValInt.mul (by positivity) hu0, padicValInt.eq_zero_of_not_dvd hunit, add_zero]
  change padicValInt 47 ((47 : ℤ) ^ (k + 1)) = 1 + k
  rw [Nat.add_comm 1 k, padicValInt, Int.natAbs_pow]
  exact Nat.multiplicity_prime_pow (p := 47) (k + 1)

private theorem residue_table : ∀ i : Fin 46,
    tribonacciInt (i : ℕ) % 47 = 1 ∨ tribonacciInt (i : ℕ) % 47 = 46 →
      (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 39 ∨ (i : ℕ) = 43 ∨ (i : ℕ) = 44 := by
  decide

private theorem other_classes (n : ℤ) (hn : ∀ j ∈ indices, ∀ r : ℤ, n ≠ 46 * r + j) :
    ¬ (47 : ℤ) ∣ tribonacciInt n - 1 ∧ ¬ (47 : ℤ) ∣ tribonacciInt n + 1 := by
  let i : Fin 46 := ⟨(n % 46).toNat, by omega⟩
  have hi : ((i : ℕ) : ℤ) = n % 46 := by dsimp [i]; omega
  have hp := value_periodic.int_mul (n / 46) (n % 46)
  have hperiod : tribonacciInt n % 47 = tribonacciInt (i : ℕ) % 47 := by
    simpa only [hi, Int.cast_id, show n % 46 + n / 46 * 46 = n by omega] using hp
  have h1 := hn 1 (by decide) (n / 46)
  have h2 := hn 2 (by decide) (n / 46)
  have hnegSeven := hn (-7) (by decide) (n / 46 + 1)
  have hnegThree := hn (-3) (by decide) (n / 46 + 1)
  have hnegTwo := hn (-2) (by decide) (n / 46 + 1)
  have hres : ¬ (tribonacciInt n % 47 = 1 ∨ tribonacciInt n % 47 = 46) := by
    rw [hperiod]
    intro h
    have := residue_table i h
    omega
  constructor <;> omega

end tribonacci_padicValInt_fortySeven

/--
**The $47$-adic valuation of Tribonacci numbers near $\pm 1$.** Let $(T_n)_{n \in \mathbb{Z}}$
be the two-sided Tribonacci sequence, determined by $T_0 = 0$, $T_1 = T_2 = 1$ and
$T_{n+3} = T_{n+2} + T_{n+1} + T_n$ for all integers $n$. Let $\nu_{47}$ be the $47$-adic
valuation on the integers, with the convention $\nu_{47}(0) = 0$, and let
$J = \{1, 2, -2, -3, -7\}$. First, $T_j = 1$ or $T_j = -1$ for every $j \in J$. Second, for every
$j \in J$ and every nonzero integer $r$, $\nu_{47}(T_{46r+j} - T_j) = 1 + \nu_{47}(r)$. Third, for
every integer $n$ that is not of the form $46r + j$ with $j \in J$ and $r \in \mathbb{Z}$, neither
$T_n - 1$ nor $T_n + 1$ is divisible by $47$.

The condition $r \ne 0$ is needed because $\nu_{47}(0)$ is $0$ here, whereas the paper uses an
infinite valuation at $0$.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci
Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public theorem tribonacci_padicValInt_fortySeven :
    (∀ j ∈ ({1, 2, -2, -3, -7} : Finset ℤ),
      tribonacciInt j = 1 ∨ tribonacciInt j = -1) ∧
    (∀ j ∈ ({1, 2, -2, -3, -7} : Finset ℤ), ∀ r : ℤ, r ≠ 0 →
      padicValInt 47 (tribonacciInt (46 * r + j) - tribonacciInt j) =
        1 + padicValInt 47 r) ∧
    (∀ n : ℤ,
      (∀ j ∈ ({1, 2, -2, -3, -7} : Finset ℤ), ∀ r : ℤ, n ≠ 46 * r + j) →
        ¬ (47 : ℤ) ∣ tribonacciInt n - 1 ∧ ¬ (47 : ℤ) ∣ tribonacciInt n + 1) := by
  refine ⟨?_, tribonacci_padicValInt_fortySeven.valuation,
    tribonacci_padicValInt_fortySeven.other_classes⟩
  intro j hj
  fin_cases hj <;> decide

end MetaMathlibExt
