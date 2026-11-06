/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 2, Corollary 1

For `f` analytic on a disc of radius `R > 1` and `z` not a nonpositive integer, the series
`∑ f⁽ᵏ⁾(0) / ((z + k) k!)` and `∑ (-1)ᵏ f⁽ᵏ⁾(1) / (z (z + 1) ⋯ (z + k))` have the same sum,
provided the double series obtained by expanding each `f⁽ʲ⁾(1)` in its Taylor series at `0`
is summable.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry2Corollary1DerivativeSeries

private theorem aux_prod_ne {z : ℂ} (hz : ∀ n : ℕ, z + (n : ℂ) ≠ 0) (j : ℕ) :
    (Finset.range (j + 1)).prod (fun k => z + (k : ℂ)) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => hz i)

private theorem aux_natA {n : ℕ} (j : ℕ) (hjle : j ≤ n) :
    (Nat.choose (n + 1) j : ℂ) * ((Nat.factorial j : ℂ) * ((n + 1 - j : ℕ) : ℂ)) =
      ((n + 1 : ℕ) : ℂ) * ((Nat.choose n j : ℂ) * (Nat.factorial j : ℂ)) := by
  have h1 : j ≤ n + 1 := by omega
  have e1 := Nat.choose_mul_factorial_mul_factorial h1
  have e2 := Nat.choose_mul_factorial_mul_factorial hjle
  have hfact : (n + 1 - j).factorial = (n + 1 - j) * (n - j).factorial := by
    have hsub : n + 1 - j = (n - j) + 1 := by omega
    rw [hsub, Nat.factorial_succ]
  have hfact2 : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n :=
    Nat.factorial_succ n
  rw [hfact, hfact2] at e1
  have e1c : ((Nat.choose (n + 1) j : ℂ) * (Nat.factorial j : ℂ)) *
      ((((n + 1 - j : ℕ)) : ℂ) * ((n - j).factorial : ℂ)) =
      ((n + 1 : ℕ) : ℂ) * (Nat.factorial n : ℂ) := by
    exact_mod_cast e1
  have e2c : ((Nat.choose n j : ℂ) * (Nat.factorial j : ℂ)) *
      ((n - j).factorial : ℂ) = (Nat.factorial n : ℂ) := by
    exact_mod_cast e2
  have hE : ((n - j).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  refine mul_right_cancel₀ hE ?_
  linear_combination e1c - ((n + 1 : ℕ) : ℂ) * e2c

private theorem aux_natB {n : ℕ} (i : ℕ) (hile : i ≤ n) :
    (Nat.choose (n + 1) (i + 1) : ℂ) * (Nat.factorial (i + 1) : ℂ) =
      ((n + 1 : ℕ) : ℂ) * ((Nat.choose n i : ℂ) * (Nat.factorial i : ℂ)) := by
  have h1 : i + 1 ≤ n + 1 := by omega
  have e1 := Nat.choose_mul_factorial_mul_factorial h1
  have e2 := Nat.choose_mul_factorial_mul_factorial hile
  have hsub : n + 1 - (i + 1) = n - i := by omega
  rw [hsub] at e1
  have hfact2 : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n :=
    Nat.factorial_succ n
  rw [hfact2] at e1
  have e1c : ((Nat.choose (n + 1) (i + 1) : ℂ) * (Nat.factorial (i + 1) : ℂ)) *
      ((n - i).factorial : ℂ) = ((n + 1 : ℕ) : ℂ) * (Nat.factorial n : ℂ) := by
    exact_mod_cast e1
  have e2c : ((Nat.choose n i : ℂ) * (Nat.factorial i : ℂ)) *
      ((n - i).factorial : ℂ) = (Nat.factorial n : ℂ) := by
    exact_mod_cast e2
  have hE : ((n - i).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  refine mul_right_cancel₀ hE ?_
  linear_combination e1c - ((n + 1 : ℕ) : ℂ) * e2c

private theorem aux_key {z : ℂ} (hz : ∀ n : ℕ, z + (n : ℂ) ≠ 0) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j *
      ((Nat.choose n j : ℂ) * ((Nat.factorial j : ℂ) /
        (Finset.range (j + 1)).prod (fun k => z + (k : ℂ)))) =
      1 / (z + (n : ℂ)) := by
  induction n with
  | zero =>
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        Finset.prod_range_succ, Finset.prod_empty, one_mul,
        pow_zero, Nat.choose_zero_right, Nat.cast_one, Nat.factorial_zero, Nat.cast_one]
  | succ n ih =>
      have hP : ∀ j : ℕ, (Finset.range (j + 1 + 1)).prod (fun k => z + (k : ℂ)) =
          (Finset.range (j + 1)).prod (fun k => z + (k : ℂ)) *
            (z + ((j + 1 : ℕ) : ℂ)) := by
        intro j
        rw [Finset.prod_range_succ]
      have hZ : ∀ i : ℕ, (z + ((i + 1 : ℕ) : ℂ)) /
          ((Finset.range (i + 1)).prod (fun k => z + (k : ℂ)) *
            (z + ((i + 1 : ℕ) : ℂ))) =
          1 / (Finset.range (i + 1)).prod (fun k => z + (k : ℂ)) := by
        intro i
        have h1 := aux_prod_ne hz i
        have h2 := hz (i + 1)
        field_simp
      have hA0 : (-1 : ℂ) ^ (0 : ℕ) * ((Nat.choose (n + 1) 0 : ℂ) *
          ((Nat.factorial 0 : ℂ) * ((z + ((0 : ℕ) : ℂ)) /
            (Finset.range (0 + 1)).prod (fun k => z + (k : ℂ))))) = 1 := by
        have hP0 : (Finset.range (0 + 1)).prod (fun k => z + (k : ℂ)) =
            z + ((0 : ℕ) : ℂ) := by
          simp
        rw [hP0]
        simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one,
          Nat.factorial_zero, Nat.cast_one]
        exact div_self (hz 0)
      have hAi : ∀ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ (i + 1) *
          ((Nat.choose (n + 1) (i + 1) : ℂ) * ((Nat.factorial (i + 1) : ℂ) *
            ((z + ((i + 1 : ℕ) : ℂ)) /
              (Finset.range (i + 1 + 1)).prod (fun k => z + (k : ℂ))))) =
          (-((n + 1 : ℕ) : ℂ)) * ((-1 : ℂ) ^ i * ((Nat.choose n i : ℂ) *
            ((Nat.factorial i : ℂ) /
              (Finset.range (i + 1)).prod (fun k => z + (k : ℂ))))) := by
        intro i hi
        have hile : i ≤ n := by
          have hlt : i < n + 1 := Finset.mem_range.mp hi
          omega
        have eB := aux_natB i hile
        have hPi := hP i
        have hZi := hZ i
        rw [hPi, hZi, pow_succ]
        calc ((-1 : ℂ) ^ i * -1) *
                ((Nat.choose (n + 1) (i + 1) : ℂ) *
                  ((Nat.factorial (i + 1) : ℂ) * (1 /
                    (Finset.range (i + 1)).prod (fun k => z + (k : ℂ))))) =
              -((((-1 : ℂ) ^ i) *
                (1 / (Finset.range (i + 1)).prod (fun k => z + (k : ℂ)))) *
                ((Nat.choose (n + 1) (i + 1) : ℂ) *
                  (Nat.factorial (i + 1) : ℂ))) := by
              ring
          _ = -((((-1 : ℂ) ^ i) *
                (1 / (Finset.range (i + 1)).prod (fun k => z + (k : ℂ)))) *
                (((n + 1 : ℕ) : ℂ) *
                  ((Nat.choose n i : ℂ) * (Nat.factorial i : ℂ)))) := by
              rw [eB]
          _ = (-((n + 1 : ℕ) : ℂ)) *
                ((-1 : ℂ) ^ i * ((Nat.choose n i : ℂ) *
                  ((Nat.factorial i : ℂ) /
                    (Finset.range (i + 1)).prod (fun k => z + (k : ℂ))))) := by
              ring
      have hBj : ∀ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j *
          ((Nat.choose (n + 1) j : ℂ) * ((Nat.factorial j : ℂ) *
            ((((n + 1 - j : ℕ)) : ℂ) /
              (Finset.range (j + 1)).prod (fun k => z + (k : ℂ))))) =
          ((n + 1 : ℕ) : ℂ) * ((-1 : ℂ) ^ j * ((Nat.choose n j : ℂ) *
            ((Nat.factorial j : ℂ) /
              (Finset.range (j + 1)).prod (fun k => z + (k : ℂ))))) := by
        intro j hj
        have hjle : j ≤ n := by
          have hlt : j < n + 1 := Finset.mem_range.mp hj
          omega
        have eA := aux_natA j hjle
        calc (-1 : ℂ) ^ j * ((Nat.choose (n + 1) j : ℂ) *
                ((Nat.factorial j : ℂ) * ((((n + 1 - j : ℕ)) : ℂ) /
                  (Finset.range (j + 1)).prod (fun k => z + (k : ℂ))))) =
              (((-1 : ℂ) ^ j) *
                (1 / (Finset.range (j + 1)).prod (fun k => z + (k : ℂ)))) *
                ((Nat.choose (n + 1) j : ℂ) *
                  ((Nat.factorial j : ℂ) * ((n + 1 - j : ℕ) : ℂ))) := by
              ring
          _ = (((-1 : ℂ) ^ j) *
                (1 / (Finset.range (j + 1)).prod (fun k => z + (k : ℂ)))) *
                (((n + 1 : ℕ) : ℂ) *
                  ((Nat.choose n j : ℂ) * (Nat.factorial j : ℂ))) := by
              rw [eA]
          _ = ((n + 1 : ℕ) : ℂ) * ((-1 : ℂ) ^ j * ((Nat.choose n j : ℂ) *
                ((Nat.factorial j : ℂ) /
                  (Finset.range (j + 1)).prod (fun k => z + (k : ℂ))))) := by
              ring
      have hsumA : (∑ j ∈ Finset.range (n + 1 + 1), (-1 : ℂ) ^ j *
          ((Nat.choose (n + 1) j : ℂ) * ((Nat.factorial j : ℂ) *
            ((z + ((j : ℕ) : ℂ)) /
              (Finset.range (j + 1)).prod (fun k => z + (k : ℂ)))))) =
          1 - ((n + 1 : ℕ) : ℂ) *
            (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i *
              ((Nat.choose n i : ℂ) * ((Nat.factorial i : ℂ) /
                (Finset.range (i + 1)).prod (fun k => z + (k : ℂ))))) := by
        have hpeel : (∑ j ∈ Finset.range (n + 1 + 1), (-1 : ℂ) ^ j *
            ((Nat.choose (n + 1) j : ℂ) * ((Nat.factorial j : ℂ) *
              ((z + ((j : ℕ) : ℂ)) /
                (Finset.range (j + 1)).prod (fun k => z + (k : ℂ)))))) =
            (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ (i + 1) *
              ((Nat.choose (n + 1) (i + 1) : ℂ) * ((Nat.factorial (i + 1) : ℂ) *
                ((z + (((i + 1 : ℕ)) : ℂ)) /
                  (Finset.range (i + 1 + 1)).prod (fun k => z + (k : ℂ)))))) +
              ((-1 : ℂ) ^ (0 : ℕ) * ((Nat.choose (n + 1) 0 : ℂ) *
                ((Nat.factorial 0 : ℂ) * ((z + ((0 : ℕ) : ℂ)) /
                  (Finset.range (0 + 1)).prod (fun k => z + (k : ℂ)))))) :=
          Finset.sum_range_succ' _ _
        rw [hpeel, hA0]
        have h1 : (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ (i + 1) *
            ((Nat.choose (n + 1) (i + 1) : ℂ) * ((Nat.factorial (i + 1) : ℂ) *
              ((z + (((i + 1 : ℕ)) : ℂ)) /
                (Finset.range (i + 1 + 1)).prod (fun k => z + (k : ℂ)))))) =
            (-((n + 1 : ℕ) : ℂ)) *
              (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i *
                ((Nat.choose n i : ℂ) * ((Nat.factorial i : ℂ) /
                  (Finset.range (i + 1)).prod (fun k => z + (k : ℂ))))) := by
          rw [Finset.sum_congr rfl (fun i hi => hAi i hi), ← Finset.mul_sum]
        rw [h1]
        ring
      have hsumB : (∑ j ∈ Finset.range (n + 1 + 1), (-1 : ℂ) ^ j *
          ((Nat.choose (n + 1) j : ℂ) * ((Nat.factorial j : ℂ) *
            ((((n + 1 - j : ℕ)) : ℂ) /
              (Finset.range (j + 1)).prod (fun k => z + (k : ℂ)))))) =
          ((n + 1 : ℕ) : ℂ) *
            (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i *
              ((Nat.choose n i : ℂ) * ((Nat.factorial i : ℂ) /
                (Finset.range (i + 1)).prod (fun k => z + (k : ℂ))))) := by
        have hpeel : (∑ j ∈ Finset.range (n + 1 + 1), (-1 : ℂ) ^ j *
            ((Nat.choose (n + 1) j : ℂ) * ((Nat.factorial j : ℂ) *
              ((((n + 1 - j : ℕ)) : ℂ) /
                (Finset.range (j + 1)).prod (fun k => z + (k : ℂ)))))) =
            (∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j *
              ((Nat.choose (n + 1) j : ℂ) * ((Nat.factorial j : ℂ) *
                ((((n + 1 - j : ℕ)) : ℂ) /
                  (Finset.range (j + 1)).prod (fun k => z + (k : ℂ)))))) +
              ((-1 : ℂ) ^ (n + 1) * ((Nat.choose (n + 1) (n + 1) : ℂ) *
                ((Nat.factorial (n + 1) : ℂ) *
                  ((((n + 1 - (n + 1) : ℕ)) : ℂ) /
                    (Finset.range (n + 1 + 1)).prod (fun k => z + (k : ℂ)))))) :=
          Finset.sum_range_succ _ _
        rw [hpeel]
        have hBlast : (-1 : ℂ) ^ (n + 1) * ((Nat.choose (n + 1) (n + 1) : ℂ) *
            ((Nat.factorial (n + 1) : ℂ) * ((((n + 1 - (n + 1) : ℕ)) : ℂ) /
              (Finset.range (n + 1 + 1)).prod (fun k => z + (k : ℂ))))) = 0 := by
          have hD0 : ((n + 1 - (n + 1) : ℕ) : ℂ) = 0 := by
            have hsub : n + 1 - (n + 1) = 0 := by omega
            exact_mod_cast hsub
          rw [hD0]
          simp
        rw [hBlast, add_zero]
        have h1 : (∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j *
            ((Nat.choose (n + 1) j : ℂ) * ((Nat.factorial j : ℂ) *
              ((((n + 1 - j : ℕ)) : ℂ) /
                (Finset.range (j + 1)).prod (fun k => z + (k : ℂ)))))) =
            ((n + 1 : ℕ) : ℂ) *
              (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i *
                ((Nat.choose n i : ℂ) * ((Nat.factorial i : ℂ) /
                  (Finset.range (i + 1)).prod (fun k => z + (k : ℂ))))) := by
          rw [Finset.sum_congr rfl (fun j hj => hBj j hj), ← Finset.mul_sum]
        exact h1
      have hsplit : ∀ j ∈ Finset.range (n + 1 + 1), (z + ((n + 1 : ℕ) : ℂ)) *
          ((-1 : ℂ) ^ j * ((Nat.choose (n + 1) j : ℂ) *
            ((Nat.factorial j : ℂ) /
              (Finset.range (j + 1)).prod (fun k => z + (k : ℂ))))) =
          ((-1 : ℂ) ^ j * ((Nat.choose (n + 1) j : ℂ) *
            ((Nat.factorial j : ℂ) * ((z + ((j : ℕ) : ℂ)) /
              (Finset.range (j + 1)).prod (fun k => z + (k : ℂ)))))) +
          ((-1 : ℂ) ^ j * ((Nat.choose (n + 1) j : ℂ) *
            ((Nat.factorial j : ℂ) * ((((n + 1 - j : ℕ)) : ℂ) /
              (Finset.range (j + 1)).prod (fun k => z + (k : ℂ)))))) := by
        intro j hj
        have hJD : ((n + 1 : ℕ) : ℂ) = ((j : ℕ) : ℂ) + ((n + 1 - j : ℕ) : ℂ) := by
          have h2 : j + (n + 1 - j) = n + 1 := by
            have hlt : j < n + 1 + 1 := Finset.mem_range.mp hj
            omega
          exact_mod_cast h2.symm
        rw [hJD]
        ring
      have hmul : (z + ((n + 1 : ℕ) : ℂ)) *
          (∑ j ∈ Finset.range (n + 1 + 1), (-1 : ℂ) ^ j *
            ((Nat.choose (n + 1) j : ℂ) * ((Nat.factorial j : ℂ) /
              (Finset.range (j + 1)).prod (fun k => z + (k : ℂ))))) = 1 := by
        have h1 : (z + ((n + 1 : ℕ) : ℂ)) *
            (∑ j ∈ Finset.range (n + 1 + 1), (-1 : ℂ) ^ j *
              ((Nat.choose (n + 1) j : ℂ) * ((Nat.factorial j : ℂ) /
                (Finset.range (j + 1)).prod (fun k => z + (k : ℂ))))) =
            (∑ j ∈ Finset.range (n + 1 + 1), (-1 : ℂ) ^ j *
              ((Nat.choose (n + 1) j : ℂ) * ((Nat.factorial j : ℂ) *
                ((z + ((j : ℕ) : ℂ)) /
                  (Finset.range (j + 1)).prod (fun k => z + (k : ℂ)))))) +
              (∑ j ∈ Finset.range (n + 1 + 1), (-1 : ℂ) ^ j *
                ((Nat.choose (n + 1) j : ℂ) * ((Nat.factorial j : ℂ) *
                  ((((n + 1 - j : ℕ)) : ℂ) /
                    (Finset.range (j + 1)).prod (fun k => z + (k : ℂ)))))) := by
          rw [Finset.mul_sum]
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j hj => hsplit j hj)
        rw [h1, hsumA, hsumB]
        ring
      have hzne : z + ((n + 1 : ℕ) : ℂ) ≠ 0 := hz (n + 1)
      have hfinal : (∑ j ∈ Finset.range (n + 1 + 1), (-1 : ℂ) ^ j *
          ((Nat.choose (n + 1) j : ℂ) * ((Nat.factorial j : ℂ) /
            (Finset.range (j + 1)).prod (fun k => z + (k : ℂ))))) *
          (z + ((n + 1 : ℕ) : ℂ)) = 1 := by
        rw [mul_comm]
        exact hmul
      exact (eq_div_iff hzne).mpr hfinal

private theorem aux_bridge {z : ℂ} (hz : ∀ n : ℕ, z + (n : ℂ) ≠ 0) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j /
      ((Finset.range (j + 1)).prod (fun k => z + (k : ℂ)) *
        ((n - j).factorial : ℂ)) =
      1 / ((z + (n : ℂ)) * (Nat.factorial n : ℂ)) := by
  have hkey := aux_key hz n
  have hN : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hper : ∀ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j /
      ((Finset.range (j + 1)).prod (fun k => z + (k : ℂ)) *
        ((n - j).factorial : ℂ)) =
        (((-1 : ℂ) ^ j * ((Nat.choose n j : ℂ) *
          ((Nat.factorial j : ℂ) /
            (Finset.range (j + 1)).prod (fun k => z + (k : ℂ))))) /
          (Nat.factorial n : ℂ)) := by
    intro j hj
    have hjle : j ≤ n := by
      have hlt : j < n + 1 := Finset.mem_range.mp hj
      omega
    have e := Nat.choose_mul_factorial_mul_factorial hjle
    have ec : ((Nat.choose n j : ℂ) * (Nat.factorial j : ℂ)) *
        ((n - j).factorial : ℂ) = (Nat.factorial n : ℂ) := by
      exact_mod_cast e
    have hPj := aux_prod_ne hz j
    have hE : ((n - j).factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    rw [eq_div_iff hN, div_mul_eq_mul_div, ← ec, mul_div_assoc,
      mul_div_mul_right _ _ hE]
    ring
  have hsum : (∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j /
      ((Finset.range (j + 1)).prod (fun k => z + (k : ℂ)) *
        ((n - j).factorial : ℂ))) =
      ((∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j *
        ((Nat.choose n j : ℂ) * ((Nat.factorial j : ℂ) /
          (Finset.range (j + 1)).prod (fun k => z + (k : ℂ)))))) /
        (Nat.factorial n : ℂ) := by
    rw [Finset.sum_congr rfl (fun j hj => hper j hj)]
    simp only [div_eq_inv_mul]
    rw [← Finset.mul_sum]
  rw [hsum, hkey, div_div]

private theorem aux_taylor {R : ℝ} {f : ℂ → ℂ}
    (hf : AnalyticOn ℂ f (Metric.ball (0 : ℂ) R))
    (hR : 1 < R) (j : ℕ) :
    HasSum (fun m : ℕ => iteratedDeriv (j + m) f (0 : ℂ) / (Nat.factorial m : ℂ))
      (iteratedDeriv j f (1 : ℂ)) := by
  have hg_an : AnalyticOn ℂ (deriv ^[j] f) (Metric.ball (0 : ℂ) R) := by
    intro x hx
    have hxnh : Metric.ball (0 : ℂ) R ∈ nhds x := Metric.isOpen_ball.mem_nhds hx
    have hfx : AnalyticAt ℂ f x := hf.analyticAt hxnh
    exact (hfx.iterated_deriv j).analyticWithinAt
  have hg_diff : DifferentiableOn ℂ (deriv ^[j] f) (Metric.ball (0 : ℂ) R) :=
    hg_an.differentiableOn
  have h1mem : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right, norm_one]
    exact hR
  have htaylor := Complex.hasSum_taylorSeries_on_ball hg_diff h1mem
  have hkey : ∀ m : ℕ, iteratedDeriv m (deriv ^[j] f) (0 : ℂ) =
      iteratedDeriv (j + m) f (0 : ℂ) := by
    intro m
    rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, add_comm j m,
      Function.iterate_add_apply]
  have hterm : ∀ m : ℕ, ((Nat.factorial m : ℂ))⁻¹ • (((1 : ℂ) - (0 : ℂ)) ^ m •
      iteratedDeriv m (deriv ^[j] f) (0 : ℂ)) =
      iteratedDeriv (j + m) f (0 : ℂ) / (Nat.factorial m : ℂ) := by
    intro m
    rw [hkey m, sub_zero, one_pow, one_smul, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hval : (deriv ^[j] f) (1 : ℂ) = iteratedDeriv j f (1 : ℂ) := by
    rw [iteratedDeriv_eq_iterate]
  rw [hval] at htaylor
  exact htaylor.congr_fun (fun m => (hterm m).symm)

private def sigmaProdEquiv : (Σ _ : ℕ, ℕ) ≃ ℕ × ℕ where
  toFun q := (q.1, q.2)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by
    intro q
    cases q
    rfl
  right_inv := by
    intro p
    cases p
    rfl

private def diagEquiv : (Σ n : ℕ, Fin (n + 1)) ≃ ℕ × ℕ where
  toFun q := (q.2.val, q.1 - q.2.val)
  invFun p := ⟨p.1 + p.2, p.1, by omega⟩
  left_inv := by
    rintro ⟨n, ⟨j, hj⟩⟩
    have hje : j + (n - j) = n := by omega
    change (⟨j + (n - j), (⟨j, by omega⟩ : Fin (j + (n - j) + 1))⟩ : Σ n : ℕ, Fin (n + 1)) =
      ⟨n, ⟨j, hj⟩⟩
    simp only [hje, Sigma.mk.injEq]
    have hIdx : j + (n - j) + 1 = n + 1 := by omega
    exact ⟨trivial, (Fin.heq_ext_iff hIdx).mpr rfl⟩
  right_inv := by
    rintro ⟨u, v⟩
    dsimp only
    rw [Nat.add_sub_cancel_left]

/-- **Two derivative series with the same sum (Chapter 3, Entry 2, Corollary 1).** Let $R > 1$, let
$f : \mathbb{C} \to \mathbb{C}$ be analytic on the open disc $|w| < R$, and let $z$ be a complex
number with $z + n \ne 0$ for every natural number $n$. Suppose that the double series
$\sum_{j, m \ge 0} \frac{(-1)^j}{z(z+1)\cdots(z+j)} \cdot \frac{f^{(j+m)}(0)}{m!}$ converges
absolutely. Then there is a complex number $c$ such that the series
$\sum_{k \ge 0} \frac{f^{(k)}(0)}{(z+k)\, k!}$ and
$\sum_{k \ge 0} \frac{(-1)^k f^{(k)}(1)}{z(z+1)\cdots(z+k)}$ both converge absolutely with sum $c$.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 2, Corollary 1, printed p.
    46 / PDF p. 56.
Proves `Wanted` entry `ramanujan_part1_ch3_entry2_corollary1_derivative_series`.
-/
theorem ramanujan_part1_ch3_entry2_corollary1_derivative_series (R : ℝ)
    (hR : 1 < R)
        (f : ℂ → ℂ)
            (hf : AnalyticOn ℂ f (Metric.ball (0 : ℂ) R))
                (z : ℂ)
                    (hz : ∀ n : ℕ, z + (n : ℂ) ≠ 0)
                        (hSumm : Summable (fun p : ℕ × ℕ => (-1 : ℂ) ^ p.1 /
                            (Finset.range (p.1 + 1)).prod (fun i => z + (i : ℂ)) *
                                (iteratedDeriv (p.1 + p.2) f (0 : ℂ) / (Nat.factorial p.2 : ℂ)))) :
    ∃ c : ℂ,
        HasSum (fun k : ℕ => iteratedDeriv k f (0 : ℂ) /
            ((z + (k : ℂ)) * (Nat.factorial k : ℂ))) c ∧
            HasSum (fun k : ℕ => (-1 : ℂ) ^ k * iteratedDeriv k f (1 : ℂ) /
                (Finset.range (k + 1)).prod (fun i => z + (i : ℂ))) c := by
  set S : ℕ × ℕ → ℂ := (fun p : ℕ × ℕ => (-1 : ℂ) ^ p.1 /
      (Finset.range (p.1 + 1)).prod (fun i => z + (i : ℂ)) *
          (iteratedDeriv (p.1 + p.2) f (0 : ℂ) / (Nat.factorial p.2 : ℂ))) with hSdef
  have hSummS : Summable S := by
    rw [hSdef]
    exact hSumm
  have hfib2 : ∀ j : ℕ, HasSum (fun m : ℕ => (S ∘ sigmaProdEquiv) ⟨j, m⟩)
      ((-1 : ℂ) ^ j * iteratedDeriv j f (1 : ℂ) /
        (Finset.range (j + 1)).prod (fun i => z + (i : ℂ))) := by
    intro j
    have ht := aux_taylor hf hR j
    have htm := ht.mul_left
      ((-1 : ℂ) ^ j / (Finset.range (j + 1)).prod (fun i => z + (i : ℂ)))
    have hv : ((-1 : ℂ) ^ j / (Finset.range (j + 1)).prod (fun i => z + (i : ℂ))) *
        iteratedDeriv j f (1 : ℂ) =
        (-1 : ℂ) ^ j * iteratedDeriv j f (1 : ℂ) /
          (Finset.range (j + 1)).prod (fun i => z + (i : ℂ)) := by
      ring
    rw [hv] at htm
    exact htm
  have hF : Summable (S ∘ sigmaProdEquiv) :=
    hSummS.comp_injective sigmaProdEquiv.injective
  have htot : (∑' q, (S ∘ sigmaProdEquiv) q) = ∑' p, S p :=
    sigmaProdEquiv.tsum_eq S
  have hsecond : HasSum (fun k : ℕ => (-1 : ℂ) ^ k * iteratedDeriv k f (1 : ℂ) /
      (Finset.range (k + 1)).prod (fun i => z + (i : ℂ))) (∑' p, S p) := by
    rw [← htot]
    exact HasSum.sigma hF.hasSum hfib2
  have hfun : ∀ (n : ℕ) (j : Fin (n + 1)), (S ∘ diagEquiv) ⟨n, j⟩ =
      (-1 : ℂ) ^ (j.val) / (Finset.range (j.val + 1)).prod (fun i => z + (i : ℂ)) *
        (iteratedDeriv n f (0 : ℂ) / (((n - j.val)).factorial : ℂ)) := by
    intro n j
    have hjle : j.val ≤ n := by
      have hlt : j.val < n + 1 := j.isLt
      omega
    have hadd : j.val + (n - j.val) = n := by omega
    change (-1 : ℂ) ^ ((⟨n, j⟩ : (Σ n : ℕ, Fin (n + 1))).2.val) /
        (Finset.range (((⟨n, j⟩ : (Σ n : ℕ, Fin (n + 1))).2.val) + 1)).prod
          (fun i => z + (i : ℂ)) *
        (iteratedDeriv (((⟨n, j⟩ : (Σ n : ℕ, Fin (n + 1))).2.val) +
          ((⟨n, j⟩ : (Σ n : ℕ, Fin (n + 1))).1 -
            ((⟨n, j⟩ : (Σ n : ℕ, Fin (n + 1))).2.val))) f (0 : ℂ) /
          (((⟨n, j⟩ : (Σ n : ℕ, Fin (n + 1))).1 -
            ((⟨n, j⟩ : (Σ n : ℕ, Fin (n + 1))).2.val)).factorial : ℂ)) =
      (-1 : ℂ) ^ (j.val) / (Finset.range (j.val + 1)).prod (fun i => z + (i : ℂ)) *
        (iteratedDeriv n f (0 : ℂ) / (((n - j.val)).factorial : ℂ))
    rw [hadd]
  have hfib1 : ∀ n : ℕ, HasSum (fun c : Fin (n + 1) => (S ∘ diagEquiv) ⟨n, c⟩)
      (iteratedDeriv n f (0 : ℂ) / ((z + (n : ℂ)) * (Nat.factorial n : ℂ))) := by
    intro n
    have h1 : (∑ j : Fin (n + 1), (S ∘ diagEquiv) ⟨n, j⟩) =
        ∑ m ∈ Finset.range (n + 1), (-1 : ℂ) ^ m /
          (Finset.range (m + 1)).prod (fun i => z + (i : ℂ)) *
          (iteratedDeriv n f (0 : ℂ) / (((n - m)).factorial : ℂ)) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun m => (-1 : ℂ) ^ m / (Finset.range (m + 1)).prod (fun i => z + (i : ℂ)) *
          (iteratedDeriv n f (0 : ℂ) / (((n - m)).factorial : ℂ))) (n + 1)]
      exact Finset.sum_congr rfl (fun j _ => hfun n j)
    have h2 : (∑ m ∈ Finset.range (n + 1), (-1 : ℂ) ^ m /
        (Finset.range (m + 1)).prod (fun i => z + (i : ℂ)) *
        (iteratedDeriv n f (0 : ℂ) / (((n - m)).factorial : ℂ))) =
        iteratedDeriv n f (0 : ℂ) *
          (∑ m ∈ Finset.range (n + 1), (-1 : ℂ) ^ m /
            ((Finset.range (m + 1)).prod (fun i => z + (i : ℂ)) *
              ((n - m).factorial : ℂ))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    have h3 := aux_bridge hz n
    have hval : (∑ j : Fin (n + 1), (S ∘ diagEquiv) ⟨n, j⟩) =
        iteratedDeriv n f (0 : ℂ) / ((z + (n : ℂ)) * (Nat.factorial n : ℂ)) := by
      rw [h1, h2, h3]
      ring
    rw [← hval]
    exact hasSum_fintype _
  have hD : Summable (S ∘ diagEquiv) :=
    hSummS.comp_injective diagEquiv.injective
  have htotD : (∑' q, (S ∘ diagEquiv) q) = ∑' p, S p :=
    diagEquiv.tsum_eq S
  have hfirst : HasSum (fun k : ℕ => iteratedDeriv k f (0 : ℂ) /
      ((z + (k : ℂ)) * (Nat.factorial k : ℂ))) (∑' p, S p) := by
    rw [← htotD]
    exact HasSum.sigma hD.hasSum hfib1
  exact ⟨∑' p, S p, hfirst, hsecond⟩

end Entry2Corollary1DerivativeSeries

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
