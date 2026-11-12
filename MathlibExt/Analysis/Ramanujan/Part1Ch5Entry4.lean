/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 4

Eulerian polynomial: Ψₙ(p)/(p+1)ⁿ⁺¹ equals Σ(k+1)ⁿ(-p)ᵏ.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch5

namespace Entry4

open scoped Nat Real BigOperators Interval Polynomial
open Asymptotics Filter Finset Complex Topology

noncomputable section

def chapter5Entry4Term (n : ℕ) (p : ℂ) (k : ℕ) : ℂ :=
  (k + 1 : ℂ) ^ n * (-p) ^ k

def eulerianNumber : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k =>
      (k + 1) * eulerianNumber n k +
        (n + 1 - k) *
          (if k = 0 then 0 else eulerianNumber n (k - 1))

def chapter5Psi {R : Type*} [CommRing R] (n : ℕ) (p : R) : R :=
  if n = 0 then 1
  else ∑ k ∈ range n, (eulerianNumber n k : R) * (-p) ^ k

private lemma eulerian_succ_ge : ∀ (n j : ℕ), eulerianNumber (n+1) (n+1+j) = 0 := by
  intro n
  induction n with
  | zero =>
    intro j
    cases j with
    | zero => simp [eulerianNumber]
    | succ j => simp [eulerianNumber]
  | succ n ih =>
    intro j
    have h1' : eulerianNumber (n+1) (n+1+1+j) = 0 := by
      have h := ih (j+1)
      convert h using 2
      omega
    have h2 : eulerianNumber (n+1+1) (n+1+1+j)
        = (n+1+1+j+1) * eulerianNumber (n+1) (n+1+1+j)
          + (n+1+1-(n+1+1+j)) * (if n+1+1+j = 0 then 0 else eulerianNumber (n+1) (n+1+1+j-1)) := by
      simp only [eulerianNumber]
    have hC : n + 1 + 1 - (n + 1 + 1 + j) = 0 := by omega
    rw [h2, hC, zero_mul, add_zero, h1', mul_zero]

private lemma choose_succ_right_ℂ (a N : ℕ) :
    ((a.choose (N+1) : ℕ) : ℂ) * ((N + 1 : ℕ) : ℂ)
      = ((a.choose N : ℕ) : ℂ) * (((a : ℕ) : ℂ) - ((N : ℕ) : ℂ)) := by
  have hnat : a.choose (N+1) * (N+1) = a.choose N * (a - N) :=
    Nat.choose_succ_right_eq a N
  have h2 : ((((a.choose (N+1) * (N+1) : ℕ))) : ℂ)
      = ((((a.choose N * (a - N) : ℕ))) : ℂ) := by
    exact_mod_cast hnat
  push_cast at h2 ⊢
  by_cases hle : N ≤ a
  · have hsub : ((((a - N : ℕ))) : ℂ) = (((a : ℕ) : ℂ) - ((N : ℕ) : ℂ)) :=
      Nat.cast_sub hle
    rw [hsub] at h2
    exact h2
  · have h1 : a.choose N = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h3 : a.choose (N+1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h1, h3]

private lemma key_id (k m N : ℕ) (hm : m ≤ N) :
    ((k + 1 : ℕ) : ℂ) * ((((k + (N - m)).choose N : ℕ)) : ℂ)
      = (((m + 1 : ℕ)) : ℂ) * ((((k + (N - m)).choose N : ℕ)) : ℂ)
        + (((N + 1 : ℕ)) : ℂ) * ((((k + (N - m)).choose (N+1) : ℕ)) : ℂ) := by
  have hcast : ((((k + (N - m) : ℕ))) : ℂ)
      = ((k : ℕ) : ℂ) + ((N : ℕ) : ℂ) - ((m : ℕ) : ℂ) := by
    have heq : k + (N - m) = k + N - m := by omega
    have hm2 : m ≤ k + N := by omega
    have hsub2 : ((((k + N - m : ℕ))) : ℂ)
        = ((((k + N : ℕ))) : ℂ) - (((m : ℕ)) : ℂ) :=
      Nat.cast_sub hm2
    rw [heq, hsub2]
    push_cast
    ring
  have hchoice := choose_succ_right_ℂ (k + (N - m)) N
  have hkk : (((k + 1 : ℕ)) : ℂ)
      = (((m + 1 : ℕ)) : ℂ) + (((((k + (N - m) : ℕ))) : ℂ) - ((N : ℕ) : ℂ)) := by
    rw [hcast]
    push_cast
    ring
  calc ((k + 1 : ℕ) : ℂ) * (((k + (N - m)).choose N : ℕ) : ℂ)
      = (((m + 1 : ℕ) : ℂ) + (((((k + (N - m) : ℕ))) : ℂ) - ((N : ℕ) : ℂ)))
          * ((((k + (N - m)).choose N : ℕ)) : ℂ) := by
        rw [← hkk]
    _ = (((m + 1 : ℕ)) : ℂ) * ((((k + (N - m)).choose N : ℕ)) : ℂ)
        + (((N + 1 : ℕ)) : ℂ) * ((((k + (N - m)).choose (N+1) : ℕ)) : ℂ) := by
        have hcc : (((((k + (N - m) : ℕ))) : ℂ) - ((N : ℕ) : ℂ))
              * ((((k + (N - m)).choose N : ℕ)) : ℂ)
            = ((((N + 1 : ℕ))) : ℂ) * ((((k + (N - m)).choose (N+1) : ℕ)) : ℂ) := by
          linear_combination -hchoice
        rw [add_mul, hcc]

private lemma key_id_cast (k m N : ℕ) (hm : m ≤ N) :
    (↑(k + 1) : ℂ) * (↑((k + (N - m)).choose N) : ℂ)
      = (↑(m + 1) : ℂ) * (↑((k + (N - m)).choose N) : ℂ)
        + (↑(N + 1) : ℂ) * (↑((k + (N - m)).choose (N + 1)) : ℂ) :=
  key_id k m N hm

private lemma coeff_add (m n : ℕ) (hm : m ≤ n + 1) :
    (↑(m + 1) : ℂ) + (↑(n + 1 - m) : ℂ) = (↑(n + 1 + 1) : ℂ) := by
  have hnat : m + 1 + (n + 1 - m) = n + 1 + 1 := by omega
  exact_mod_cast hnat

private lemma eulerian_expand (n m : ℕ) :
    (↑(eulerianNumber (n + 1 + 1) m) : ℂ)
      = (↑(m + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
        + (↑(n + 1 + 1 - m) : ℂ)
          * (if m = 0 then (0 : ℂ) else (↑(eulerianNumber (n + 1) (m - 1)) : ℂ)) := by
  have hnat : eulerianNumber (n + 1 + 1) m
      = (m + 1) * eulerianNumber (n + 1) m
        + (n + 1 + 1 - m) * (if m = 0 then 0 else eulerianNumber (n + 1) (m - 1)) := by
    simp only [eulerianNumber]
  exact_mod_cast hnat

private lemma pascal_cast (n k m : ℕ) (hm : m ≤ n + 1) :
    (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ)
      = (↑((k + (n + 1) - m).choose (n + 1)) : ℂ)
        + (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ) := by
  have htop : k + (n + 1 + 1) - m = (k + (n + 1) - m) + 1 := by omega
  have h := Nat.choose_succ_succ (k + (n + 1) - m) (n + 1)
  rw [htop]
  exact_mod_cast h

private lemma worp_step (n k : ℕ) :
    ((↑k + 1 : ℂ)) * (∑ m ∈ Finset.range (n + 1),
      (↑(eulerianNumber (n + 1) m) : ℂ) * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ))
    = ∑ m ∈ Finset.range (n + 1 + 1),
      (↑(eulerianNumber (n + 1 + 1) m) : ℂ)
        * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ) := by
  have hk : ((↑k + 1 : ℂ)) = (↑(k + 1) : ℂ) := by push_cast; ring
  have hterm : ∀ m ∈ Finset.range (n + 1),
      (↑(k + 1) : ℂ) * ((↑(eulerianNumber (n + 1) m) : ℂ)
        * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ))
      = (↑(m + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
          * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ)
        + (↑(n + 1 + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
          * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ) := by
    intro m hm
    have hmle : m ≤ n + 1 := by
      have hmem := Finset.mem_range.mp hm
      omega
    have hform : k + (n + 1 - m) = k + (n + 1) - m := by omega
    have hkey := key_id_cast k m (n + 1) hmle
    rw [hform] at hkey
    calc (↑(k + 1) : ℂ) * ((↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ))
        = (↑(eulerianNumber (n + 1) m) : ℂ) * ((↑(k + 1) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ)) := by ring
      _ = (↑(eulerianNumber (n + 1) m) : ℂ) * ((↑(m + 1) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ)
            + (↑(n + 1 + 1) : ℂ) * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)) := by
          rw [hkey]
      _ = (↑(m + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ)
          + (↑(n + 1 + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ) := by ring
  have hA : (↑(k + 1) : ℂ) * (∑ m ∈ Finset.range (n + 1),
        (↑(eulerianNumber (n + 1) m) : ℂ) * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ))
      = (∑ m ∈ Finset.range (n + 1), (↑(m + 1) : ℂ)
          * (↑(eulerianNumber (n + 1) m) : ℂ)
          * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ))
        + (∑ m ∈ Finset.range (n + 1), (↑(n + 1 + 1) : ℂ)
          * (↑(eulerianNumber (n + 1) m) : ℂ)
          * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)) := by
    calc (↑(k + 1) : ℂ) * (∑ m ∈ Finset.range (n + 1),
            (↑(eulerianNumber (n + 1) m) : ℂ) * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ))
        = ∑ m ∈ Finset.range (n + 1), ((↑(m + 1) : ℂ)
            * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ)
          + (↑(n + 1 + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl hterm
      _ = (∑ m ∈ Finset.range (n + 1), (↑(m + 1) : ℂ)
            * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ))
          + (∑ m ∈ Finset.range (n + 1), (↑(n + 1 + 1) : ℂ)
            * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)) :=
          Finset.sum_add_distrib
  have e1 : (∑ m ∈ Finset.range (n + 1 + 1),
      (↑(eulerianNumber (n + 1 + 1) m) : ℂ)
        * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ))
    = (∑ m ∈ Finset.range (n + 1 + 1), (↑(m + 1) : ℂ)
        * (↑(eulerianNumber (n + 1) m) : ℂ)
        * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ))
      + (∑ m ∈ Finset.range (n + 1 + 1), (↑(n + 1 + 1 - m) : ℂ)
        * (if m = 0 then (0 : ℂ) else (↑(eulerianNumber (n + 1) (m - 1)) : ℂ))
        * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ)) := by
    have hpt : ∀ m ∈ Finset.range (n + 1 + 1),
        (↑(eulerianNumber (n + 1 + 1) m) : ℂ)
          * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ)
        = ((↑(m + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ)
          + (↑(n + 1 + 1 - m) : ℂ)
            * (if m = 0 then (0 : ℂ) else (↑(eulerianNumber (n + 1) (m - 1)) : ℂ))
            * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ)) := by
      intro m hm
      have he := eulerian_expand n m
      calc (↑(eulerianNumber (n + 1 + 1) m) : ℂ)
              * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ)
          = ((↑(m + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
              + (↑(n + 1 + 1 - m) : ℂ)
                * (if m = 0 then (0 : ℂ) else (↑(eulerianNumber (n + 1) (m - 1)) : ℂ)))
            * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ) := by
            rw [he]
        _ = ((↑(m + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
              * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ)
            + (↑(n + 1 + 1 - m) : ℂ)
              * (if m = 0 then (0 : ℂ) else (↑(eulerianNumber (n + 1) (m - 1)) : ℂ))
              * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ)) := by
            ring
    calc (∑ m ∈ Finset.range (n + 1 + 1),
            (↑(eulerianNumber (n + 1 + 1) m) : ℂ)
              * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ))
        = ∑ m ∈ Finset.range (n + 1 + 1), ((↑(m + 1) : ℂ)
            * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ)
          + (↑(n + 1 + 1 - m) : ℂ)
            * (if m = 0 then (0 : ℂ) else (↑(eulerianNumber (n + 1) (m - 1)) : ℂ))
            * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ)) :=
          Finset.sum_congr rfl hpt
      _ = (∑ m ∈ Finset.range (n + 1 + 1), (↑(m + 1) : ℂ)
            * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ))
          + (∑ m ∈ Finset.range (n + 1 + 1), (↑(n + 1 + 1 - m) : ℂ)
            * (if m = 0 then (0 : ℂ) else (↑(eulerianNumber (n + 1) (m - 1)) : ℂ))
            * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ)) :=
          Finset.sum_add_distrib
  have hlast : (↑(n + 1 + 1) : ℂ) * (↑(eulerianNumber (n + 1) (n + 1)) : ℂ)
      * (↑((k + (n + 1 + 1) - (n + 1)).choose (n + 1 + 1)) : ℂ) = 0 := by
    have hz : eulerianNumber (n + 1) (n + 1) = 0 := by
      have h := eulerian_succ_ge n 0
      simpa using h
    rw [hz]
    simp
  have e2 : (∑ m ∈ Finset.range (n + 1 + 1), (↑(m + 1) : ℂ)
        * (↑(eulerianNumber (n + 1) m) : ℂ)
        * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ))
      = (∑ m ∈ Finset.range (n + 1), (↑(m + 1) : ℂ)
        * (↑(eulerianNumber (n + 1) m) : ℂ)
        * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ))
      + (∑ m ∈ Finset.range (n + 1), (↑(m + 1) : ℂ)
        * (↑(eulerianNumber (n + 1) m) : ℂ)
        * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)) := by
    have hpeel : (∑ m ∈ Finset.range (n + 1 + 1), (↑(m + 1) : ℂ)
          * (↑(eulerianNumber (n + 1) m) : ℂ)
          * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ))
        = (∑ m ∈ Finset.range (n + 1), (↑(m + 1) : ℂ)
          * (↑(eulerianNumber (n + 1) m) : ℂ)
          * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ))
        + (↑(n + 1 + 1) : ℂ) * (↑(eulerianNumber (n + 1) (n + 1)) : ℂ)
          * (↑((k + (n + 1 + 1) - (n + 1)).choose (n + 1 + 1)) : ℂ) := by
      rw [Finset.sum_range_succ]
    rw [hpeel, hlast, add_zero]
    have hpm : ∀ m ∈ Finset.range (n + 1),
        (↑(m + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
          * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ)
        = (↑(m + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ)
          + (↑(m + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ) := by
      intro m hm
      have hmle : m ≤ n + 1 := by
        have hmem := Finset.mem_range.mp hm
        omega
      have hp := pascal_cast n k m hmle
      calc (↑(m + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
              * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ)
          = (↑(m + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
            * ((↑((k + (n + 1) - m).choose (n + 1)) : ℂ)
              + (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)) := by
            rw [hp]
        _ = (↑(m + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
              * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ)
            + (↑(m + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
              * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ) := by
            ring
    calc (∑ m ∈ Finset.range (n + 1), (↑(m + 1) : ℂ)
            * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ))
        = ∑ m ∈ Finset.range (n + 1), ((↑(m + 1) : ℂ)
            * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ)
          + (↑(m + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)) :=
          Finset.sum_congr rfl hpm
      _ = (∑ m ∈ Finset.range (n + 1), (↑(m + 1) : ℂ)
            * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ))
          + (∑ m ∈ Finset.range (n + 1), (↑(m + 1) : ℂ)
            * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)) :=
          Finset.sum_add_distrib
  have e3 : (∑ m ∈ Finset.range (n + 1 + 1), (↑(n + 1 + 1 - m) : ℂ)
        * (if m = 0 then (0 : ℂ) else (↑(eulerianNumber (n + 1) (m - 1)) : ℂ))
        * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ))
      = (∑ j ∈ Finset.range (n + 1), (↑(n + 1 - j) : ℂ)
        * (↑(eulerianNumber (n + 1) j) : ℂ)
        * (↑((k + (n + 1) - j).choose (n + 1 + 1)) : ℂ)) := by
    have hpeel2 : (∑ m ∈ Finset.range (n + 1 + 1), (↑(n + 1 + 1 - m) : ℂ)
          * (if m = 0 then (0 : ℂ) else (↑(eulerianNumber (n + 1) (m - 1)) : ℂ))
          * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ))
        = (∑ j ∈ Finset.range (n + 1), (↑(n + 1 + 1 - (j + 1)) : ℂ)
          * (if j + 1 = 0 then (0 : ℂ) else (↑(eulerianNumber (n + 1) (j + 1 - 1)) : ℂ))
          * (↑((k + (n + 1 + 1) - (j + 1)).choose (n + 1 + 1)) : ℂ))
        + (↑(n + 1 + 1 - 0) : ℂ)
          * (if (0 : ℕ) = 0 then (0 : ℂ) else (↑(eulerianNumber (n + 1) (0 - 1)) : ℂ))
          * (↑((k + (n + 1 + 1) - 0).choose (n + 1 + 1)) : ℂ) := by
      rw [Finset.sum_range_succ']
    have hf0 : (↑(n + 1 + 1 - 0) : ℂ)
          * (if (0 : ℕ) = 0 then (0 : ℂ) else (↑(eulerianNumber (n + 1) (0 - 1)) : ℂ))
          * (↑((k + (n + 1 + 1) - 0).choose (n + 1 + 1)) : ℂ) = 0 := by
      simp
    rw [hpeel2, hf0, add_zero]
    have hpt3 : ∀ j ∈ Finset.range (n + 1),
        (↑(n + 1 + 1 - (j + 1)) : ℂ)
          * (if j + 1 = 0 then (0 : ℂ) else (↑(eulerianNumber (n + 1) (j + 1 - 1)) : ℂ))
          * (↑((k + (n + 1 + 1) - (j + 1)).choose (n + 1 + 1)) : ℂ)
        = (↑(n + 1 - j) : ℂ) * (↑(eulerianNumber (n + 1) j) : ℂ)
          * (↑((k + (n + 1) - j).choose (n + 1 + 1)) : ℂ) := by
      intro j hj
      have ha1 : n + 1 + 1 - (j + 1) = n + 1 - j := by omega
      have ha2 : k + (n + 1 + 1) - (j + 1) = k + (n + 1) - j := by omega
      have ha3 : j + 1 - 1 = j := by omega
      have hif : (if j + 1 = 0 then (0 : ℂ)
          else (↑(eulerianNumber (n + 1) (j + 1 - 1)) : ℂ))
          = (↑(eulerianNumber (n + 1) (j + 1 - 1)) : ℂ) := by
        simp
      rw [hif, ha1, ha2, ha3]
    exact Finset.sum_congr rfl hpt3
  have e4 : (∑ m ∈ Finset.range (n + 1), (↑(m + 1) : ℂ)
        * (↑(eulerianNumber (n + 1) m) : ℂ)
        * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ))
      + (∑ m ∈ Finset.range (n + 1), (↑(n + 1 - m) : ℂ)
        * (↑(eulerianNumber (n + 1) m) : ℂ)
        * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ))
      = (∑ m ∈ Finset.range (n + 1), (↑(n + 1 + 1) : ℂ)
        * (↑(eulerianNumber (n + 1) m) : ℂ)
        * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)) := by
    have hpt4 : ∀ m ∈ Finset.range (n + 1),
        (↑(m + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
          * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)
        + (↑(n + 1 - m) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
          * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)
        = (↑(n + 1 + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
          * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ) := by
      intro m hm
      have hmle : m ≤ n + 1 := by
        have hmem := Finset.mem_range.mp hm
        omega
      have hc := coeff_add m n hmle
      calc (↑(m + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
              * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)
            + (↑(n + 1 - m) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
              * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)
          = ((↑(m + 1) : ℂ) + (↑(n + 1 - m) : ℂ))
            * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ) := by
            ring
        _ = (↑(n + 1 + 1) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ) := by
            rw [hc]
    calc (∑ m ∈ Finset.range (n + 1), (↑(m + 1) : ℂ)
            * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ))
          + (∑ m ∈ Finset.range (n + 1), (↑(n + 1 - m) : ℂ)
            * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ))
        = ∑ m ∈ Finset.range (n + 1), ((↑(m + 1) : ℂ)
            * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)
          + (↑(n + 1 - m) : ℂ) * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)) :=
          (Finset.sum_add_distrib).symm
      _ = (∑ m ∈ Finset.range (n + 1), (↑(n + 1 + 1) : ℂ)
            * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)) :=
          Finset.sum_congr rfl hpt4
  have hB : (∑ m ∈ Finset.range (n + 1 + 1),
        (↑(eulerianNumber (n + 1 + 1) m) : ℂ)
          * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ))
      = (∑ m ∈ Finset.range (n + 1), (↑(m + 1) : ℂ)
          * (↑(eulerianNumber (n + 1) m) : ℂ)
          * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ))
        + (∑ m ∈ Finset.range (n + 1), (↑(n + 1 + 1) : ℂ)
          * (↑(eulerianNumber (n + 1) m) : ℂ)
          * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)) := by
    calc (∑ m ∈ Finset.range (n + 1 + 1),
            (↑(eulerianNumber (n + 1 + 1) m) : ℂ)
              * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ))
        = ((∑ m ∈ Finset.range (n + 1 + 1), (↑(m + 1) : ℂ)
              * (↑(eulerianNumber (n + 1) m) : ℂ)
              * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ))
          + (∑ m ∈ Finset.range (n + 1 + 1), (↑(n + 1 + 1 - m) : ℂ)
            * (if m = 0 then (0 : ℂ) else (↑(eulerianNumber (n + 1) (m - 1)) : ℂ))
            * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ))) := e1
      _ = ((∑ m ∈ Finset.range (n + 1), (↑(m + 1) : ℂ)
              * (↑(eulerianNumber (n + 1) m) : ℂ)
              * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ))
            + (∑ m ∈ Finset.range (n + 1), (↑(m + 1) : ℂ)
              * (↑(eulerianNumber (n + 1) m) : ℂ)
              * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)))
          + (∑ j ∈ Finset.range (n + 1), (↑(n + 1 - j) : ℂ)
            * (↑(eulerianNumber (n + 1) j) : ℂ)
            * (↑((k + (n + 1) - j).choose (n + 1 + 1)) : ℂ)) := by
            rw [e2, e3]
      _ = (∑ m ∈ Finset.range (n + 1), (↑(m + 1) : ℂ)
            * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ))
          + (∑ m ∈ Finset.range (n + 1), (↑(n + 1 + 1) : ℂ)
            * (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1 + 1)) : ℂ)) := by
            rw [add_assoc, e4]
  rw [hk, hA]
  exact hB.symm

private lemma worpitzky (n k : ℕ) :
    ((↑k + 1 : ℂ)) ^ (n + 1)
      = ∑ m ∈ Finset.range (n + 1),
        (↑(eulerianNumber (n + 1) m) : ℂ) * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ) := by
  induction n with
  | zero =>
    have hA10 : eulerianNumber (0 + 1) 0 = 1 := by simp [eulerianNumber]
    have hC : (k + (0 + 1) - 0).choose (0 + 1) = k + 1 := by
      simp [Nat.choose_one_right]
    have hsum : (∑ m ∈ Finset.range (0 + 1),
          (↑(eulerianNumber (0 + 1) m) : ℂ) * (↑((k + (0 + 1) - m).choose (0 + 1)) : ℂ))
        = (↑(eulerianNumber (0 + 1) 0) : ℂ) * (↑((k + (0 + 1) - 0).choose (0 + 1)) : ℂ) := by
      rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
    rw [pow_one, hsum, hA10, hC]
    push_cast
    ring
  | succ n ih =>
    have hws := worp_step n k
    calc ((↑k + 1 : ℂ) ^ ((n + 1) + 1))
        = (((↑k + 1 : ℂ) ^ (n + 1))) * (((↑k + 1 : ℂ))) := pow_succ _ _
      _ = (∑ m ∈ Finset.range (n + 1),
            (↑(eulerianNumber (n + 1) m) : ℂ) * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ))
          * (((↑k + 1 : ℂ))) := by rw [ih]
      _ = ((↑k + 1 : ℂ)) * (∑ m ∈ Finset.range (n + 1),
            (↑(eulerianNumber (n + 1) m) : ℂ) * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ)) := by
          ring
      _ = ∑ m ∈ Finset.range (n + 1 + 1),
            (↑(eulerianNumber (n + 1 + 1) m) : ℂ)
              * (↑((k + (n + 1 + 1) - m).choose (n + 1 + 1)) : ℂ) := hws

private lemma summable_entry4 (n : ℕ) (p : ℂ) (hp : ‖p‖ < 1) :
    Summable (fun k : ℕ => (↑k + 1 : ℂ) ^ n * (-p) ^ k) := by
  have hpx : ‖-p‖ < 1 := by rwa [norm_neg]
  have hexpand : ∀ k : ℕ, (↑k + 1 : ℂ) ^ n * (-p) ^ k
      = ∑ i ∈ Finset.range (n + 1),
        (↑(n.choose i) : ℂ) * ((↑k : ℂ) ^ i * (-p) ^ k) := by
    intro k
    have h := add_pow (↑k : ℂ) 1 n
    calc (↑k + 1 : ℂ) ^ n * (-p) ^ k
        = (∑ m ∈ Finset.range (n + 1), (↑k : ℂ) ^ m * 1 ^ (n - m) * (↑(n.choose m) : ℂ))
          * (-p) ^ k := by rw [h]
      _ = ∑ i ∈ Finset.range (n + 1),
            (↑(n.choose i) : ℂ) * ((↑k : ℂ) ^ i * (-p) ^ k) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i hi => by ring)
  have hfun : (fun k : ℕ => (↑k + 1 : ℂ) ^ n * (-p) ^ k)
      = (fun k : ℕ => ∑ i ∈ Finset.range (n + 1),
        (↑(n.choose i) : ℂ) * ((↑k : ℂ) ^ i * (-p) ^ k)) :=
    funext hexpand
  rw [hfun]
  apply summable_sum
  intro i hi
  exact (summable_pow_mul_geometric_of_norm_lt_one i hpx).mul_left _

private lemma summable_choose_shift (N m : ℕ) (x : ℂ) (hx : ‖x‖ < 1) (hm : m ≤ N) :
    Summable (fun k : ℕ => (↑((k + N - m).choose N) : ℂ) * x ^ k) := by
  have hshift : ∀ k : ℕ, (↑((k + m + N - m).choose N) : ℂ) * x ^ (k + m)
      = x ^ m * ((↑((k + N).choose N) : ℂ) * x ^ k) := by
    intro k
    have heq : k + m + N - m = k + N := by omega
    rw [heq, pow_add]
    ring
  have hgsum := summable_choose_mul_geometric_of_norm_lt_one N (r := x) hx
  have hshifted : Summable (fun k : ℕ => (↑((k + m + N - m).choose N) : ℂ) * x ^ (k + m)) := by
    have h2 : (fun k : ℕ => (↑((k + m + N - m).choose N) : ℂ) * x ^ (k + m))
        = (fun k : ℕ => x ^ m * ((↑((k + N).choose N) : ℂ) * x ^ k)) :=
      funext hshift
    rw [h2]
    exact hgsum.mul_left _
  have htrans := (summable_nat_add_iff
    (f := fun k : ℕ => (↑((k + N - m).choose N) : ℂ) * x ^ k) m).mp
  apply htrans
  exact hshifted

private lemma tsum_choose_shift (N m : ℕ) (x : ℂ) (hx : ‖x‖ < 1) (hm : m ≤ N) :
    (∑' k : ℕ, (↑((k + N - m).choose N) : ℂ) * x ^ k)
      = x ^ m / (1 - x) ^ (N + 1) := by
  have hF : Summable (fun k : ℕ => (↑((k + N - m).choose N) : ℂ) * x ^ k) :=
    summable_choose_shift N m x hx hm
  have hvan : ∀ k ∈ Finset.range m,
      (↑((k + N - m).choose N) : ℂ) * x ^ k = 0 := by
    intro k hk
    have hkm : k + N - m < N := by
      have h1 := Finset.mem_range.mp hk
      omega
    rw [Nat.choose_eq_zero_of_lt hkm]
    simp
  have hshift : ∀ k : ℕ, (↑((k + m + N - m).choose N) : ℂ) * x ^ (k + m)
      = x ^ m * ((↑((k + N).choose N) : ℂ) * x ^ k) := by
    intro k
    have heq : k + m + N - m = k + N := by omega
    rw [heq, pow_add]
    ring
  have hgsum := summable_choose_mul_geometric_of_norm_lt_one N (r := x) hx
  have hval := tsum_choose_mul_geometric_of_norm_lt_one N (r := x) hx
  have hts : (∑' i : ℕ, (↑(((i + m) + N - m).choose N) : ℂ) * x ^ (i + m))
      = x ^ m * (∑' i : ℕ, (↑((i + N).choose N) : ℂ) * x ^ i) := by
    calc (∑' i : ℕ, (↑(((i + m) + N - m).choose N) : ℂ) * x ^ (i + m))
        = ∑' i : ℕ, x ^ m * ((↑((i + N).choose N) : ℂ) * x ^ i) := by
          apply tsum_congr
          intro i
          exact hshift i
      _ = x ^ m * (∑' i : ℕ, (↑((i + N).choose N) : ℂ) * x ^ i) :=
          Summable.tsum_mul_left _ hgsum
  have hdecomp := Summable.sum_add_tsum_nat_add m hF
  rw [Finset.sum_eq_zero hvan, zero_add] at hdecomp
  rw [← hdecomp, hts, hval, mul_one_div]

/-- **Eulerian polynomials and the series of (k+1)^n (-p)^k.** Let $A(n,k)$ be the Eulerian
numbers, given by $A(0,0) = 1$, $A(0,k) = 0$ for $k \ge 1$ and
$A(n+1,k) = (k+1)A(n,k) + (n+1-k)A(n,k-1)$, where the last term is $0$ when $k = 0$, and let
$\Psi_0(p) = 1$ and $\Psi_n(p) = \sum_{k=0}^{n-1} A(n,k)(-p)^k$ for $n \ge 1$. For every natural
number $n$ and every complex number $p$ with $|p| < 1$, we have $p + 1 \ne 0$, the series
$\sum_{k \ge 0} (k+1)^n (-p)^k$ is summable, and
$\Psi_n(p)/(p+1)^{n+1} = \sum_{k=0}^{\infty} (k+1)^n (-p)^k$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 5,
Entry 4, p. 113.
Proves `Wanted` entry `ramanujan_part1_ch5_entry4`.
-/
theorem ramanujan_part1_ch5_entry4 (n : ℕ) (p : ℂ) (hp : ‖p‖ < 1) :
    p + 1 ≠ 0 ∧
      Summable (chapter5Entry4Term n p) ∧
      chapter5Psi n p / (p + 1) ^ (n + 1) =
        ∑' k : ℕ, chapter5Entry4Term n p k := by
  have h1 : p + 1 ≠ 0 := by
    intro h
    have hp1 : p = -1 := by linear_combination h
    rw [hp1] at hp
    simp at hp
  have hx : ‖-p‖ < 1 := by rwa [norm_neg]
  have hs : Summable (chapter5Entry4Term n p) := summable_entry4 n p hp
  refine ⟨h1, hs, ?_⟩
  cases n with
  | zero =>
    have hterm0 : ∀ k : ℕ, chapter5Entry4Term 0 p k = (-p) ^ k := by
      intro k
      simp [chapter5Entry4Term]
    have hts : (∑' k : ℕ, chapter5Entry4Term 0 p k) = (1 - (-p))⁻¹ := by
      calc (∑' k : ℕ, chapter5Entry4Term 0 p k)
          = ∑' k : ℕ, (-p) ^ k := tsum_congr hterm0
        _ = (1 - (-p))⁻¹ := tsum_geometric_of_norm_lt_one hx
    have hPsi0 : chapter5Psi 0 p = 1 := rfl
    have hexp : (p + 1) ^ (0 + 1) = p + 1 := pow_one _
    rw [hPsi0, hts, hexp]
    have hpp : (1 : ℂ) - (-p) = p + 1 := by ring
    rw [hpp, one_div]
  | succ n =>
    have hPsi : chapter5Psi (n + 1) p
        = ∑ m ∈ Finset.range (n + 1),
          (↑(eulerianNumber (n + 1) m) : ℂ) * (-p) ^ m := rfl
    have hW : ∀ k : ℕ, (↑k + 1 : ℂ) ^ (n + 1)
        = ∑ m ∈ Finset.range (n + 1),
          (↑(eulerianNumber (n + 1) m) : ℂ)
            * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ) :=
      fun k => worpitzky n k
    have hterm : ∀ k : ℕ, chapter5Entry4Term (n + 1) p k
        = ∑ m ∈ Finset.range (n + 1),
          (↑(eulerianNumber (n + 1) m) : ℂ)
            * ((↑((k + (n + 1) - m).choose (n + 1)) : ℂ) * (-p) ^ k) := by
      intro k
      have hw := hW k
      show (↑k + 1 : ℂ) ^ (n + 1) * (-p) ^ k = _
      calc (↑k + 1 : ℂ) ^ (n + 1) * (-p) ^ k
          = (∑ m ∈ Finset.range (n + 1),
              (↑(eulerianNumber (n + 1) m) : ℂ)
                * (↑((k + (n + 1) - m).choose (n + 1)) : ℂ)) * (-p) ^ k := by
            rw [hw]
        _ = ∑ m ∈ Finset.range (n + 1),
              (↑(eulerianNumber (n + 1) m) : ℂ)
                * ((↑((k + (n + 1) - m).choose (n + 1)) : ℂ) * (-p) ^ k) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl (fun m hm => by ring)
    have hsub : ∀ m ∈ Finset.range (n + 1),
        Summable (fun k : ℕ => (↑(eulerianNumber (n + 1) m) : ℂ)
          * ((↑((k + (n + 1) - m).choose (n + 1)) : ℂ) * (-p) ^ k)) := by
      intro m hm
      have hmle : m ≤ n + 1 := by
        have hmem := Finset.mem_range.mp hm
        omega
      exact (summable_choose_shift (n + 1) m (-p) hx hmle).mul_left _
    have hsum1 : (∑' k : ℕ, chapter5Entry4Term (n + 1) p k)
        = ∑ m ∈ Finset.range (n + 1),
          (↑(eulerianNumber (n + 1) m) : ℂ)
            * (∑' k : ℕ, (↑((k + (n + 1) - m).choose (n + 1)) : ℂ) * (-p) ^ k) := by
      have hfun : (fun k : ℕ => chapter5Entry4Term (n + 1) p k)
          = (fun k : ℕ => ∑ m ∈ Finset.range (n + 1),
            (↑(eulerianNumber (n + 1) m) : ℂ)
              * ((↑((k + (n + 1) - m).choose (n + 1)) : ℂ) * (-p) ^ k)) :=
        funext hterm
      rw [hfun]
      calc (∑' k : ℕ, ∑ m ∈ Finset.range (n + 1),
              (↑(eulerianNumber (n + 1) m) : ℂ)
                * ((↑((k + (n + 1) - m).choose (n + 1)) : ℂ) * (-p) ^ k))
          = ∑ m ∈ Finset.range (n + 1), ∑' k : ℕ,
              (↑(eulerianNumber (n + 1) m) : ℂ)
                * ((↑((k + (n + 1) - m).choose (n + 1)) : ℂ) * (-p) ^ k) :=
            Summable.tsum_finsetSum hsub
        _ = ∑ m ∈ Finset.range (n + 1),
              (↑(eulerianNumber (n + 1) m) : ℂ)
                * (∑' k : ℕ, (↑((k + (n + 1) - m).choose (n + 1)) : ℂ) * (-p) ^ k) := by
            apply Finset.sum_congr rfl
            intro m hm
            have hmle : m ≤ n + 1 := by
              have hmem := Finset.mem_range.mp hm
              omega
            exact Summable.tsum_mul_left _
              (summable_choose_shift (n + 1) m (-p) hx hmle)
    have hval2 : ∀ m ∈ Finset.range (n + 1),
        (↑(eulerianNumber (n + 1) m) : ℂ)
          * (∑' k : ℕ, (↑((k + (n + 1) - m).choose (n + 1)) : ℂ) * (-p) ^ k)
        = ((↑(eulerianNumber (n + 1) m) : ℂ) * (-p) ^ m) / (1 - (-p)) ^ (n + 1 + 1) := by
      intro m hm
      have hmle : m ≤ n + 1 := by
        have hmem := Finset.mem_range.mp hm
        omega
      rw [tsum_choose_shift (n + 1) m (-p) hx hmle]
      ring
    have hsum2 : (∑' k : ℕ, chapter5Entry4Term (n + 1) p k)
        = (∑ m ∈ Finset.range (n + 1),
          (↑(eulerianNumber (n + 1) m) : ℂ) * (-p) ^ m)
          / (1 - (-p)) ^ (n + 1 + 1) := by
      calc (∑' k : ℕ, chapter5Entry4Term (n + 1) p k)
          = ∑ m ∈ Finset.range (n + 1),
              (↑(eulerianNumber (n + 1) m) : ℂ)
                * (∑' k : ℕ, (↑((k + (n + 1) - m).choose (n + 1)) : ℂ) * (-p) ^ k) := hsum1
        _ = ∑ m ∈ Finset.range (n + 1),
              ((↑(eulerianNumber (n + 1) m) : ℂ) * (-p) ^ m)
                / (1 - (-p)) ^ (n + 1 + 1) :=
              Finset.sum_congr rfl hval2
        _ = (∑ m ∈ Finset.range (n + 1),
              (↑(eulerianNumber (n + 1) m) : ℂ) * (-p) ^ m)
            / (1 - (-p)) ^ (n + 1 + 1) :=
              (Finset.sum_div _ _ _).symm
    rw [hPsi, hsum2]
    have hpp : (1 : ℂ) - (-p) = p + 1 := by ring
    rw [hpp]

end

end Entry4

end MathlibExt.Analysis.Ramanujan.Part1Ch5
