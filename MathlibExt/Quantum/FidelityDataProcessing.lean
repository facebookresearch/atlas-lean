/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Mathlib.Tactic.Ring

/-!
# Data processing for fidelity

A stochastic map cannot decrease the Bhattacharyya
coefficient of two finite distributions. The quantum CPTP
version is not included here.
-/

@[expose] public section

/-- Bhattacharyya coefficient of two finite distributions. -/
noncomputable def bhattD {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  ∑ i, Real.sqrt (p i * q i)

/-- Pushforward of a distribution along a stochastic
matrix `S` (rows indexed by inputs). -/
noncomputable def pushf {m n : ℕ} (S : Fin m → Fin n → ℝ)
    (p : Fin m → ℝ) : Fin n → ℝ :=
  fun j => ∑ i, p i * S i j

private lemma sqrt_prod_mul {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    Real.sqrt (a * s) * Real.sqrt (b * s) = Real.sqrt (a * b) * s := by
  rw [Real.sqrt_mul ha s, Real.sqrt_mul hb s]
  calc (Real.sqrt a * Real.sqrt s) * (Real.sqrt b * Real.sqrt s)
      = (Real.sqrt a * Real.sqrt b) * (Real.sqrt s * Real.sqrt s) := by ring
    _ = Real.sqrt (a * b) * s := by
        rw [← Real.sqrt_mul ha b, Real.mul_self_sqrt hs]

private lemma inner_le {m : ℕ} (p q : Fin m → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hq0 : ∀ i, 0 ≤ q i) (s : Fin m → ℝ) (hs0 : ∀ i, 0 ≤ s i) :
    ∑ i, Real.sqrt (p i * q i) * s i ≤
      Real.sqrt ((∑ i, p i * s i) * (∑ i, q i * s i)) := by
  classical
  set f : Fin m → ℝ := fun i => Real.sqrt (p i * s i) with hf
  set g : Fin m → ℝ := fun i => Real.sqrt (q i * s i) with hg
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  -- rewrite the three sums
  have hfg : ∀ i, f i * g i = Real.sqrt (p i * q i) * s i := fun i =>
    sqrt_prod_mul (hp0 i) (hq0 i) (hs0 i)
  have hf2 : ∀ i, (f i) ^ 2 = p i * s i := fun i =>
    Real.sq_sqrt (mul_nonneg (hp0 i) (hs0 i))
  have hg2 : ∀ i, (g i) ^ 2 = q i * s i := fun i =>
    Real.sq_sqrt (mul_nonneg (hq0 i) (hs0 i))
  have hsum1 : ∑ i, f i * g i = ∑ i, Real.sqrt (p i * q i) * s i :=
    Finset.sum_congr rfl (fun i _ => hfg i)
  have hsum2 : ∑ i, (f i) ^ 2 = ∑ i, p i * s i :=
    Finset.sum_congr rfl (fun i _ => hf2 i)
  have hsum3 : ∑ i, (g i) ^ 2 = ∑ i, q i * s i :=
    Finset.sum_congr rfl (fun i _ => hg2 i)
  rw [hsum1, hsum2, hsum3] at hCS
  exact Real.le_sqrt_of_sq_le hCS

/-- Data processing for fidelity (QCI-52 classical core):
a stochastic map cannot decrease the Bhattacharyya
coefficient. -/
theorem bhatt_pushf_ge {m n : ℕ} (S : Fin m → Fin n → ℝ)
    (hS0 : ∀ i j, 0 ≤ S i j) (hS1 : ∀ i, ∑ j, S i j = 1)
    (p q : Fin m → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i) :
    bhattD p q ≤ bhattD (pushf S p) (pushf S q) := by
  classical
  simp only [bhattD, pushf]
  calc ∑ i, Real.sqrt (p i * q i)
      = ∑ i, Real.sqrt (p i * q i) * (∑ j, S i j) := by
        congr 1
        ext i
        rw [hS1 i, mul_one]
    _ = ∑ i, ∑ j, Real.sqrt (p i * q i) * S i j := by
        congr 1
        ext i
        rw [Finset.mul_sum]
    _ = ∑ j, ∑ i, Real.sqrt (p i * q i) * S i j := Finset.sum_comm
    _ ≤ ∑ j, Real.sqrt ((∑ i, p i * S i j) * (∑ i, q i * S i j)) := by
        apply Finset.sum_le_sum
        intro j _
        exact inner_le p q hp0 hq0 (fun i => S i j) (fun i => hS0 i j)

end
