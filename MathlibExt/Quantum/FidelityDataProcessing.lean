/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BhattacharyyaCoeff
public import Mathlib.Data.Matrix.Mul

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Data processing for the classical fidelity

The Bhattacharyya coefficient `bhattacharyyaCoeff p q = ∑ x, √(p x * q x)` is the classical
fidelity of two probability vectors (M. A. Nielsen and I. L. Chuang, Chapter 9). It cannot
decrease when both vectors pass through the same row-stochastic matrix `S`, that is, under
the vector-matrix product `p ᵥ* S`, whose entry `j` is `∑ i, p i * S i j`. The proof applies the
Cauchy–Schwarz inequality to each output coordinate. The quantum version, for density operators
and quantum channels, is not included here.

## Main results

* `MathlibExt.Quantum.FidelityDataProcessing.bhattacharyyaCoeff_le_bhattacharyyaCoeff_vecMul`:
  for nonnegative `p`, `q` and a matrix `S` with nonnegative entries and rows summing to `1`,
  `bhattacharyyaCoeff p q ≤ bhattacharyyaCoeff (p ᵥ* S) (q ᵥ* S)`.

## References

* M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*, Cambridge
  University Press (2000), Chapter 9.
-/

@[expose] public section

namespace MathlibExt.Quantum.FidelityDataProcessing

open MathlibExt.Quantum.ClassicalFuchsVanDeGraaf (bhattacharyyaCoeff)
open Matrix

private lemma sqrt_prod_mul {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    Real.sqrt (a * s) * Real.sqrt (b * s) = Real.sqrt (a * b) * s := by
  rw [Real.sqrt_mul ha s, Real.sqrt_mul hb s]
  calc (Real.sqrt a * Real.sqrt s) * (Real.sqrt b * Real.sqrt s)
      = (Real.sqrt a * Real.sqrt b) * (Real.sqrt s * Real.sqrt s) := by ring
    _ = Real.sqrt (a * b) * s := by
        rw [← Real.sqrt_mul ha b, Real.mul_self_sqrt hs]

private lemma inner_le {α : Type*} [Fintype α] (p q : α → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hq0 : ∀ i, 0 ≤ q i) (s : α → ℝ) (hs0 : ∀ i, 0 ≤ s i) :
    ∑ i, Real.sqrt (p i * q i) * s i ≤
      Real.sqrt ((∑ i, p i * s i) * (∑ i, q i * s i)) := by
  set f : α → ℝ := fun i => Real.sqrt (p i * s i) with hf
  set g : α → ℝ := fun i => Real.sqrt (q i * s i) with hg
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
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

/-- **Data processing for the classical fidelity.** Passing two
nonnegative vectors `p` and `q` through the same row-stochastic
matrix `S` (nonnegative entries, each row summing to `1`) cannot
decrease their Bhattacharyya coefficient. -/
theorem bhattacharyyaCoeff_le_bhattacharyyaCoeff_vecMul {α β : Type*} [Fintype α] [Fintype β]
    (S : Matrix α β ℝ) (hS0 : ∀ i j, 0 ≤ S i j) (hS1 : ∀ i, ∑ j, S i j = 1)
    (p q : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i) :
    bhattacharyyaCoeff p q ≤ bhattacharyyaCoeff (p ᵥ* S) (q ᵥ* S) := by
  simp only [bhattacharyyaCoeff, vecMul_apply_eq_sum]
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

end MathlibExt.Quantum.FidelityDataProcessing

end
