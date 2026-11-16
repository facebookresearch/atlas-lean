/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BhattacharyyaCoeff
public import MathlibExt.Probability.MarkovMixing
public import Mathlib.Analysis.Real.Sqrt

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Classical Fuchs-van de Graaf inequalities

For probability vectors `p` and `q` on a finite type, let `D = tvDist p q = (1/2) ∑ x, |p x - q x|`
be their total variation distance, which is the trace distance between probability distributions
of Nielsen and Chuang (Chapter 9), and let `B = bhattacharyyaCoeff p q = ∑ x, √(p x * q x)` be
their Bhattacharyya coefficient. Then

`1 - B ≤ D ≤ √(1 - B ^ 2)`.

`B` is the unsquared coefficient: the classical fidelity `F(p, q) = ∑ x, √(p x * q x)` of
Nielsen and Chuang (Chapter 9), sometimes called the root fidelity. Under the squared convention
`F = B ^ 2` the same bounds read `1 - √F ≤ D ≤ √(1 - F)`. The quantum version for density
operators is not proved here.

## Main results

* `one_sub_bhattacharyyaCoeff_le_tvDist`: `1 - B ≤ D`.
* `tvDist_le_sqrt_one_sub_bhattacharyyaCoeff_sq`: `D ≤ √(1 - B ^ 2)`.

## References

* C. A. Fuchs and J. van de Graaf, *Cryptographic distinguishability measures for
  quantum-mechanical states*, IEEE Transactions on Information Theory 45 (1999), no. 4,
  1216-1227.
* M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*, Cambridge
  University Press (2000), Chapter 9.
-/

@[expose] public section

namespace MathlibExt.Quantum.ClassicalFuchsVanDeGraaf

open MathlibExt.Probability.MarkovMixing

variable {S : Type*} [Fintype S]

private theorem sum_sqrt_mul_sqrt (p q : S → ℝ) (hp0 : ∀ x, 0 ≤ p x) :
    ∑ x, Real.sqrt (p x) * Real.sqrt (q x) = bhattacharyyaCoeff p q :=
  Finset.sum_congr rfl fun x _ => (Real.sqrt_mul (hp0 x) _).symm

private theorem sum_sub_sq (p q : S → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) :
    ∑ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 = 2 - 2 * bhattacharyyaCoeff p q := by
  have e : ∀ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 =
      p x + q x - 2 * (Real.sqrt (p x) * Real.sqrt (q x)) := by
    intro x
    have h : (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2
        = Real.sqrt (p x) ^ 2 + Real.sqrt (q x) ^ 2
          - 2 * (Real.sqrt (p x) * Real.sqrt (q x)) := by ring
    rw [h, Real.sq_sqrt (hp0 x), Real.sq_sqrt (hq0 x)]
  rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, sum_sqrt_mul_sqrt p q hp0, hp1, hq1]
  ring

private theorem sum_add_sq (p q : S → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) :
    ∑ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2 = 2 + 2 * bhattacharyyaCoeff p q := by
  have e : ∀ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2 =
      p x + q x + 2 * (Real.sqrt (p x) * Real.sqrt (q x)) := by
    intro x
    have h : (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2
        = Real.sqrt (p x) ^ 2 + Real.sqrt (q x) ^ 2
          + 2 * (Real.sqrt (p x) * Real.sqrt (q x)) := by ring
    rw [h, Real.sq_sqrt (hp0 x), Real.sq_sqrt (hq0 x)]
  rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, sum_sqrt_mul_sqrt p q hp0, hp1, hq1]
  ring

/-- `|a - b| = |√a - √b| (√a + √b)` for nonnegative `a` and `b`. -/
private theorem abs_sub_eq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a - b| = |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) := by
  have hnonneg : 0 ≤ Real.sqrt a + Real.sqrt b :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hfac : a - b = (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) := by
    have h : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b)
        = Real.sqrt a ^ 2 - Real.sqrt b ^ 2 := by ring
    rw [h, Real.sq_sqrt ha, Real.sq_sqrt hb]
  rw [hfac, abs_mul, abs_of_nonneg hnonneg]

/-- **Classical Fuchs-van de Graaf lower bound**: for probability vectors, one minus the
Bhattacharyya coefficient is at most the total variation distance. -/
theorem one_sub_bhattacharyyaCoeff_le_tvDist (p q : S → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) :
    1 - bhattacharyyaCoeff p q ≤ tvDist p q := by
  have hpt : ∀ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ≤ |p x - q x| := by
    intro x
    have hle : |Real.sqrt (p x) - Real.sqrt (q x)| ≤ Real.sqrt (p x) + Real.sqrt (q x) :=
      (abs_sub _ _).trans_eq (by
        rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)])
    rw [abs_sub_eq (p x) (q x) (hp0 x) (hq0 x), ← sq_abs, sq]
    exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
  have hS : 2 - 2 * bhattacharyyaCoeff p q ≤ ∑ x, |p x - q x| := by
    rw [← sum_sub_sq p q hp0 hq0 hp1 hq1]
    exact Finset.sum_le_sum fun x _ => hpt x
  unfold tvDist
  linarith

/-- **Classical Fuchs-van de Graaf upper bound**: for probability vectors, the total
variation distance is at most `√(1 - B ^ 2)`, where `B` is the Bhattacharyya coefficient. -/
theorem tvDist_le_sqrt_one_sub_bhattacharyyaCoeff_sq (p q : S → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) :
    tvDist p q ≤ Real.sqrt (1 - bhattacharyyaCoeff p q ^ 2) := by
  have hcs : (∑ x, |Real.sqrt (p x) - Real.sqrt (q x)| * (Real.sqrt (p x) + Real.sqrt (q x)))
        ^ 2
      ≤ (∑ x, |Real.sqrt (p x) - Real.sqrt (q x)| ^ 2)
        * ∑ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have e1 : ∑ x, |Real.sqrt (p x) - Real.sqrt (q x)| * (Real.sqrt (p x) + Real.sqrt (q x))
      = ∑ x, |p x - q x| :=
    Finset.sum_congr rfl fun x _ => (abs_sub_eq (p x) (q x) (hp0 x) (hq0 x)).symm
  have e2 : ∑ x, |Real.sqrt (p x) - Real.sqrt (q x)| ^ 2 = 2 - 2 * bhattacharyyaCoeff p q := by
    rw [← sum_sub_sq p q hp0 hq0 hp1 hq1]
    exact Finset.sum_congr rfl fun x _ => sq_abs _
  rw [e1, e2, sum_add_sq p q hp0 hq0 hp1 hq1] at hcs
  have hcs' : (∑ x, |p x - q x|) ^ 2 ≤ 4 * (1 - bhattacharyyaCoeff p q ^ 2) :=
    hcs.trans_eq (by ring)
  apply Real.le_sqrt_of_sq_le
  have hsq : tvDist p q ^ 2 = (∑ x, |p x - q x|) ^ 2 / 4 := by
    unfold tvDist
    ring
  rw [hsq]
  linarith

end MathlibExt.Quantum.ClassicalFuchsVanDeGraaf

end
