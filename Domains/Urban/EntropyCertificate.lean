/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import MathlibExt.LinearAlgebra.Matrix.SinkhornMargins
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

/-!
# Entropy optimality certificate

For finite tables with positive `K`, row scales `a`, and column
scales `b`, put `T i j = a i * K i j * b j`. Every nonnegative
table `S` with the same row and column margins as `T` satisfies
`F(S) - F(T) = ∑ i j, T i j * klFun (S i j / T i j) ≥ 0`, where
`F(S) = ∑ i j, S i j * log (S i j / K i j)`: the scaled table `T`
minimizes the entropy functional over its margin class, and the
Kullback-Leibler-style sum is the optimality certificate.

## Main results

- `SinkhornMargins.entropy_optimality_certificate`: the identity
  and its nonnegativity, for general finite index types.
- `SinkhornMargins.entropy_optimality_certificate_scaledTable`:
  the certificate stated for the canonical scaled table
  `SinkhornMargins.scaledTable`.

The entropy functional is the finite I-divergence-style
objective `F(S) = ∑ i j, S i j * log (S i j / K i j)` with
reference kernel `K`, minimized over the linear row/column
margin constraints. The formal statement below is the exact
finite algebraic certificate for that objective and those
constraints: it assumes the scaled table and its margins and
proves optimality directly, without asserting existence of
scaling factors for prescribed margins.

## References

- R. Sinkhorn and P. Knopp, concerning nonnegative matrices
  and doubly stochastic matrices, *Pacific J. Math.* 21,
  1967 (matrix scaling to prescribed margins).
- I. Csiszár, I-divergence geometry of probability
  distributions and minimization problems, *Ann. Probab.* 3,
  1975 (entropy/I-projection minimization under linear
  constraints).
-/

@[expose] public section

open InformationTheory

namespace SinkhornMargins

private theorem klFun_entrywise_identity (s k aval bval : ℝ) (hk : 0 < k) (ha : 0 < aval)
    (hb : 0 < bval) (hs : 0 ≤ s) :
    (aval * k * bval) * klFun (s / (aval * k * bval))
      = s * Real.log (s / k) - (aval * k * bval) * Real.log ((aval * k * bval) / k)
        - (s - aval * k * bval) * Real.log aval
        - (s - aval * k * bval) * Real.log bval
        + (aval * k * bval - s) := by
  have hT : 0 < aval * k * bval := mul_pos (mul_pos ha hk) hb
  have hTne : aval * k * bval ≠ 0 := ne_of_gt hT
  have hkne : k ≠ 0 := ne_of_gt hk
  have hane : aval ≠ 0 := ne_of_gt ha
  have hbne : bval ≠ 0 := ne_of_gt hb
  have hTk : (aval * k * bval) / k = aval * bval := by
    rw [div_eq_iff hkne]
    ring
  have hlogT : Real.log ((aval * k * bval) / k)
      = Real.log aval + Real.log bval := by
    rw [hTk, Real.log_mul hane hbne]
  by_cases hs0 : s = 0
  · subst hs0
    rw [zero_div, klFun_zero, hlogT]
    ring
  · have hpos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    have hsne : s ≠ 0 := ne_of_gt hpos
    have hlogS : Real.log (s / (aval * k * bval))
        = Real.log (s / k) - Real.log ((aval * k * bval) / k) := by
      rw [Real.log_div hsne hTne, Real.log_div hsne hkne, Real.log_div hTne hkne]
      ring
    have hTT : (aval * k * bval) * (s / (aval * k * bval)) = s := by
      rw [mul_comm, div_mul_cancel₀ s hTne]
    have hkl : (aval * k * bval) * klFun (s / (aval * k * bval))
        = s * Real.log (s / (aval * k * bval)) + (aval * k * bval - s) := by
      rw [klFun_apply, mul_sub, mul_add, mul_one, ← mul_assoc, hTT]
      ring
    rw [hkl, hlogS, hlogT]
    ring

/-- Entropy optimality certificate. For finite index sets and
positive `K`, `a`, `b`, let `T i j = a i * K i j * b j`. Every
nonnegative table `S` with exactly the same row and column margins
as `T` satisfies
`F(S) - F(T) = ∑ i j, T i j * klFun (S i j / T i j) ≥ 0`, where
`F(S) = ∑ i j, S i j * log (S i j / K i j)` and zero entries use
the convention `log 0 = 0` (so a zero entry contributes `0` to
`F(S)` and `T i j` to the certificate sum). Hence `T` minimizes
`F` over its margin class. -/
theorem entropy_optimality_certificate {ι κ : Type*}
    [Fintype ι] [Fintype κ] (K S : ι → κ → ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (hK : ∀ i j, 0 < K i j) (ha : ∀ i, 0 < a i)
    (hb : ∀ j, 0 < b j) (hS : ∀ i j, 0 ≤ S i j)
    (hrow : ∀ i, ∑ j, S i j = ∑ j, a i * K i j * b j)
    (hcol : ∀ j, ∑ i, S i j = ∑ i, a i * K i j * b j) :
    (∑ i, ∑ j, S i j * Real.log (S i j / K i j))
        - (∑ i, ∑ j, (a i * K i j * b j)
            * Real.log ((a i * K i j * b j) / K i j))
      = ∑ i, ∑ j, (a i * K i j * b j)
          * klFun (S i j / (a i * K i j * b j))
    ∧ 0 ≤ ∑ i, ∑ j, (a i * K i j * b j)
          * klFun (S i j / (a i * K i j * b j)) := by
  have hT : ∀ i j, 0 < a i * K i j * b j :=
    fun i j => mul_pos (mul_pos (ha i) (hK i j)) (hb j)
  have hentry : ∀ i j, (a i * K i j * b j) * klFun (S i j / (a i * K i j * b j))
      = S i j * Real.log (S i j / K i j)
        - (a i * K i j * b j) * Real.log ((a i * K i j * b j) / K i j)
        - (S i j - a i * K i j * b j) * Real.log (a i)
        - (S i j - a i * K i j * b j) * Real.log (b j)
        + (a i * K i j * b j - S i j) :=
    fun i j => klFun_entrywise_identity (S i j) (K i j) (a i) (b j)
      (hK i j) (ha i) (hb j) (hS i j)
  have hrow0 : ∀ i, ∑ j, (S i j - a i * K i j * b j) = 0 := by
    intro i
    rw [Finset.sum_sub_distrib, hrow i, sub_self]
  have hcol0 : ∀ j, ∑ i, (S i j - a i * K i j * b j) = 0 := by
    intro j
    rw [Finset.sum_sub_distrib, hcol j, sub_self]
  have htot : (∑ i, ∑ j, a i * K i j * b j) - (∑ i, ∑ j, S i j) = 0 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← hrow i, sub_self]
  have hcorrA : ∑ i, ∑ j, (S i j - a i * K i j * b j) * Real.log (a i) = 0 := by
    have h : ∀ i, ∑ j, (S i j - a i * K i j * b j) * Real.log (a i) = 0 := by
      intro i
      rw [← Finset.sum_mul, hrow0 i, zero_mul]
    exact Finset.sum_eq_zero fun i _ => h i
  have hcorrB : ∑ i, ∑ j, (S i j - a i * K i j * b j) * Real.log (b j) = 0 := by
    rw [Finset.sum_comm]
    have h : ∀ j, ∑ i, (S i j - a i * K i j * b j) * Real.log (b j) = 0 := by
      intro j
      rw [← Finset.sum_mul, hcol0 j, zero_mul]
    exact Finset.sum_eq_zero fun j _ => h j
  constructor
  · have hrewrite : (∑ i, ∑ j, (a i * K i j * b j)
          * klFun (S i j / (a i * K i j * b j)))
        = ∑ i, ∑ j, (S i j * Real.log (S i j / K i j)
          - (a i * K i j * b j) * Real.log ((a i * K i j * b j) / K i j)
          - (S i j - a i * K i j * b j) * Real.log (a i)
          - (S i j - a i * K i j * b j) * Real.log (b j)
          + (a i * K i j * b j - S i j)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      exact hentry i j
    rw [hrewrite]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hcorrA, hcorrB, htot]
    ring
  · refine Finset.sum_nonneg fun i _ => ?_
    refine Finset.sum_nonneg fun j _ => ?_
    refine mul_nonneg (le_of_lt (hT i j)) (klFun_nonneg (div_nonneg (hS i j) ?_))
    exact le_of_lt (hT i j)

/-- The certificate for the canonical scaled table
`SinkhornMargins.scaledTable`: for positive `K`, `a`, `b`, every
nonnegative matrix `S` with the same row and column margins as
`scaledTable a K b` satisfies the entropy identity and the
nonnegativity of the certificate sum. -/
theorem entropy_optimality_certificate_scaledTable {m n : ℕ}
    (a : Fin m → ℝ) (K : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (S : Matrix (Fin m) (Fin n) ℝ)
    (hK : ∀ i j, 0 < K i j) (ha : ∀ i, 0 < a i)
    (hb : ∀ j, 0 < b j) (hS : ∀ i j, 0 ≤ S i j)
    (hrow : ∀ i, ∑ j, S i j = ∑ j, scaledTable a K b i j)
    (hcol : ∀ j, ∑ i, S i j = ∑ i, scaledTable a K b i j) :
    (∑ i, ∑ j, S i j * Real.log (S i j / K i j))
        - (∑ i, ∑ j, scaledTable a K b i j
            * Real.log (scaledTable a K b i j / K i j))
      = ∑ i, ∑ j, scaledTable a K b i j
          * klFun (S i j / scaledTable a K b i j)
    ∧ 0 ≤ ∑ i, ∑ j, scaledTable a K b i j
          * klFun (S i j / scaledTable a K b i j) := by
  have h := entropy_optimality_certificate (fun i j => K i j)
    (fun i j => S i j) a b hK ha hb hS
    (fun i => by simpa only [scaledTable] using hrow i)
    (fun j => by simpa only [scaledTable] using hcol j)
  simpa only [scaledTable] using h

end SinkhornMargins
