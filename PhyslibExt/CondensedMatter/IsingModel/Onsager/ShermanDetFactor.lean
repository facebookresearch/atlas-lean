/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanLoopSplit
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanLoopReversal
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.DetWalkExp

/-!

# The Kac-Ward determinant factored at a dart

Writing `det (1 - Λ)` as the determinant with a dart removed times the square of a first-return
factor.

## i. Overview

With the buckets `ons_bucketE` (closed walks of length `n + 1` visiting `e` but not its reverse) and
`ons_bucketN` (walks visiting neither), the loop sum of length `n + 1` is `2 · bucketE + bucketN`.
Under summability this factors the determinant as
`det (1 - Λ) = exp (-∑ bucketN / (n + 1)) · (1 - λ) ^ 2`, where `1 - λ` is the exponential of the
`bucketE` series. Iterating over darts gives Sherman's product formula.

## ii. Key results

- `ons_bucketE` : closed walks visiting `e` but not its reverse
- `ons_bucketN` : closed walks visiting neither `e` nor its reverse
- `ons_KW_loopSum_two_bucket` : the loop sum is `2 · bucketE + bucketN`
- `ons_det_eq_A_mul_sq` : the determinant factored at a dart

## iii. Table of contents

- A. Buckets
- B. Determinant factorization

## iv. References

- S. Sherman, *Combinatorial aspects of the Ising model for ferromagnetism. I. A conjecture of
  Feynman on paths and graphs*, J. Math. Phys. 1 (1960) 202-217

-/

@[expose] public section

namespace StatMech.Onsager

open Matrix BigOperators Finset

section Bucket

variable {L : ℕ} [NeZero L]

/-! ## A. Buckets -/

/-- The total Kac-Ward weight of closed walks of length `n + 1` that visit `e` but not its reverse.
-/
noncomputable def ons_bucketE (L : ℕ) [NeZero L] (x ω : ℂ) (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → ons_Dart L =>
      (∃ i, v i = e) ∧ ¬ (∃ j, v j = ons_dartRev L e)),
    ons_loopWeight (ons_KWmat L x ω) v

/-- The total Kac-Ward weight of closed walks of length `n + 1` that visit neither `e` nor its
reverse. -/
noncomputable def ons_bucketN (L : ℕ) [NeZero L] (x ω : ℂ) (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → ons_Dart L =>
      ¬ (∃ i, v i = e) ∧ ¬ (∃ j, v j = ons_dartRev L e)),
    ons_loopWeight (ons_KWmat L x ω) v

lemma ons_KW_loopSum_two_bucket [Fact (2 < L)] {n : ℕ} (x ω : ℂ) (hω : ω ^ 2 = Complex.I)
    (e : ons_Dart L) :
    (∑ v : Fin (n + 1) → ons_Dart L, ons_loopWeight (ons_KWmat L x ω) v)
      = 2 * ons_bucketE L x ω e n + ons_bucketN L x ω e n := by
  simp only [ons_bucketE, ons_bucketN, ons_loopWeight]
  have hno := ons_KW_loopSum_no_both (L := L) n x ω hω e
  have hsymm := ons_loopSum_symm (L := L) (n := n + 1) x ω hω e
  simp only [ons_loopWeight] at hsymm
  have hset : (Finset.univ.filter (fun v : Fin (n + 1) → ons_Dart L =>
        (∃ i, v i = ons_dartRev L e) ∧ ¬ ∃ j, v j = e))
      = (Finset.univ.filter (fun v : Fin (n + 1) → ons_Dart L =>
        ¬ (∃ i, v i = e) ∧ (∃ j, v j = ons_dartRev L e))) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hset] at hsymm
  linear_combination hno - hsymm

end Bucket

section Det

variable {L : ℕ} [NeZero L] [Fact (2 < L)]

/-! ## B. Determinant factorization -/

lemma ons_det_eq_two_bucket_exp (x ω : ℂ) (hω : ω ^ 2 = Complex.I) (e : ons_Dart L)
    (hspec : ∀ α ∈ (ons_KWmat L x ω).charpoly.roots, ‖α‖ < 1) :
    (1 - ons_KWmat L x ω).det
      = Complex.exp (- ∑' n : ℕ,
          (2 * ons_bucketE L x ω e n + ons_bucketN L x ω e n) / ((n : ℂ) + 1)) := by
  rw [ons_det_eq_walk_exp (ons_KWmat L x ω) hspec]
  refine congrArg Complex.exp (congrArg Neg.neg (tsum_congr (fun n => ?_)))
  exact congrArg (· / ((n : ℂ) + 1)) (ons_KW_loopSum_two_bucket (L := L) (n := n) x ω hω e)

lemma ons_det_eq_A_mul_bucket (x ω : ℂ) (hω : ω ^ 2 = Complex.I) (e : ons_Dart L)
    (hspec : ∀ α ∈ (ons_KWmat L x ω).charpoly.roots, ‖α‖ < 1)
    (hB : Summable (fun n : ℕ => ons_bucketE L x ω e n / ((n : ℂ) + 1)))
    (hN : Summable (fun n : ℕ => ons_bucketN L x ω e n / ((n : ℂ) + 1))) :
    (1 - ons_KWmat L x ω).det
      = Complex.exp (- ∑' n : ℕ, ons_bucketN L x ω e n / ((n : ℂ) + 1))
        * Complex.exp (-2 * ∑' n : ℕ, ons_bucketE L x ω e n / ((n : ℂ) + 1)) := by
  have hsplit : (∑' n : ℕ,
        (2 * ons_bucketE L x ω e n + ons_bucketN L x ω e n) / ((n : ℂ) + 1))
      = 2 * (∑' n : ℕ, ons_bucketE L x ω e n / ((n : ℂ) + 1))
        + (∑' n : ℕ, ons_bucketN L x ω e n / ((n : ℂ) + 1)) := by
    have e1 : (fun n : ℕ =>
          (2 * ons_bucketE L x ω e n + ons_bucketN L x ω e n) / ((n : ℂ) + 1))
        = (fun n : ℕ => 2 * (ons_bucketE L x ω e n / ((n : ℂ) + 1))
            + ons_bucketN L x ω e n / ((n : ℂ) + 1)) := by
      funext n; ring
    rw [e1, (hB.mul_left 2).tsum_add hN, tsum_mul_left]
  rw [ons_det_eq_two_bucket_exp (L := L) x ω hω e hspec, hsplit]
  rw [show -(2 * (∑' n : ℕ, ons_bucketE L x ω e n / ((n : ℂ) + 1))
        + (∑' n : ℕ, ons_bucketN L x ω e n / ((n : ℂ) + 1)))
      = (-(∑' n : ℕ, ons_bucketN L x ω e n / ((n : ℂ) + 1)))
        + (-2 * ∑' n : ℕ, ons_bucketE L x ω e n / ((n : ℂ) + 1)) from by ring]
  rw [Complex.exp_add]

lemma ons_det_eq_A_mul_sq (x ω : ℂ) (hω : ω ^ 2 = Complex.I) (e : ons_Dart L)
    (hspec : ∀ α ∈ (ons_KWmat L x ω).charpoly.roots, ‖α‖ < 1)
    (hB : Summable (fun n : ℕ => ons_bucketE L x ω e n / ((n : ℂ) + 1)))
    (hN : Summable (fun n : ℕ => ons_bucketN L x ω e n / ((n : ℂ) + 1)))
    (lam : ℂ)
    (hlam : Complex.exp (- ∑' n : ℕ, ons_bucketE L x ω e n / ((n : ℂ) + 1)) = 1 - lam) :
    (1 - ons_KWmat L x ω).det
      = Complex.exp (- ∑' n : ℕ, ons_bucketN L x ω e n / ((n : ℂ) + 1)) * (1 - lam) ^ 2 := by
  rw [ons_det_eq_A_mul_bucket (L := L) x ω hω e hspec hB hN]
  congr 1
  rw [pow_two, ← hlam, ← Complex.exp_add]
  congr 1
  ring

end Det

end StatMech.Onsager
