/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanDetFactor
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanFirstReturn
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanSplit

/-!

# Loop weights through first-return factors

Loop weights as products over first-return segments, and the determinant factorization when the
first-return weights are geometric.

## i. Overview

A closed walk `v` of length `n + 1` is the list `v₀, …, vₙ, v₀`; its loop weight is the edge weight
of that list and factors over its first-return segments at any state `e`. If the bucket
`ons_bucketE` of walks through `e` (avoiding its reverse) has the geometric form `z ^ (n + 1)` with
`‖z‖ < 1`, the bucket series is summable, its exponential is of the form `1 - λ`, and the Kac-Ward
determinant factors as the determinant without `e` times `(1 - λ) ^ 2`.

## ii. Key results

- `ons_loopWeight_eq_edgeWeight` : a loop weight is the edge weight of the closed list
- `ons_loopWeight_eq_firstReturn_prod` : loop weights factor over first-return segments
- `ons_det_final_of_count` : determinant factorization from a geometric bucket count

## iii. Table of contents

- A. Loop weights as list weights
- B. Geometric buckets

## iv. References

- S. Sherman, *Combinatorial aspects of the Ising model for ferromagnetism. I. A conjecture of
  Feynman on paths and graphs*, J. Math. Phys. 1 (1960) 202-217

-/

@[expose] public section

namespace StatMech.Onsager

open Matrix BigOperators Finset

set_option linter.unusedSectionVars false

/-! ## A. Loop weights as list weights -/

lemma ons_edgeWeight_ofFn {E : Type*} (Λ : Matrix E E ℂ) (m : ℕ) (f : Fin (m + 1) → E) :
    ons_edgeWeight Λ (List.ofFn f) = ∏ i : Fin m, Λ (f i.castSucc) (f i.succ) := by
  induction m with
  | zero => simp [List.ofFn_succ]
  | succ m ih =>
      rw [List.ofFn_succ]
      set g : Fin (m + 1) → E := fun i => f i.succ with hg
      have hgcons : List.ofFn g = g 0 :: List.ofFn (fun i : Fin m => g i.succ) := by
        rw [List.ofFn_succ]
      rw [hgcons, ons_edgeWeight_cons_cons, ← hgcons, ih g, Fin.prod_univ_succ]
      simp only [hg, Fin.castSucc_zero, Fin.succ_castSucc]

lemma ons_snoc_succ {E : Type*} {n : ℕ} (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    (Fin.snoc v (v 0) : Fin (n + 2) → E) i.succ = v (i + 1) := by
  rcases eq_or_ne i (Fin.last n) with rfl | hne
  · rw [Fin.succ_last, Fin.snoc_last, Fin.last_add_one]
  · have hlt : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) hne
    have hval : (i + 1 : Fin (n + 1)).val = i.val + 1 := Fin.val_add_one_of_lt hlt
    have hcast : i.succ = (i + 1 : Fin (n + 1)).castSucc := by
      apply Fin.ext
      rw [Fin.val_succ, Fin.val_castSucc, hval]
    rw [hcast, Fin.snoc_castSucc]

lemma ons_loopWeight_eq_edgeWeight {E : Type*} [Fintype E] [DecidableEq E] (Λ : Matrix E E ℂ)
    {n : ℕ} (v : Fin (n + 1) → E) :
    ons_loopWeight Λ v = ons_edgeWeight Λ (List.ofFn v ++ [v 0]) := by
  have hlist : List.ofFn v ++ [v 0] = List.ofFn (Fin.snoc v (v 0) : Fin (n + 2) → E) := by
    rw [List.ofFn_succ' (Fin.snoc v (v 0) : Fin (n + 2) → E)]
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  rw [hlist, ons_edgeWeight_ofFn]
  unfold ons_loopWeight
  apply Finset.prod_congr rfl
  intro i _
  rw [Fin.snoc_castSucc, ons_snoc_succ]

lemma ons_loopWeight_eq_firstReturn_prod {E : Type*} [Fintype E] [DecidableEq E]
    (Λ : Matrix E E ℂ) {n : ℕ} (e : E) (v : Fin (n + 1) → E) :
    ons_loopWeight Λ v
      = ((ons_firstReturnSplit e (List.ofFn v ++ [v 0])).map (ons_edgeWeight Λ)).prod := by
  rw [ons_loopWeight_eq_edgeWeight]
  exact (ons_edgeWeight_firstReturnSplit Λ e _).symm

/-! ## B. Geometric buckets -/

lemma ons_summable_bucketE_of_count {L : ℕ} [NeZero L] (x ω : ℂ) (e : ons_Dart L) {z : ℂ}
    (hz : ‖z‖ < 1) (hcount : ∀ n : ℕ, ons_bucketE L x ω e n = z ^ (n + 1)) :
    Summable (fun n : ℕ => ons_bucketE L x ω e n / ((n : ℂ) + 1)) := by
  have hfun : (fun n : ℕ => ons_bucketE L x ω e n / ((n : ℂ) + 1))
      = (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1)) := by
    funext n; rw [hcount n]
  rw [hfun]
  exact (Complex.hasSum_taylorSeries_neg_log' hz).summable

lemma ons_hlam {L : ℕ} [NeZero L] [Fact (2 < L)] (x ω : ℂ) (e : ons_Dart L) {z : ℂ}
    (hz : ‖z‖ < 1) (hcount : ∀ n : ℕ, ons_bucketE L x ω e n = z ^ (n + 1)) :
    ∃ lam : ℂ,
      Complex.exp (- ∑' n : ℕ, ons_bucketE L x ω e n / ((n : ℂ) + 1)) = 1 - lam := by
  refine ⟨z, ?_⟩
  have hcong : (∑' n : ℕ, ons_bucketE L x ω e n / ((n : ℂ) + 1))
      = ∑' k : ℕ, z ^ (k + 1) / ((k : ℂ) + 1) := by
    apply tsum_congr; intro n; rw [hcount n]
  rw [hcong]
  exact ons_lemma4_exp hz

lemma ons_det_final_of_count {L : ℕ} [NeZero L] [Fact (2 < L)] (x ω : ℂ)
    (hω : ω ^ 2 = Complex.I) (e : ons_Dart L)
    (hspec : ∀ α ∈ (ons_KWmat L x ω).charpoly.roots, ‖α‖ < 1)
    {z : ℂ} (hz : ‖z‖ < 1) (hcount : ∀ n : ℕ, ons_bucketE L x ω e n = z ^ (n + 1))
    (hN : Summable (fun n : ℕ => ons_bucketN L x ω e n / ((n : ℂ) + 1))) :
    (1 - ons_KWmat L x ω).det
      = Complex.exp (- ∑' n : ℕ, ons_bucketN L x ω e n / ((n : ℂ) + 1)) * (1 - z) ^ 2 := by
  have hB := ons_summable_bucketE_of_count x ω e hz hcount
  have hlam : Complex.exp (- ∑' n : ℕ, ons_bucketE L x ω e n / ((n : ℂ) + 1)) = 1 - z := by
    have hcong : (∑' n : ℕ, ons_bucketE L x ω e n / ((n : ℂ) + 1))
        = ∑' k : ℕ, z ^ (k + 1) / ((k : ℂ) + 1) := by
      apply tsum_congr; intro n; rw [hcount n]
    rw [hcong]; exact ons_lemma4_exp hz
  exact ons_det_eq_A_mul_sq x ω hω e hspec hB hN z hlam

end StatMech.Onsager
