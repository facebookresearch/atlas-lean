/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Omics.Normalization
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Subcompositional coherence of the centered log-ratio transform

A **subcomposition** keeps only the parts in a subset `S` of the parts of a composition, for
example a panel of genes or a group of taxa out of a full sequencing profile. Aitchison's
principle of *subcompositional coherence* asks that an analysis of the parts in `S` should not
depend on whether the other parts were measured. This file proves that the centered log-ratio
transform `clr` of `Domains.Biology.Omics.Normalization` (T40) satisfies the principle in the
following precise senses, and that raw proportions do not.

The subcomposition is `subcomp S x`, the strictly positive vector `(x i)_{i ∈ S}` indexed by
the subtype of `S`. Aitchison's subcomposition is its closure `closureOp (subcomp S x)`, the
same vector rescaled to total `1`; because `clr` is scale invariant, both give the same CLR
transform (`clr_closureOp`), so the statements below hold for either convention. The closure is
only defined for at least one part (`[Nonempty ι]`, and `[Nonempty S]`, i.e. `S.Nonempty`, for a
closed subcomposition): with no parts the total is `0` and no rescaling has total `1`.

## Main definitions

* `subcomp S x`: the parts of the positive composition `x` in the finite set `S`.
* `closureOp x`: the closure operation, `x` rescaled to total `1`, for a nonempty index type.
* `aitchisonDistSq x y`: the squared Aitchison distance `∑ i, (clr x i - clr y i) ^ 2`.

## Main results

* `clr_subcomp_sub_clr_subcomp`: **log-ratio coherence**. Within `S`, CLR differences of the
  subcomposition equal CLR differences of the full composition (both are `log (x i / x j)`).
* `clr_subcomp`: the CLR of a subcomposition is the restriction of the full CLR, re-centred over
  `S`: `clr (subcomp S x) i = clr x i - (∑ j ∈ S, clr x j) / #S`.
* `clr_subcomp_congr`: the CLR of a subcomposition is a function of the full CLR alone; hence
  it does not depend on the total (`clr_subcomp_smul`) nor on closing the full composition
  first (`clr_subcomp_closureOp`).
* `clr_subcomp_univ`: the trivial subcomposition `S = univ` has the full CLR.
* `aitchisonDistSq_subcomp_le`: **subcompositional dominance**. The Aitchison distance between
  two subcompositions is at most the Aitchison distance between the full compositions.
* `closureOp_subcomp_apply_eq_iff`: in contrast, a closed proportion of a part in `S` is
  unchanged by passing to the closed subcomposition only when `S = univ`.

## References

* J. Aitchison, *The statistical analysis of compositional data*, Chapman & Hall (1986),
  §2.2 (subcompositions, closure) and §4 (log-ratios and subcompositional coherence).
* J. Aitchison, *On criteria for measures of compositional difference*, Math. Geol. 24 (1992),
  365–379: subcompositional dominance of a distance as a requirement.
* V. Pawlowsky-Glahn, J. J. Egozcue, R. Tolosana-Delgado, *Modeling and Analysis of
  Compositional Data*, Wiley (2015), §2.3: subcompositional coherence and dominance of the
  Aitchison distance.

## Reuse receipt (API-00)

T40 (`Biology/Omics/Normalization.lean`) defines `PosComposition`, `clr`, `PosComposition.smul`
and proves `clr_smul`, `clr_perm`, `sum_clr`, `clr_le_clr_iff`, `clr_eq_clr_iff` and the
pseudocount results. It has no subcomposition, closure, or Aitchison distance and nothing about
subsets of the parts, so none of the results here duplicate it; they reuse `clr`, `clr_smul`
and `sum_clr`. Searched `MathlibExt`, `CSLibExt`, `WantedExt` and pinned Mathlib for
`subcomposition`, `subcompositional`, `Aitchison`, `closure operation` and `log-ratio`: no other
hits. The re-centring inequality `sum_sq_sub_mean_le` is proved from Mathlib's `Finset` sum
lemmas.
-/

@[expose] public section

open Finset MathlibExt.Biology.Omics.Normalization

namespace MathlibExt.Biology.Omics.CompositionalCoherence

variable {ι : Type*} [Fintype ι]

/-- The **subcomposition** of `x` on the parts in `S`: the positive vector `(x i)_{i ∈ S}`
indexed by the subtype of `S`. -/
def subcomp (S : Finset ι) (x : PosComposition ι) : PosComposition S :=
  ⟨fun i => x.1 i, fun i => x.2 i⟩

/-- The **closure operation**: rescale a positive composition with at least one part to
total `1`. Without parts the total would be `0`, so the index type must be nonempty. -/
noncomputable def closureOp [Nonempty ι] (x : PosComposition ι) : PosComposition ι :=
  ⟨fun i => x.1 i / ∑ j, x.1 j,
    fun i => div_pos (x.2 i) (sum_pos (fun j _ => x.2 j) univ_nonempty)⟩

/-- The squared **Aitchison distance** `∑ i, (clr x i - clr y i) ^ 2`. -/
noncomputable def aitchisonDistSq (x y : PosComposition ι) : ℝ :=
  ∑ i, (clr x i - clr y i) ^ 2

/-! ### Closure -/

/-- The closure is the rescaling by the reciprocal of the total. -/
theorem closureOp_eq_smul [Nonempty ι] (x : PosComposition ι) :
    closureOp x =
      x.smul (1 / ∑ j, x.1 j) (one_div_pos.2 (sum_pos (fun j _ => x.2 j) univ_nonempty)) := by
  apply Subtype.ext
  funext i
  simp only [closureOp, PosComposition.smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- A closed composition has total `1`. -/
theorem sum_closureOp [Nonempty ι] (x : PosComposition ι) : ∑ i, (closureOp x).1 i = 1 := by
  have hS : (∑ j, x.1 j) ≠ 0 := (sum_pos (fun j _ => x.2 j) univ_nonempty).ne'
  simp only [closureOp, ← sum_div]
  exact div_self hS

/-- Closing a composition does not change its CLR transform. -/
theorem clr_closureOp [Nonempty ι] (x : PosComposition ι) : clr (closureOp x) = clr x := by
  rw [closureOp_eq_smul, clr_smul]

/-! ### Log-ratio coherence -/

/-- **Log-ratio coherence.** For parts `i, j ∈ S`, the CLR difference computed from the
subcomposition equals the CLR difference computed from the full composition. -/
theorem clr_subcomp_sub_clr_subcomp (S : Finset ι) (x : PosComposition ι) (i j : S) :
    clr (subcomp S x) i - clr (subcomp S x) j = clr x i - clr x j := by
  simp only [clr, subcomp]
  ring

omit [Fintype ι] in
/-- The CLR difference of a subcomposition is the log-ratio `log (x i / x j)`. -/
theorem clr_subcomp_sub_eq_log_div (S : Finset ι) (x : PosComposition ι) (i j : S) :
    clr (subcomp S x) i - clr (subcomp S x) j = Real.log (x.1 i / x.1 j) := by
  rw [Real.log_div (x.2 i).ne' (x.2 j).ne']
  simp only [clr, subcomp]
  ring

/-! ### The CLR of a subcomposition from the full CLR -/

/-- **CLR of a subcomposition.** It is the restriction of the full CLR to `S`, re-centred to
have mean zero over `S`. -/
theorem clr_subcomp (S : Finset ι) (x : PosComposition ι) (i : S) :
    clr (subcomp S x) i = clr x i - (∑ j ∈ S, clr x j) / #S := by
  have hS : (#S : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (card_ne_zero_of_mem i.2)
  simp only [clr, subcomp, Fintype.card_coe, sum_coe_sort S (fun j => Real.log (x.1 j)),
    sum_sub_distrib, sum_const, nsmul_eq_mul]
  field_simp
  ring

/-- The CLR of a subcomposition is a function of the full CLR: compositions with the same CLR
have subcompositions with the same CLR. -/
theorem clr_subcomp_congr (S : Finset ι) {x y : PosComposition ι} (h : clr x = clr y) :
    clr (subcomp S x) = clr (subcomp S y) := by
  funext i
  rw [clr_subcomp, clr_subcomp, h]

omit [Fintype ι] in
/-- The CLR of a subcomposition does not depend on the total of the full composition. -/
theorem clr_subcomp_smul (S : Finset ι) (t : ℝ) (ht : 0 < t) (x : PosComposition ι) :
    clr (subcomp S (x.smul t ht)) = clr (subcomp S x) := by
  rw [show subcomp S (x.smul t ht) = (subcomp S x).smul t ht from rfl, clr_smul]

/-- Closing the full composition before taking the subcomposition does not change its CLR. -/
theorem clr_subcomp_closureOp [Nonempty ι] (S : Finset ι) (x : PosComposition ι) :
    clr (subcomp S (closureOp x)) = clr (subcomp S x) :=
  clr_subcomp_congr S (clr_closureOp x)

omit [Fintype ι] in
/-- Aitchison's closed subcomposition of a nonempty `S` has the same CLR as the unclosed one,
so it is also computed from the full CLR by `clr_subcomp`. -/
theorem clr_closureOp_subcomp (S : Finset ι) [Nonempty S] (x : PosComposition ι) :
    clr (closureOp (subcomp S x)) = clr (subcomp S x) :=
  clr_closureOp _

/-- The trivial subcomposition `S = univ` has the full CLR. -/
theorem clr_subcomp_univ (x : PosComposition ι) (i : (univ : Finset ι)) :
    clr (subcomp univ x) i = clr x i := by
  rw [clr_subcomp, sum_clr, zero_div, sub_zero]

/-! ### Subcompositional dominance -/

omit [Fintype ι] in
/-- Re-centring over `S` does not increase the sum of squares over `S`. For empty `S` both sides
are `0`; the mean is then `0 / 0`, which is `0` by the convention `x / 0 = 0`. -/
theorem sum_sq_sub_mean_le (S : Finset ι) (a : ι → ℝ) :
    ∑ i ∈ S, (a i - (∑ j ∈ S, a j) / #S) ^ 2 ≤ ∑ i ∈ S, a i ^ 2 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hc : (#S : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hne.card_pos.ne'
  set m := (∑ j ∈ S, a j) / #S with hm
  have hsum : ∑ j ∈ S, a j = #S * m := by rw [hm]; field_simp
  have e : ∀ i ∈ S, (a i - m) ^ 2 = a i ^ 2 - 2 * m * a i + m ^ 2 := fun i _ => by ring
  rw [sum_congr rfl e, sum_add_distrib, sum_sub_distrib, ← mul_sum, hsum, sum_const,
    nsmul_eq_mul]
  have := mul_nonneg (Nat.cast_nonneg (α := ℝ) #S) (sq_nonneg m)
  nlinarith

/-- **Subcompositional dominance of the Aitchison distance.** Passing to a subcomposition
never increases the Aitchison distance. -/
theorem aitchisonDistSq_subcomp_le (S : Finset ι) (x y : PosComposition ι) :
    aitchisonDistSq (subcomp S x) (subcomp S y) ≤ aitchisonDistSq x y := by
  set a : ι → ℝ := fun i => clr x i - clr y i with ha
  have h : ∀ i : S, clr (subcomp S x) i - clr (subcomp S y) i =
      a i - (∑ j ∈ S, a j) / #S := by
    intro i
    rw [clr_subcomp, clr_subcomp]
    simp only [ha, sum_sub_distrib]
    ring
  unfold aitchisonDistSq
  simp_rw [h]
  rw [sum_coe_sort S (fun i => (a i - (∑ j ∈ S, a j) / #S) ^ 2)]
  calc ∑ i ∈ S, (a i - (∑ j ∈ S, a j) / #S) ^ 2 ≤ ∑ i ∈ S, a i ^ 2 := sum_sq_sub_mean_le S a
    _ ≤ ∑ i, a i ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun i _ _ => sq_nonneg _)

/-! ### Contrast: proportions are not subcompositionally coherent -/

/-- **Proportions are incoherent.** For a part `i ∈ S`, its proportion in the closed
subcomposition equals its proportion in the closed full composition only when `S` contains
every part. The instances follow from `i`; they are there so that both closures elaborate. -/
theorem closureOp_subcomp_apply_eq_iff [Nonempty ι] (S : Finset ι) [Nonempty S]
    (x : PosComposition ι) (i : S) :
    (closureOp (subcomp S x)).1 i = (closureOp x).1 i ↔ S = univ := by
  have hpos : 0 < ∑ j ∈ S, x.1 j := sum_pos (fun j _ => x.2 j) ⟨i, i.2⟩
  have hposU : 0 < ∑ j, x.1 j := sum_pos (fun j _ => x.2 j) ⟨i, mem_univ _⟩
  simp only [closureOp, subcomp, sum_coe_sort S (fun j => x.1 j)]
  constructor
  · intro h
    have hsum : ∑ j ∈ S, x.1 j = ∑ j, x.1 j := by
      rw [div_eq_div_iff hpos.ne' hposU.ne'] at h
      exact (mul_left_cancel₀ (x.2 i).ne' h).symm
    by_contra hne
    obtain ⟨k, hk⟩ : ∃ k, k ∉ S := by
      by_contra hall
      exact hne (eq_univ_of_forall fun k => not_not.1 fun hk => hall ⟨k, hk⟩)
    have := sum_lt_sum_of_subset (subset_univ S) (mem_univ k) hk (x.2 k)
      (fun j _ _ => (x.2 j).le)
    linarith
  · rintro rfl
    rfl

end MathlibExt.Biology.Omics.CompositionalCoherence
