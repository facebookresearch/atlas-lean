/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanGenericCancellation

/-!

# Scaling first-return weights

Multiplying the columns of a matrix indexed by a set `S` scales first-return weights at a root in
`S`.

## i. Overview

Scaling the columns indexed by `S` by `t` multiplies the weight of a walk by `t` for each step into
`S`. A first-return segment at `e ∈ S` whose interior avoids `S` enters `S` only at its last step,
so its weight scales by exactly `t`, and so does the total first-return weight.

## ii. Key results

- `ons_scaleColumns` : column scaling
- `ons_firstReturnWeight_scale` : scaling of a first-return weight
- `ons_tsum_firstReturnWeight_scale` : scaling of the total first-return weight

## iii. Table of contents

- A. Column scaling and first returns

## iv. References

- None; the material is standard.

-/

@[expose] public section

namespace StatMech.Onsager

open Matrix BigOperators

/-! ## A. Column scaling and first returns -/

/-- The matrix `Λ` with every column indexed by an element of `S` multiplied by `t`. -/
def ons_scaleColumns {E : Type*} [DecidableEq E]
    (S : Finset E) (t : ℂ) (Lambda : Matrix E E ℂ) : Matrix E E ℂ :=
  fun i j => if j ∈ S then t * Lambda i j else Lambda i j

lemma ons_edgeWeight_scale_to_last
    {E : Type*} [DecidableEq E]
    (S : Finset E) (t : ℂ) (Lambda : Matrix E E ℂ)
    (a e : E) (interior : List E)
    (he : e ∈ S) (hint : ∀ x ∈ interior, x ∉ S) :
    ons_edgeWeight (ons_scaleColumns S t Lambda)
        (a :: interior ++ [e]) =
      t * ons_edgeWeight Lambda (a :: interior ++ [e]) := by
  induction interior generalizing a with
  | nil =>
      simp only [List.cons_append, List.nil_append]
      rw [ons_edgeWeight_cons_cons, ons_edgeWeight_cons_cons,
        ons_edgeWeight_singleton, ons_edgeWeight_singleton]
      simp [ons_scaleColumns, he]
  | cons x xs ih =>
      have hx : x ∉ S := hint x (by simp)
      have hxs : ∀ y ∈ xs, y ∉ S := by
        intro y hy
        exact hint y (by simp [hy])
      simp only [List.cons_append]
      rw [ons_edgeWeight_cons_cons, ons_edgeWeight_cons_cons]
      simp only [ons_scaleColumns, ite_eq_right hx]
      have hih :
          ons_edgeWeight (ons_scaleColumns S t Lambda) (x :: (xs ++ [e])) =
            t * ons_edgeWeight Lambda (x :: (xs ++ [e])) := by
        simpa only [List.cons_append] using ih x hxs
      rw [hih]
      ring

lemma ons_firstReturnWeight_scale
    {E : Type*} [Fintype E] [DecidableEq E]
    (Lambda : Matrix E E ℂ) (e r : E)
    (t : ℂ) (s : List E) :
    ons_firstReturnWeight
        (ons_scaleColumns ({e, r} : Finset E) t Lambda) e r s =
      t * ons_firstReturnWeight Lambda e r s := by
  by_cases hvalid : ons_isFirstReturnSegment e s ∧ ∀ x ∈ s, x ≠ r
  · rw [show ons_firstReturnWeight
        (ons_scaleColumns ({e, r} : Finset E) t Lambda) e r s =
        ons_edgeWeight (ons_scaleColumns ({e, r} : Finset E) t Lambda) s by
      simp only [ons_firstReturnWeight, ite_eq_left hvalid],
      show ons_firstReturnWeight Lambda e r s = ons_edgeWeight Lambda s by
        simp only [ons_firstReturnWeight, ite_eq_left hvalid]]
    obtain ⟨interior, hs, hintE⟩ := hvalid.1
    subst s
    have hint : ∀ x ∈ interior, x ∉ ({e, r} : Finset E) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hintE x hx, hvalid.2 x (by simp [hx])⟩
    exact ons_edgeWeight_scale_to_last
      ({e, r} : Finset E) t Lambda e e interior (by simp) hint
  · simp only [ons_firstReturnWeight, ite_eq_right hvalid, mul_zero]

lemma ons_tsum_firstReturnWeight_scale
    {E : Type*} [Fintype E] [DecidableEq E]
    (Lambda : Matrix E E ℂ) (e r : E) (t : ℂ) :
    (∑' s, ons_firstReturnWeight
        (ons_scaleColumns ({e, r} : Finset E) t Lambda) e r s) =
      t * ∑' s, ons_firstReturnWeight Lambda e r s := by
  rw [tsum_congr (ons_firstReturnWeight_scale Lambda e r t),
    tsum_mul_left]

end StatMech.Onsager
