/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.ShermanGenericCancellation










namespace StatMech.Onsager

open Matrix BigOperators

def ons_scaleColumns {E : Type*} [DecidableEq E]
    (S : Finset E) (t : ℂ) (Lambda : Matrix E E ℂ) : Matrix E E ℂ :=
  fun i j => if j ∈ S then t * Lambda i j else Lambda i j

theorem ons_edgeWeight_scale_to_last
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
      simp only [ons_scaleColumns, if_neg hx]
      have hih :
          ons_edgeWeight (ons_scaleColumns S t Lambda) (x :: (xs ++ [e])) =
            t * ons_edgeWeight Lambda (x :: (xs ++ [e])) := by
        simpa only [List.cons_append] using ih x hxs
      rw [hih]
      ring

theorem ons_firstReturnWeight_scale
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
      simp only [ons_firstReturnWeight, if_pos hvalid],
      show ons_firstReturnWeight Lambda e r s = ons_edgeWeight Lambda s by
        simp only [ons_firstReturnWeight, if_pos hvalid]]
    obtain ⟨interior, hs, hintE⟩ := hvalid.1
    subst s
    have hint : ∀ x ∈ interior, x ∉ ({e, r} : Finset E) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hintE x hx, hvalid.2 x (by simp [hx])⟩
    exact ons_edgeWeight_scale_to_last
      ({e, r} : Finset E) t Lambda e e interior (by simp) hint
  · simp only [ons_firstReturnWeight, if_neg hvalid, mul_zero]

theorem ons_tsum_firstReturnWeight_scale
    {E : Type*} [Fintype E] [DecidableEq E]
    (Lambda : Matrix E E ℂ) (e r : E) (t : ℂ) :
    (∑' s, ons_firstReturnWeight
        (ons_scaleColumns ({e, r} : Finset E) t Lambda) e r s) =
      t * ∑' s, ons_firstReturnWeight Lambda e r s := by
  rw [tsum_congr (ons_firstReturnWeight_scale Lambda e r t),
    tsum_mul_left]

end StatMech.Onsager
