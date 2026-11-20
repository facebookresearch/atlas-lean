/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardRationalNormalization










namespace StatMech.FrontierA

open StatMech.Onsager.BaseCase


def kwHorizontalIntDirection (x : ℤ) : Fin 4 :=
  if 0 ≤ x then 0 else 2


def kwVerticalIntDirection (y : ℤ) : Fin 4 :=
  if 0 ≤ y then 1 else 3


def kwIntegralAxisWord (v : ℤ × ℤ) : List (Fin 4) :=
  List.replicate v.1.natAbs (kwHorizontalIntDirection v.1) ++
    List.replicate v.2.natAbs (kwVerticalIntDirection v.2)

@[simp] theorem stepOf_kwHorizontalIntDirection_nonneg
    {x : ℤ} (hx : 0 ≤ x) :
    stepOf (kwHorizontalIntDirection x) = (1, 0) := by
  simp [kwHorizontalIntDirection, hx, stepOf]

@[simp] theorem stepOf_kwHorizontalIntDirection_neg
    {x : ℤ} (hx : x < 0) :
    stepOf (kwHorizontalIntDirection x) = (-1, 0) := by
  simp [kwHorizontalIntDirection, not_le.mpr hx, stepOf]

@[simp] theorem stepOf_kwVerticalIntDirection_nonneg
    {y : ℤ} (hy : 0 ≤ y) :
    stepOf (kwVerticalIntDirection y) = (0, 1) := by
  simp [kwVerticalIntDirection, hy, stepOf]

@[simp] theorem stepOf_kwVerticalIntDirection_neg
    {y : ℤ} (hy : y < 0) :
    stepOf (kwVerticalIntDirection y) = (0, -1) := by
  simp [kwVerticalIntDirection, not_le.mpr hy, stepOf]

theorem sum_replicate_horizontalDirection (x : ℤ) :
    (List.replicate x.natAbs
      (stepOf (kwHorizontalIntDirection x))).sum = (x, 0) := by
  by_cases hx : 0 ≤ x
  · rw [stepOf_kwHorizontalIntDirection_nonneg hx]
    simp only [List.sum_replicate, nsmul_eq_mul]
    apply Prod.ext
    · simp only [Prod.fst_mul]
      simp [abs_of_nonneg hx]
    · simp
  · have hxneg : x < 0 := lt_of_not_ge hx
    rw [stepOf_kwHorizontalIntDirection_neg hxneg]
    simp only [List.sum_replicate]
    apply Prod.ext
    · simp only [Prod.smul_fst]
      simp [abs_of_neg hxneg]
    · simp

theorem sum_replicate_verticalDirection (y : ℤ) :
    (List.replicate y.natAbs
      (stepOf (kwVerticalIntDirection y))).sum = (0, y) := by
  by_cases hy : 0 ≤ y
  · rw [stepOf_kwVerticalIntDirection_nonneg hy]
    simp only [List.sum_replicate]
    apply Prod.ext
    · simp
    · simp [abs_of_nonneg hy]
  · have hyneg : y < 0 := lt_of_not_ge hy
    rw [stepOf_kwVerticalIntDirection_neg hyneg]
    simp only [List.sum_replicate]
    apply Prod.ext
    · simp
    · simp [abs_of_neg hyneg]


theorem kwIntegralAxisWord_step_sum (v : ℤ × ℤ) :
    ((kwIntegralAxisWord v).map stepOf).sum = v := by
  rw [kwIntegralAxisWord, List.map_append, List.sum_append,
    List.map_replicate, List.map_replicate,
    sum_replicate_horizontalDirection, sum_replicate_verticalDirection]
  apply Prod.ext <;> simp

theorem kwIntegralAxisWord_length (v : ℤ × ℤ) :
    (kwIntegralAxisWord v).length = v.1.natAbs + v.2.natAbs := by
  simp [kwIntegralAxisWord]


theorem kwIntegralAxisWord_ne_nil {v : ℤ × ℤ} (hv : v ≠ 0) :
    kwIntegralAxisWord v ≠ [] := by
  intro hnil
  have hsum := kwIntegralAxisWord_step_sum v
  rw [hnil] at hsum
  simpa using hv hsum.symm


def kwIntegralPolygonEdgeWord {n : ℕ} [NeZero n]
    (p : Fin n → ℤ × ℤ) (i : Fin n) : List (Fin 4) :=
  kwIntegralAxisWord (p (i + 1) - p i)


def kwIntegralPolygonWord {n : ℕ} [NeZero n]
    (p : Fin n → ℤ × ℤ) : List (Fin 4) :=
  (List.ofFn (kwIntegralPolygonEdgeWord p)).flatten

theorem kwIntegralPolygonEdgeWord_step_sum
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) (i : Fin n) :
    ((kwIntegralPolygonEdgeWord p i).map stepOf).sum =
      p (i + 1) - p i :=
  kwIntegralAxisWord_step_sum _


theorem kwIntegralPolygonWord_step_sum
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) :
    ((kwIntegralPolygonWord p).map stepOf).sum = 0 := by
  calc
    ((kwIntegralPolygonWord p).map stepOf).sum =
        (List.ofFn (fun i : Fin n ↦
          ((kwIntegralPolygonEdgeWord p i).map stepOf).sum)).sum := by
      simp [kwIntegralPolygonWord]
      rfl
    _ =
        ∑ i : Fin n, ((kwIntegralPolygonEdgeWord p i).map stepOf).sum := by
      rw [List.sum_ofFn]
    _ = ∑ i : Fin n, (p (i + 1) - p i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact kwIntegralPolygonEdgeWord_step_sum p i
    _ = 0 := by
      rw [Finset.sum_sub_distrib]
      have hshift : (∑ i : Fin n, p (i + 1)) = ∑ i : Fin n, p i :=
        Equiv.sum_comp (Equiv.addRight (1 : Fin n)) p
      rw [hshift, sub_self]



theorem kwIntegralPolygonWord_ne_nil
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ)
    (hn : 2 ≤ n) (hp : Function.Injective p) :
    kwIntegralPolygonWord p ≠ [] := by
  have hedge : p ((0 : Fin n) + 1) - p 0 ≠ 0 := by
    rw [sub_ne_zero]
    exact hp.ne (by
      apply Fin.ne_of_val_ne
      simp [Nat.mod_eq_of_lt hn])
  have hword := kwIntegralAxisWord_ne_nil hedge
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hword
  intro hempty
  have hdall : d ∈ kwIntegralPolygonWord p := by
    rw [kwIntegralPolygonWord, List.mem_flatten]
    refine ⟨kwIntegralPolygonEdgeWord p 0, ?_, hd⟩
    exact List.mem_ofFn.mpr ⟨0, rfl⟩
  simp only [hempty, List.not_mem_nil] at hdall



def kwIntegralPolygonDirection
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ)
    (k : Fin (kwIntegralPolygonWord p).length) : Fin 4 :=
  (kwIntegralPolygonWord p).get k


theorem kwIntegralPolygonDirection_closed
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) :
    ∑ k, stepOf (kwIntegralPolygonDirection p k) = 0 := by
  rw [← kwIntegralPolygonWord_step_sum p]
  simp [kwIntegralPolygonDirection]

end StatMech.FrontierA
