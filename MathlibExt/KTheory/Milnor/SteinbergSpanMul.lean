/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Milnor.ClassicalDegreeSteinbergSpan

/-!
# Multiplication closure of the Steinberg span

The degreewise Steinberg span is stable under left and right multiplication
by tensor words and by homogeneous components.
-/

@[expose] public section

open TensorAlgebra

namespace MilnorK

variable (F : Type*) [Field F]

namespace TensorRing

/-- Left multiplication by a tensor word preserves `steinbergInsertSet`. -/
theorem tensorList_mul_steinbergInsert_mem_steinbergInsertSet
    {q : ℕ} {x : TensorRing F} (hx : x ∈ steinbergInsertSet F q)
    (zs : List Fˣ) :
    tensorList F zs * x ∈ steinbergInsertSet F (zs.length + q) := by
  rcases hx with ⟨xs, ys, a, ha0, ha1, hlen, rfl⟩
  let pair : TensorRing F :=
    TensorAlgebra.ι ℤ (Additive.ofMul (Units.mk0 a ha0)) *
      TensorAlgebra.ι ℤ (Additive.ofMul (Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)))
  refine ⟨zs ++ xs, ys, a, ha0, ha1, ?_, ?_⟩
  · have h1 : (zs ++ xs).length = zs.length + xs.length := by simp
    calc (zs ++ xs).length + ys.length + 2
        = zs.length + xs.length + ys.length + 2 := by rw [h1]
      _ = zs.length + (xs.length + ys.length + 2) := by ac_rfl
      _ = zs.length + q := by rw [hlen]
  · have h_append : tensorList F zs * tensorList F xs = tensorList F (zs ++ xs) := by
      rw [← tensorList_append F zs xs]
    calc tensorList F zs * (tensorList F xs * pair * tensorList F ys)
        = tensorList F zs * tensorList F xs * pair * tensorList F ys := by
          simp only [mul_assoc]
      _ = tensorList F (zs ++ xs) * pair * tensorList F ys := by
          rw [h_append]

/-- Right multiplication by a tensor word preserves `steinbergInsertSet`. -/
theorem steinbergInsert_mul_tensorList_mem_steinbergInsertSet
    {q : ℕ} {x : TensorRing F} (hx : x ∈ steinbergInsertSet F q)
    (zs : List Fˣ) :
    x * tensorList F zs ∈ steinbergInsertSet F (q + zs.length) := by
  rcases hx with ⟨xs, ys, a, ha0, ha1, hlen, rfl⟩
  let pair : TensorRing F :=
    TensorAlgebra.ι ℤ (Additive.ofMul (Units.mk0 a ha0)) *
      TensorAlgebra.ι ℤ (Additive.ofMul (Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)))
  refine ⟨xs, ys ++ zs, a, ha0, ha1, ?_, ?_⟩
  · have h1 : (ys ++ zs).length = ys.length + zs.length := by simp
    calc xs.length + (ys ++ zs).length + 2
        = xs.length + (ys.length + zs.length) + 2 := by rw [h1]
      _ = xs.length + ys.length + zs.length + 2 := by ac_rfl
      _ = (xs.length + ys.length + 2) + zs.length := by ac_rfl
      _ = q + zs.length := by rw [hlen]
  · have h_append : tensorList F ys * tensorList F zs = tensorList F (ys ++ zs) := by
      rw [← tensorList_append F ys zs]
    calc tensorList F xs * pair * tensorList F ys * tensorList F zs
        = tensorList F xs * pair * (tensorList F ys * tensorList F zs) := by
          simp only [mul_assoc]
      _ = tensorList F xs * pair * tensorList F (ys ++ zs) := by rw [h_append]

/-- Left multiplication by a tensor word sends `steinbergInsertSet` into `steinbergDegreeSpan`. -/
private theorem tensorList_mul_steinbergInsert_mem_steinbergDegreeSpan
    {q : ℕ} {x : TensorRing F} (hx : x ∈ steinbergInsertSet F q)
    (zs : List Fˣ) :
    tensorList F zs * x ∈ steinbergDegreeSpan F (zs.length + q) :=
  Submodule.mem_span.mpr fun _ h =>
    h (tensorList_mul_steinbergInsert_mem_steinbergInsertSet F hx zs)

/-- Right multiplication by a tensor word sends `steinbergInsertSet` into `steinbergDegreeSpan`. -/
private theorem steinbergInsert_mul_tensorList_mem_steinbergDegreeSpan
    {q : ℕ} {x : TensorRing F} (hx : x ∈ steinbergInsertSet F q)
    (zs : List Fˣ) :
    x * tensorList F zs ∈ steinbergDegreeSpan F (q + zs.length) :=
  Submodule.mem_span.mpr fun _ h =>
    h (steinbergInsert_mul_tensorList_mem_steinbergInsertSet F hx zs)

/-- Left multiplication by a tensor word preserves `steinbergDegreeSpan`. -/
private theorem tensorList_mul_mem_steinbergDegreeSpan
    {q : ℕ} (zs : List Fˣ) {b : TensorRing F}
    (hb : b ∈ steinbergDegreeSpan F q) :
    tensorList F zs * b ∈ steinbergDegreeSpan F (zs.length + q) := by
  induction hb using Submodule.span_induction with
  | mem y hy =>
    exact tensorList_mul_steinbergInsert_mem_steinbergDegreeSpan F hy zs
  | zero =>
    have : tensorList F zs * (0 : TensorRing F) = 0 := by rw [mul_zero]
    rw [this]
    exact Submodule.zero_mem (steinbergDegreeSpan F (zs.length + q))
  | add y z _ _ hy hz =>
    have h_eq : tensorList F zs * (y + z) = tensorList F zs * y + tensorList F zs * z := by
      rw [mul_add]
    rw [h_eq]
    exact Submodule.add_mem (steinbergDegreeSpan F (zs.length + q)) hy hz
  | smul c y _ hy =>
    have h_eq : tensorList F zs * (c • y) = c • (tensorList F zs * y) := by
      rw [Algebra.mul_smul_comm]
    rw [h_eq]
    exact Submodule.smul_mem (steinbergDegreeSpan F (zs.length + q)) _ hy

/-- Right multiplication by a tensor word preserves `steinbergDegreeSpan`. -/
private theorem mem_steinbergDegreeSpan_mul_tensorList
    {p : ℕ} {a : TensorRing F} (ha : a ∈ steinbergDegreeSpan F p)
    (zs : List Fˣ) :
    a * tensorList F zs ∈ steinbergDegreeSpan F (p + zs.length) := by
  induction ha using Submodule.span_induction with
  | mem y hy =>
    exact steinbergInsert_mul_tensorList_mem_steinbergDegreeSpan F hy zs
  | zero =>
    have : (0 : TensorRing F) * tensorList F zs = 0 := by rw [zero_mul]
    rw [this]
    exact Submodule.zero_mem (steinbergDegreeSpan F (p + zs.length))
  | add y z _ _ hy hz =>
    have h_eq : (y + z) * tensorList F zs =
        y * tensorList F zs + z * tensorList F zs := by rw [add_mul]
    rw [h_eq]
    exact Submodule.add_mem (steinbergDegreeSpan F (p + zs.length)) hy hz
  | smul c y _ hy =>
    have h_eq : (c • y) * tensorList F zs = c • (y * tensorList F zs) := by
      rw [Algebra.smul_mul_assoc]
    rw [h_eq]
    exact Submodule.smul_mem (steinbergDegreeSpan F (p + zs.length)) _ hy

private theorem tensorListSet_mul_steinbergDegreeSpan_mem
    {p q : ℕ} {y : TensorRing F} (hy : y ∈ tensorListSet F p)
    {b : TensorRing F} (hb : b ∈ steinbergDegreeSpan F q) :
    y * b ∈ steinbergDegreeSpan F (p + q) := by
  rcases hy with ⟨zs, hlen, rfl⟩
  have h_mem := tensorList_mul_mem_steinbergDegreeSpan F zs hb
  have h_eq : zs.length + q = p + q := by rw [hlen]
  rw [h_eq] at h_mem
  exact h_mem

private theorem steinbergDegreeSpan_mul_tensorListSet_mem
    {p q : ℕ} {a : TensorRing F} (ha : a ∈ steinbergDegreeSpan F p)
    {y : TensorRing F} (hy : y ∈ tensorListSet F q) :
    a * y ∈ steinbergDegreeSpan F (p + q) := by
  rcases hy with ⟨zs, hlen, rfl⟩
  have h_mem := mem_steinbergDegreeSpan_mul_tensorList F ha zs
  have h_eq : p + zs.length = p + q := by rw [hlen]
  rw [h_eq] at h_mem
  exact h_mem

/-- `degree p * steinbergDegreeSpan q` is contained in `steinbergDegreeSpan (p+q)`. -/
theorem degree_mul_steinbergDegreeSpan_mem
    {p q : ℕ} {a : TensorRing F} (ha : a ∈ TensorRing.degree F p)
    {b : TensorRing F} (hb : b ∈ steinbergDegreeSpan F q) :
    a * b ∈ steinbergDegreeSpan F (p + q) := by
  have h_eq : TensorRing.degree F p = Submodule.span ℤ (tensorListSet F p) :=
    degree_eq_span_tensorList F p
  rw [h_eq] at ha
  induction ha using Submodule.span_induction with
  | mem y hy =>
    exact tensorListSet_mul_steinbergDegreeSpan_mem F hy hb
  | zero =>
    have : (0 : TensorRing F) * b = 0 := by rw [zero_mul]
    rw [this]
    exact Submodule.zero_mem (steinbergDegreeSpan F (p + q))
  | add y z _ _ hy hz =>
    have : (y + z) * b = y * b + z * b := by rw [add_mul]
    rw [this]
    exact Submodule.add_mem (steinbergDegreeSpan F (p + q)) hy hz
  | smul c y _ hy =>
    have : (c • y) * b = c • (y * b) := by rw [Algebra.smul_mul_assoc]
    rw [this]
    exact Submodule.smul_mem (steinbergDegreeSpan F (p + q)) _ hy

/-- `steinbergDegreeSpan p * degree q` is contained in `steinbergDegreeSpan (p+q)`. -/
theorem steinbergDegreeSpan_mul_degree_mem
    {p q : ℕ} {a : TensorRing F} (ha : a ∈ steinbergDegreeSpan F p)
    {b : TensorRing F} (hb : b ∈ TensorRing.degree F q) :
    a * b ∈ steinbergDegreeSpan F (p + q) := by
  have h_eq : TensorRing.degree F q = Submodule.span ℤ (tensorListSet F q) :=
    degree_eq_span_tensorList F q
  rw [h_eq] at hb
  induction hb using Submodule.span_induction with
  | mem y hy =>
    exact steinbergDegreeSpan_mul_tensorListSet_mem F ha hy
  | zero =>
    have : a * (0 : TensorRing F) = 0 := by rw [mul_zero]
    rw [this]
    exact Submodule.zero_mem (steinbergDegreeSpan F (p + q))
  | add y z _ _ hy hz =>
    have : a * (y + z) = a * y + a * z := by rw [mul_add]
    rw [this]
    exact Submodule.add_mem (steinbergDegreeSpan F (p + q)) hy hz
  | smul c y _ hy =>
    have : a * (c • y) = c • (a * y) := by rw [Algebra.mul_smul_comm]
    rw [this]
    exact Submodule.smul_mem (steinbergDegreeSpan F (p + q)) _ hy

end TensorRing

end MilnorK
