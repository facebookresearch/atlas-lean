/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Ideal.ColonSpanDet
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

universe u

/-- Consumer with the original binders. -/
example {P : Type u} [CommRing P] {n : ℕ} (x f : Fin n → P) (g : Matrix (Fin n) (Fin n) P)
    (hf : ∀ i, f i = ∑ j, g i j * x j)
    (hy : ∃ y : Fin n → P, RingTheory.Sequence.IsWeaklyRegular P (List.ofFn y) ∧
      ∀ i, y i ∈ Ideal.span (Set.range f)) :
    (Ideal.span (Set.range f)).colon (Ideal.span (Set.range x)) =
        Ideal.span (Set.range f) ⊔ Ideal.span {g.det} ∧
      (Ideal.span (Set.range f)).colon (Ideal.span {g.det}) = Ideal.span (Set.range x) :=
  Ideal.colon_span_eq_sup_span_det_of_isWeaklyRegular x f g hf hy

/-- Higher-universe consumer. -/
example {P : Type (u + 1)} [CommRing P] {n : ℕ} (x f : Fin n → P)
    (g : Matrix (Fin n) (Fin n) P) (hf : ∀ i, f i = ∑ j, g i j * x j)
    (hy : ∃ y : Fin n → P, RingTheory.Sequence.IsWeaklyRegular P (List.ofFn y) ∧
      ∀ i, y i ∈ Ideal.span (Set.range f)) :
    (Ideal.span (Set.range f)).colon (Ideal.span {g.det}) = Ideal.span (Set.range x) :=
  (Ideal.colon_span_eq_sup_span_det_of_isWeaklyRegular x f g hf hy).2

/-- Boundary: the regularity hypothesis matters. Over `ℤ` with `x = f = 0` and `g = 0`,
`(0) : (0)` is the unit ideal, while `(0) + (det g)` is zero. -/
example : (Ideal.span (Set.range (0 : Fin 1 → ℤ))).colon (Ideal.span (Set.range (0 : Fin 1 → ℤ))) ≠
    Ideal.span (Set.range (0 : Fin 1 → ℤ)) ⊔ Ideal.span {(0 : Matrix (Fin 1) (Fin 1) ℤ).det} := by
  have h0 : Ideal.span (Set.range (0 : Fin 1 → ℤ)) = ⊥ := by simp
  rw [h0, Submodule.colon_eq_top_iff_le.mpr le_rfl]
  simp

/-- The relation `f = g • x` may also be given in `Matrix.mulVec` form. -/
example {P : Type u} [CommRing P] {n : ℕ} (x f : Fin n → P) (g : Matrix (Fin n) (Fin n) P)
    (hf : f = g.mulVec x)
    (hy : ∃ y : Fin n → P, RingTheory.Sequence.IsWeaklyRegular P (List.ofFn y) ∧
      ∀ i, y i ∈ Ideal.span (Set.range f)) :
    (Ideal.span (Set.range f)).colon (Ideal.span {g.det}) = Ideal.span (Set.range x) :=
  (Ideal.colon_span_eq_sup_span_det_of_isWeaklyRegular x f g (fun i => congrFun hf i) hy).2

private theorem span_range_vecCons_vecEmpty {R : Type*} [CommRing R] (a : R) :
    Ideal.span (Set.range ![a]) = Ideal.span {a} := by
  rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty]

/-- Concrete instance over `ℤ`: `x = 2`, `g = 3` and `f = 6`. -/
private theorem int_hf : ∀ i, ![(6 : ℤ)] i = ∑ j, !![(3 : ℤ)] i j * ![(2 : ℤ)] j := by
  intro i; fin_cases i; simp

/-- In the concrete instance, `(6)` contains the weakly regular sequence `[6]`. -/
private theorem int_hy : ∃ y : Fin 1 → ℤ, RingTheory.Sequence.IsWeaklyRegular ℤ (List.ofFn y) ∧
    ∀ i, y i ∈ Ideal.span (Set.range ![(6 : ℤ)]) :=
  ⟨![6], by
    simpa using (RingTheory.Sequence.isWeaklyRegular_singleton_iff ℤ (6 : ℤ)).mpr
      (IsRegular.of_ne_zero (by norm_num)).left.isSMulRegular,
    fun i => Ideal.subset_span ⟨i, rfl⟩⟩

/-- The concrete instance: `(6) : (2) = (6) + (3) = (3)` and `(6) : (3) = (2)`. -/
example : (Ideal.span {(6 : ℤ)}).colon (Ideal.span {(2 : ℤ)}) = Ideal.span {3} ∧
    (Ideal.span {(6 : ℤ)}).colon (Ideal.span {(3 : ℤ)}) = Ideal.span {2} := by
  have h := Ideal.colon_span_eq_sup_span_det_of_isWeaklyRegular ![(2 : ℤ)] ![6] !![3] int_hf int_hy
  rw [span_range_vecCons_vecEmpty, span_range_vecCons_vecEmpty, Matrix.det_fin_one_of] at h
  exact ⟨h.1.trans (sup_eq_right.mpr (Ideal.span_singleton_le_span_singleton.mpr ⟨2, by norm_num⟩)),
    h.2⟩
