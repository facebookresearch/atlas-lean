/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Ideal.ColonSpanDet

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
