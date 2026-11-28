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

public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.Data.Fintype.Powerset

/-!
# Subset coordinates of diagonal quasi-Pfister forms

Let F be a field, n ∈ ℕ and a₀,…,aₙ₋₁ ∈ Fˣ. For s ⊆ Fin n put wₐ(s) = ∏ᵢ∈s (−aᵢ), and let
qₐ(x) = ∑ₛ wₐ(s)xₛ² on F^(Finset(Fin n)). This is the diagonal quasi-Pfister form associated
to the bilinear Pfister form ⊗ᵢ⟨1,−aᵢ⟩. It coincides with a quadratic Pfister form if 2 ≠ 0
in F; in characteristic two it is totally singular, rather than the quadratic Pfister form
whose last factor is [1,a] = x² + xy + ay². Its carrier has dimension 2^n, and every diagonal
coefficient is nonzero. If 2 ≠ 0, it has zero radical and is nondegenerate. At n = 0 it is
the one-dimensional square form.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter X.
* R. Elman, N. Karpenko, A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic
  Forms*, Sections 9.B and 10.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

universe u

namespace QuadraticForm

variable (F : Type u) [Field F]

/-- **The coefficient of a Pfister subset.**

Let F be a field, n ∈ ℕ and a₀,…,aₙ₋₁ ∈ Fˣ. For s ⊆ Fin n put wₐ(s) = ∏ᵢ∈s (−aᵢ), and let
qₐ(x) = ∑ₛ wₐ(s)xₛ² on F^(Finset(Fin n)). The diagonal coefficient at s is wₐ(s), with the
empty product equal to 1.
-/
def pfisterWeight {n : ℕ} (a : Fin n → Fˣ) (s : Finset (Fin n)) : F :=
  ∏ i ∈ s, -(a i : F)

/-- **The empty Pfister coefficient.**

Let F be a field, n ∈ ℕ and a₀,…,aₙ₋₁ ∈ Fˣ. For s ⊆ Fin n put wₐ(s) = ∏ᵢ∈s (−aᵢ), and let
qₐ(x) = ∑ₛ wₐ(s)xₛ² on F^(Finset(Fin n)). One has wₐ(∅) = 1.
-/
@[simp]
theorem pfisterWeight_empty {n : ℕ} (a : Fin n → Fˣ) :
    pfisterWeight F a ∅ = 1 := by
  simp [pfisterWeight]

/-- **Inserting an index into a Pfister coefficient.**

Let F be a field, n ∈ ℕ and a₀,…,aₙ₋₁ ∈ Fˣ. For s ⊆ Fin n put wₐ(s) = ∏ᵢ∈s (−aᵢ), and let
qₐ(x) = ∑ₛ wₐ(s)xₛ² on F^(Finset(Fin n)). If i ∉ s, then wₐ(s ∪ {i}) = (−aᵢ)wₐ(s).
-/
@[simp]
theorem pfisterWeight_insert {n : ℕ} (a : Fin n → Fˣ)
    (s : Finset (Fin n)) (i : Fin n) (hi : i ∉ s) :
    pfisterWeight F a (insert i s) = -(a i : F) * pfisterWeight F a s := by
  simp [pfisterWeight, hi]

/-- **Nonvanishing of Pfister coefficients.**

Let F be a field, n ∈ ℕ and a₀,…,aₙ₋₁ ∈ Fˣ. For s ⊆ Fin n put wₐ(s) = ∏ᵢ∈s (−aᵢ), and let
qₐ(x) = ∑ₛ wₐ(s)xₛ² on F^(Finset(Fin n)). For every subset s, the coefficient wₐ(s) is
nonzero.
-/
theorem pfisterWeight_ne_zero {n : ℕ} (a : Fin n → Fˣ)
    (s : Finset (Fin n)) :
    pfisterWeight F a s ≠ 0 := by
  rw [pfisterWeight, Finset.prod_ne_zero_iff]
  intro i hi
  exact neg_ne_zero.mpr (Units.ne_zero (a i))

/-- **The diagonal quasi-Pfister form.**

Let F be a field, n ∈ ℕ and a₀,…,aₙ₋₁ ∈ Fˣ. For s ⊆ Fin n put wₐ(s) = ∏ᵢ∈s (−aᵢ), and let
qₐ(x) = ∑ₛ wₐ(s)xₛ² on F^(Finset(Fin n)). The form qₐ is the quasi-Pfister form associated
to the bilinear form ⊗ᵢ⟨1,−aᵢ⟩ over F, including the zero-fold case. It is a quadratic
Pfister form when 2 ≠ 0 and a totally singular diagonal form in characteristic two.
-/
def pfister {n : ℕ} (a : Fin n → Fˣ) :
    QuadraticForm F (Finset (Fin n) → F) :=
  QuadraticMap.weightedSumSquares F (pfisterWeight F a)

/-- **Evaluation of the diagonal Pfister form.**

Let F be a field, n ∈ ℕ and a₀,…,aₙ₋₁ ∈ Fˣ. For s ⊆ Fin n put wₐ(s) = ∏ᵢ∈s (−aᵢ), and let
qₐ(x) = ∑ₛ wₐ(s)xₛ² on F^(Finset(Fin n)). For every x : Finset(Fin n) → F, evaluation is qₐ(x)
= ∑ₛ (∏ᵢ∈s (−aᵢ))xₛ².
-/
@[simp]
theorem pfister_apply {n : ℕ} (a : Fin n → Fˣ)
    (x : Finset (Fin n) → F) :
    pfister F a x =
      ∑ s : Finset (Fin n), pfisterWeight F a s * (x s * x s) := by
  simp [pfister, QuadraticMap.weightedSumSquares_apply]

/-- **The radical of a Pfister form.**

Let F be a field, n ∈ ℕ and a₀,…,aₙ₋₁ ∈ Fˣ. For s ⊆ Fin n put wₐ(s) = ∏ᵢ∈s (−aᵢ), and let
qₐ(x) = ∑ₛ wₐ(s)xₛ² on F^(Finset(Fin n)). Assume 2 ≠ 0 in F. Then the radical of qₐ is the
zero subspace.
-/
theorem pfister_radical [NeZero (2 : F)] {n : ℕ} (a : Fin n → Fˣ) :
    (pfister F a).radical = ⊥ := by
  rw [pfister, radical_weightedSumSquares]
  ext x
  simp [pfisterWeight_ne_zero, Pi.mem_spanSubset_iff, funext_iff]

/-- **Nondegeneracy of a Pfister form.**

Let F be a field, n ∈ ℕ and a₀,…,aₙ₋₁ ∈ Fˣ. For s ⊆ Fin n put wₐ(s) = ∏ᵢ∈s (−aᵢ), and let
qₐ(x) = ∑ₛ wₐ(s)xₛ² on F^(Finset(Fin n)). Assume 2 ≠ 0 in F. Then qₐ is nondegenerate.
-/
theorem pfister_nondegenerate [NeZero (2 : F)] {n : ℕ}
    (a : Fin n → Fˣ) :
    (pfister F a).Nondegenerate := by
  let _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne _)
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
  exact pfister_radical F a

/-- **Dimension of the Pfister coordinate space.**

Let F be a field and n ∈ ℕ. The vector space of functions Finset(Fin n) → F has dimension 2^n,
including dimension 1 when n = 0.
-/
theorem finrank_pfister_carrier (n : ℕ) :
    Module.finrank F (Finset (Fin n) → F) = 2 ^ n := by
  rw [Module.finrank_pi, Fintype.card_finset, Fintype.card_fin]

end QuadraticForm

end
