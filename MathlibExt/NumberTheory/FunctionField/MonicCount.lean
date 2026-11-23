/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Field.GeomSum
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting monic polynomials over a finite field

A monic polynomial of degree `d` is determined by its `d` lower coefficients.
Summing the counts for the individual degrees gives a finite geometric sum.
-/

open Polynomial

namespace MetaMathlibExt

/-- Over a field with `q` elements, the number of monic polynomials of degree at most `N`
is `(q ^ (N + 1) - 1) / (q - 1)`.

The original statement cites Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor
Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80,
Proposition 4 (`integers-2026-A80-prop-4`), case `h = 1`, `m = 1`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Proposition 4
(`integers-2026-A80-prop-4`), case `h = 1`, `m = 1`. -/
public theorem monic_count_natDegree_le {F : Type*} [Field F] [Fintype F] (N : ℕ) :
    (Nat.card {f : F[X] // f.Monic ∧ f.natDegree ≤ N} : ℚ) =
      ((Fintype.card F : ℚ) ^ (N + 1) - 1) / (Fintype.card F - 1) := by
  let byDegree : {f : F[X] // f.Monic ∧ f.natDegree ≤ N} ≃
      Σ d : Fin (N + 1), {f : F[X] // f.Monic ∧ f.natDegree = d} :=
    { toFun := fun ⟨f, hm, hd⟩ => ⟨⟨f.natDegree, Nat.lt_succ_of_le hd⟩, f, hm, rfl⟩
      invFun := fun ⟨d, f, hm, hd⟩ => ⟨f, hm, hd ▸ Nat.le_of_lt_succ d.isLt⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨d, hd⟩, f, hm, hdeg⟩
        change f.natDegree = d at hdeg
        subst d
        rfl }
  let coeffs (d : Fin (N + 1)) :
      {f : F[X] // f.Monic ∧ f.natDegree = d} ≃ (Fin d → F) :=
    (monicEquivDegreeLT d).trans (degreeLTEquiv F d).toEquiv
  rw [Nat.card_congr (byDegree.trans (Equiv.sigmaCongrRight coeffs)), Nat.card_sigma]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Nat.cast_sum,
    Nat.cast_pow]
  rw [Fin.sum_univ_eq_sum_range (fun d => (Fintype.card F : ℚ) ^ d)]
  apply geom_sum_eq
  exact_mod_cast (Fintype.one_lt_card (α := F)).ne'

end MetaMathlibExt
