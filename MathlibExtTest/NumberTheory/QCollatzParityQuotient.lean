/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QCollatzParityQuotient

/-! # Tests for the finite q-Collatz parity bijection -/

open MetaMathlibExt PowerSeries

-- At the smallest positive precision, X and 0 give the same residue.
example :
    ∃ e : (PowerSeries (ZMod 2) ⧸ Ideal.span {(X : PowerSeries (ZMod 2)) ^ 1}) ≃ ZMod (2 ^ 1),
      e (Ideal.Quotient.mk _ X) = 0 := by
  obtain ⟨e, he⟩ := qCollatzParityVector_quotient_bijection 1 1 (by simp) (by simp) 1 le_rfl
  refine ⟨e, ?_⟩
  have hX : Ideal.Quotient.mk (Ideal.span {(X : PowerSeries (ZMod 2)) ^ 1}) X =
      Ideal.Quotient.mk _ 0 := by
    rw [Ideal.Quotient.eq]
    simp
  rw [hX, he, qCollatzParityVector_zero, map_zero]

-- At precision two, the X class is distinguished from zero and maps to its parity residue.
example :
    ∃ e : (PowerSeries (ZMod 2) ⧸ Ideal.span {(X : PowerSeries (ZMod 2)) ^ 2}) ≃ ZMod (2 ^ 2),
      e (Ideal.Quotient.mk _ X) = PadicInt.toZModPow 2 (qCollatzParityVector (1 + X) 1 X) ∧
        e (Ideal.Quotient.mk _ X) ≠ 0 := by
  obtain ⟨e, he⟩ :=
    qCollatzParityVector_quotient_bijection (1 + X) 1 (by simp) (by simp) 2 (by decide)
  refine ⟨e, he X, ?_⟩
  have h0 : e (Ideal.Quotient.mk _ 0) = 0 := by rw [he, qCollatzParityVector_zero, map_zero]
  rw [← h0]
  intro h
  have hd := (Ideal.Quotient.eq.mp (e.injective h))
  rw [Ideal.mem_span_singleton, sub_zero] at hd
  have hc := X_pow_dvd_iff.mp hd 1 (by decide)
  simp at hc

-- Surjectivity modulo eight supplies a series with parity residue seven.
example : ∃ a, PadicInt.toZModPow 3 (qCollatzParityVector (1 + X) 1 a) = 7 := by
  obtain ⟨e, he⟩ :=
    qCollatzParityVector_quotient_bijection (1 + X) 1 (by simp) (by simp) 3 (by decide)
  obtain ⟨x, hx⟩ := e.surjective 7
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨a, (he a).symm.trans hx⟩
