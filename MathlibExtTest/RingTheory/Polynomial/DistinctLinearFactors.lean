/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Polynomial.DistinctLinearFactors

@[expose] public section

open Polynomial

/-- Source-shaped consumer: the original binders, in the original order. -/
example {K : Type*} [Field K]
    (I : Ideal K[X]) (h : K[X]) (hh : h.Separable) (hhI : h ∈ I)
    (S : Finset K) (n : K → ℕ) (hn : ∀ a ∈ S, 0 < n a) (c : K) (hc : c ≠ 0)
    (hfI : C c * ∏ a ∈ S, (X - C a) ^ n a ∈ I)
    (hIf : I ≤ (Ideal.span {C c * ∏ a ∈ S, (X - C a) ^ n a}).radical) :
    I = Ideal.span {∏ a ∈ S, (X - C a)} :=
  Ideal.eq_span_prod_X_sub_C I h hh hhI S n hn c hc hfI hIf

/-- Boundary: a repeated linear factor does not generate the same ideal as
the distinct factor, so the separability / squarefree input is essential. -/
example : (Ideal.span {(X - C (0 : ℚ)) ^ 2} : Ideal ℚ[X])
    ≠ Ideal.span {X - C (0 : ℚ)} := by
  intro hEq
  have hmem : X - C (0 : ℚ) ∈ Ideal.span {(X - C (0 : ℚ)) ^ 2} := by
    rw [hEq]
    exact Ideal.subset_span rfl
  rw [Ideal.mem_span_singleton] at hmem
  have hdeg := Polynomial.degree_le_of_dvd hmem (by simp)
  simp [degree_pow] at hdeg
