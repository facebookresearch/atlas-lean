/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.RingTheory.Length.FiniteFractionSubalgebra
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Ideal.Span

/-!
# Principal quotient lengths of algebraic fractions

Let k be a field, R a commutative Noetherian k-algebra that is a domain of Krull dimension at
most one, and K its fraction field with the compatible k-action. Suppose f ∈ K is nonzero and
integral over k, and write f = a/b for nonzero a,b ∈ R.

Then ℓ_R(R/(a)) = ℓ_R(R/(b)). Adjoining f and f⁻¹ to R inside K gives a finite birational
subalgebra in which a and b differ by a unit. Their principal ideals there are equal, and the
principal-quotient length comparison for a finite fraction subalgebra transfers the equality
back to R. The coefficient field, ring and fraction-field universes are independent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u v w

namespace Algebra

/-- Equality of numerator and denominator quotient lengths for an algebraic constant.

Let R be a Noetherian domain of Krull dimension at most one over a field k, with fraction
field K and compatible scalar tower. If f ∈ K is nonzero and integral over k and f = a/b for
nonzero a,b ∈ R, then ℓ_R(R/Ideal.span{a}) = ℓ_R(R/Ideal.span{b}). Both lengths use the
original R-module structures. -/
theorem length_quotient_span_num_eq_den_of_integral_constant
    {k : Type u} [Field k]
    {R : Type v} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [Algebra k R]
    {K : Type w} [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra k K] [IsScalarTower k R K]
    {f : K} (hf : IsIntegral k f) (hne : f ≠ 0)
    {a b : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : algebraMap R K a / algebraMap R K b = f) :
    Module.length R (R ⧸ Ideal.span {a}) = Module.length R (R ⧸ Ideal.span {b}) := by
  let B := Algebra.adjoin R ({f, f⁻¹} : Set K)
  let _ : Module.Finite R B :=
    Algebra.finite_adjoin_of_finite_of_isIntegral ((Set.finite_singleton f⁻¹).insert f)
      (by
        intro x hx
        rcases Set.mem_insert_iff.mp hx with h | h
        · subst x
          exact hf.tower_top
        · have hx : x = f⁻¹ := Set.mem_singleton_iff.mp h
          subst x
          exact hf.inv.tower_top)
  have hfB : f ∈ B := Algebra.subset_adjoin (Set.mem_insert f {f⁻¹})
  have hiB : f⁻¹ ∈ B :=
    Algebra.subset_adjoin (Set.mem_insert_of_mem f (Set.mem_singleton f⁻¹))
  let u : Bˣ :=
    ⟨⟨f, hfB⟩, ⟨f⁻¹, hiB⟩,
      by apply Subtype.ext; exact mul_inv_cancel₀ hne,
      by apply Subtype.ext; exact inv_mul_cancel₀ hne⟩
  have hbK : algebraMap R K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hb)
  have hmul : algebraMap R B a = (u : B) * algebraMap R B b := by
    apply Subtype.ext
    change algebraMap R K a = f * algebraMap R K b
    rw [← hab]
    exact (div_mul_cancel₀ (algebraMap R K a) hbK).symm
  have hspan : Ideal.span {algebraMap R B a} = Ideal.span {algebraMap R B b} := by
    rw [hmul]
    exact Ideal.span_singleton_mul_left_unit u.isUnit _
  calc
    Module.length R (R ⧸ Ideal.span {a}) =
        Module.length R (B ⧸ Ideal.span {algebraMap R B a}) :=
      Subalgebra.length_quotient_span_eq_of_finite B ha
    _ = Module.length R (B ⧸ Ideal.span {algebraMap R B b}) := by rw [hspan]
    _ = Module.length R (R ⧸ Ideal.span {b}) :=
      (Subalgebra.length_quotient_span_eq_of_finite B hb).symm

end Algebra
