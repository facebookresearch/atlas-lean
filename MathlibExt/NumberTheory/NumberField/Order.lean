/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

/-! An order in a number field `K` is a `ℤ`-subalgebra of `K` contained in the
integral closure `integralClosure ℤ K = 𝓞 K` whose fraction field is `K`.
This formalizes arXiv:2608.02983v1, TypesofQuartic25.tex line 136:
> Let K be an algebraic number field and O_K its ring of integers, and O an order
> in O_K (a subring of O_K with quotient field K). -/
def NumberField.IsOrder (K : Type*) [Field K] [NumberField K] (O : Subalgebra ℤ K) : Prop :=
  O ≤ integralClosure ℤ K ∧ IsFractionRing O K

namespace NumberField.IsOrder

variable {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K}

/-- **Orders lie in the ring of integers.** Let $K$ be a number field and $O$ an order in $K$,
that is, a subring of $K$ contained in the ring of integers $\mathcal{O}_K$ (the integral
closure of $\mathbb{Z}$ in $K$) whose field of fractions is $K$. Then
$O \subseteq \mathcal{O}_K$. -/
theorem le_integralClosure (h : NumberField.IsOrder K O) :
    O ≤ integralClosure ℤ K :=
  h.1

/-- **The fraction field of an order.** Let $K$ be a number field and $O$ an order in $K$, that
is, a subring of $K$ contained in the ring of integers $\mathcal{O}_K$ (the integral closure of
$\mathbb{Z}$ in $K$) whose field of fractions is $K$. Then $K$, with the inclusion
$O \subseteq K$, is a field of fractions of $O$. -/
theorem isFractionRing (h : NumberField.IsOrder K O) :
    IsFractionRing O K :=
  h.2

/-- **Elements of a number field are quotients of elements of an order.** Let $K$ be a number
field and $O$ an order in $K$, that is, a subring of $K$ contained in the ring of integers
$\mathcal{O}_K$ (the integral closure of $\mathbb{Z}$ in $K$) whose field of fractions is $K$.
Then for every $x \in K$ there are $a, b \in O$ with $b \neq 0$ and $x = a / b$. -/
theorem exists_div_eq (hO : NumberField.IsOrder K O) (x : K) :
    ∃ (a b : O), b ≠ 0 ∧ (a : K) / (b : K) = x := by
  let _inst : IsFractionRing O K := hO.isFractionRing
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := O) x
  exact ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp hb, by simpa using hab⟩

end NumberField.IsOrder

/-- **The ring of integers is an order.** For every number field $K$, the ring of integers
$\mathcal{O}_K$, the integral closure of $\mathbb{Z}$ in $K$, is an order in $K$, that is, a
subring of $K$ contained in $\mathcal{O}_K$ whose field of fractions is $K$. -/
theorem NumberField.isOrder_integralClosure (K : Type*) [Field K] [NumberField K] :
    NumberField.IsOrder K (integralClosure ℤ K) := by
  constructor
  · exact le_rfl
  · exact integralClosure.isFractionRing_of_finite_extension ℚ _

end
