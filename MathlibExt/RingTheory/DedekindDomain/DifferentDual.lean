/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Different

@[expose] public section

/-!
# Different-dual order bridge

This module records the order-theoretic bridge between the different ideal and
the dual fractional ideal: an integral ideal lies below the different if and
only if its product with the dual of `1` lies below `1`.

## Source correspondence

The motivating source statement is Andrew V. Sutherland, *18.785 Number Theory I*,
Lecture 12,
[Theorem 12.27](https://math.mit.edu/classes/18.785/2021fa/LectureNotes12.pdf#page=10).
In the AKLB setting it bounds the valuation of the different
`D_{B/A}` at a prime `q` and characterizes equality in the tame case.  This module does
not claim those valuation bounds; it isolates the ideal-containment bridge needed for the
upper-bound route.

Here `FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L)` is the trace dual
`Bᵛ = {x ∈ L | Tr_{L/K}(xB) ⊆ A}`, and Mathlib's
`coeIdeal_differentIdeal` identifies the fractional ideal underlying
`differentIdeal A B` with `(Bᵛ)⁻¹`.  After coercing an integral ideal `I` to a
fractional ideal, the theorem is the order identity
`I ⊆ (Bᵛ)⁻¹ ⇔ I Bᵛ ⊆ B`; the right-hand `1` denotes the unit
fractional ideal `B`.

The typeclass assumptions reproduce AKLB: `A` is an integrally closed domain with
fraction field `K`; `L/K` is finite separable; and `B` is the Dedekind integral closure
of `A` in `L`, with fraction field `L`.  The scalar-tower and torsion-free instances
supply the compatible embeddings used by Mathlib's trace-dual and different APIs.
-/

open scoped nonZeroDivisors

namespace Ideal

variable (A K L B : Type*)
variable [CommRing A] [CommRing B] [Field K] [Field L]
variable [Algebra A B] [Algebra K L] [Algebra A K] [Algebra A L]
variable [Algebra B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [IsDomain A] [IsFractionRing A K] [IsFractionRing B L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [IsIntegralClosure B A L] [IsIntegrallyClosed A]
variable [IsDedekindDomain B] [Module.IsTorsionFree A B]

/-- **Ideals below the different.** Let $A$ be an integrally closed domain with fraction field
$K$, let $L/K$ be a finite separable extension, and let $B$ be the integral closure of $A$ in $L$;
assume that $B$ is a Dedekind domain with fraction field $L$ and is torsion-free as an
$A$-module. Write $B^\vee = \{x \in L : \operatorname{Tr}_{L/K}(xB) \subseteq A\}$ for the trace
dual of $B$ and $\mathfrak{D}_{B/A}$ for the different ideal of $B$ over $A$. Then an ideal $I$
of $B$ satisfies $I \subseteq \mathfrak{D}_{B/A}$ if and only if $I B^\vee \subseteq B$, where
the product is taken in the fractional ideals of $B$ in $L$. -/
theorem le_differentIdeal_iff_mul_dual_le_one (I : Ideal B) :
    I ≤ differentIdeal A B ↔
      (I : FractionalIdeal B⁰ L) * FractionalIdeal.dual A K
          (1 : FractionalIdeal B⁰ L) ≤ 1 := by
  have hdual : FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L) ≠ 0 :=
    FractionalIdeal.dual_ne_zero A K
      (@one_ne_zero (FractionalIdeal B⁰ L) _ _ _)
  rw [← FractionalIdeal.coeIdeal_le_coeIdeal L,
    coeIdeal_differentIdeal A K L B, inv_eq_one_div]
  exact FractionalIdeal.le_div_iff_mul_le hdual

end Ideal
