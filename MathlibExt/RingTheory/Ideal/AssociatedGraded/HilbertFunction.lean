/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import MathlibExt.RingTheory.Ideal.AdicOrder
public import MathlibExt.RingTheory.Ideal.AssociatedGraded.Basic

/-!
# Finite associated-graded pieces and their Hilbert function

In a Noetherian ring, every degree of the associated graded of an ideal is
finite over the degree-zero quotient.  At a maximal ideal this gives the
graded-piece Hilbert function.  Krull separation also supplies a nonzero
initial form for every supplied nonzero element of a proper ideal in a
Noetherian local ring.

This file defines neither a total adic order nor eventual polynomiality,
multiplicity, or a ring structure on the total associated-graded carrier.

## Main declarations

* `Ideal.associatedGradedPiece_finite`
* `Ideal.associatedGradedHilbertFunction`
* `Ideal.exists_initialForm_ne_zero_of_ne_zero`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Ideal

universe u

variable {R : Type u} [CommRing R]

/-- In a Noetherian ring, every associated-graded piece is finite over the
degree-zero quotient. -/
theorem associatedGradedPiece_finite [IsNoetherianRing R]
    (I : Ideal R) (n : ℕ) :
    Module.Finite (R ⧸ I) (AssociatedGradedPiece I n) := by
  infer_instance

/-- The finrank-valued associated-graded function. At a maximal ideal this
is the dimension of `I ^ n / I ^ (n + 1)` over `R / I`. -/
def associatedGradedHilbertFunction
    (I : Ideal R) (n : ℕ) : ℕ :=
  Module.finrank (R ⧸ I) (AssociatedGradedPiece I n)

/-- Krull separation supplies a nonzero initial form for every supplied
nonzero element with respect to a proper ideal in a Noetherian local ring. -/
theorem exists_initialForm_ne_zero_of_ne_zero
    [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≠ ⊤) {x : R} (hx : x ≠ 0) :
    ∃ (n : ℕ) (hxn : x ∈ I ^ n),
      initialForm I n ⟨x, hxn⟩ ≠ 0 := by
  obtain ⟨n, hxn, hnext⟩ :=
    Ideal.exists_mem_pow_notMem_pow_succ_of_ne_zero I hI hx
  refine ⟨n, hxn, ?_⟩
  rw [ne_eq, initialForm_eq_zero_iff]
  exact hnext

end Ideal
