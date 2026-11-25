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

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Length

/-!
# Length symmetry for double ideal quotients

Quotienting a commutative ring first by `I` and then by the image of `J`
has the same underlying base-ring module length as quotienting first by `J`
and then by the image of `I`.  This follows from the canonical
`DoubleQuot.quotQuotEquivCommₐ` algebra equivalence and requires no finiteness
hypothesis; the equality is in `ℕ∞` and also covers infinite length.

The singleton-span specialization identifies the two orders of quotienting
by elements.  These are local algebra inputs for iterated Cartier
intersections.  They do not identify iterated fundamental cycles, prove an
associativity formula for component multiplicities, construct a Gysin map,
or prove cubical face interchange.

## Main declarations

* `Ideal.length_quotient_quotient_comm`
* `Ideal.length_quotient_span_quotient_span_comm`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace Ideal

variable (R : Type u) [CommRing R]

/-- The two orders of quotienting by ideals have equal length as modules
over the original ring. -/
theorem length_quotient_quotient_comm (I J : Ideal R) :
    Module.length R
        ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) =
      Module.length R
        ((R ⧸ J) ⧸ I.map (Ideal.Quotient.mk J)) :=
  (DoubleQuot.quotQuotEquivCommₐ R I J).toLinearEquiv.length_eq

/-- Element form of double-quotient length symmetry: quotienting by `g`
then the image of `h` has the same length as quotienting in the opposite
order. -/
theorem length_quotient_span_quotient_span_comm (g h : R) :
    Module.length R
        ((R ⧸ Ideal.span {g}) ⧸
          Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) h}) =
      Module.length R
        ((R ⧸ Ideal.span {h}) ⧸
          Ideal.span {Ideal.Quotient.mk (Ideal.span {h}) g}) := by
  have hgh : (Ideal.span {h}).map
      (Ideal.Quotient.mk (Ideal.span {g})) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) h} := by
    rw [Ideal.map_span]
    simp
  have hhg : (Ideal.span {g}).map
      (Ideal.Quotient.mk (Ideal.span {h})) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {h}) g} := by
    rw [Ideal.map_span]
    simp
  rw [← hgh, ← hhg]
  exact length_quotient_quotient_comm R
    (Ideal.span {g}) (Ideal.span {h})

end Ideal
